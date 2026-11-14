#!/usr/bin/env python3
"""Local dashboard server. The only writable input is progress/config.json."""
from __future__ import annotations

import argparse
import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
from pathlib import Path
import threading
from urllib.parse import urlsplit, unquote

from generate import ConfigConflict, _atomic_write, collect_snapshot, generate, render_html, validate_config


class Dashboard:
    def __init__(self, root: Path):
        self.root = root.resolve()
        self.progress = self.root / "progress"
        self.lock = threading.RLock()
        self.state = generate(self.root, discover=False)

    def refresh(self, base_revision=None):
        with self.lock:
            if base_revision is not None:
                raw = (self.progress / "config.json").read_bytes()
                if hashlib.sha256(raw).hexdigest() != base_revision:
                    raise ConfigConflict("The configuration has changed since this page was loaded. Your draft is retained; load the latest configuration before refreshing.")
            self.state = generate(self.root, discover=True)
            return self.state

    def get_state(self):
        with self.lock:
            raw = (self.progress / "config.json").read_bytes()
            if hashlib.sha256(raw).hexdigest() != self.state["revision"]:
                self.state = generate(self.root, discover=False)
            return self.state

    def save(self, config: dict, base_revision: str):
        errors = validate_config(config)
        if errors:
            raise ValueError("; ".join(errors))
        with self.lock:
            raw = (self.progress / "config.json").read_bytes()
            if hashlib.sha256(raw).hexdigest() != base_revision:
                raise ConfigConflict("Another page or editor has updated the configuration. Export your draft, then load the latest configuration to merge your changes.")
            new_raw = (json.dumps(config, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
            state = {"config": config, "snapshot": collect_snapshot(self.root),
                     "revision": hashlib.sha256(new_raw).hexdigest()}
            # Prepare all outputs before replacing the one authoritative editable file.
            html = render_html(self.progress, state)
            if (self.progress / "config.json").read_bytes() != raw:
                raise ConfigConflict("The configuration changed while saving was being prepared. Your saved configuration was left unchanged; load the latest version before saving your draft.")
            _atomic_write(self.progress / "config.json", new_raw)
            _atomic_write(self.progress / "snapshot.json", json.dumps(state["snapshot"], ensure_ascii=False, indent=2) + "\n")
            _atomic_write(self.progress / "index.html", html)
            self.state = state
            return state


def handler_for(dashboard: Dashboard):
    class Handler(BaseHTTPRequestHandler):
        def _send(self, code, data, mime="application/json; charset=utf-8"):
            if not isinstance(data, bytes):
                data = json.dumps(data, ensure_ascii=False).encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", mime)
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.send_header("Referrer-Policy", "no-referrer")
            self.end_headers()
            self.wfile.write(data)

        def _host_allowed(self):
            return self.headers.get("Host") in {
                f"127.0.0.1:{self.server.server_port}", f"localhost:{self.server.server_port}"}

        def _write_body(self):
            if not self._host_allowed() or self.headers.get("Origin") != "http://" + self.headers.get("Host", ""):
                self._send(403, {"error": "Only the current local page may save configuration changes"})
                return None
            if self.headers.get("Content-Type", "").split(";")[0].strip() != "application/json":
                self._send(415, {"error": "Requests must use application/json"})
                return None
            try:
                length = int(self.headers.get("Content-Length", "0"))
                if length <= 0 or length > 4 * 1024 * 1024:
                    self._send(413, {"error": "Request size must be between 1 byte and 4 MB"})
                    return None
                body = json.loads(self.rfile.read(length))
                if not isinstance(body, dict):
                    raise ValueError("JSON must be an object")
                return body
            except (ValueError, UnicodeDecodeError):
                self._send(400, {"error": "Invalid JSON request"})
                return None

        def do_GET(self):
            if not self._host_allowed():
                self._send(403, {"error": "Invalid local Host"})
                return
            path = urlsplit(self.path).path
            if path == "/api/state":
                try:
                    self._send(200, dashboard.get_state())
                except ConfigConflict as exc:
                    self._send(409, {"error": str(exc)})
                except (OSError, ValueError) as exc:
                    self._send(422, {"error": str(exc)})
                return
            # Generated offline HTML is the only served file. No repo/static traversal.
            if unquote(path) in ("/", "/index.html"):
                self._send(200, (dashboard.progress / "index.html").read_bytes(), "text/html; charset=utf-8")
            elif path == "/favicon.ico":
                self._send(204, b"", "image/x-icon")
            else:
                self._send(404, {"error": "Not found"})

        def do_PUT(self):
            body = self._write_body()
            if body is None:
                return
            if urlsplit(self.path).path != "/api/config":
                self._send(404, {"error": "Not found"})
                return
            if set(body) != {"config", "baseRevision"} or not isinstance(body.get("baseRevision"), str):
                self._send(400, {"error": "config and baseRevision are required"})
                return
            try:
                self._send(200, dashboard.save(body["config"], body["baseRevision"]))
            except ConfigConflict as exc:
                self._send(409, {"error": str(exc)})
            except (OSError, ValueError) as exc:
                self._send(422, {"error": str(exc)})

        def do_POST(self):
            body = self._write_body()
            if body is None:
                return
            if urlsplit(self.path).path != "/api/refresh":
                self._send(404, {"error": "Not found"})
                return
            if body and (set(body) != {"baseRevision"} or not isinstance(body["baseRevision"], str)):
                self._send(400, {"error": "Refresh accepts an empty object or a baseRevision string"})
                return
            try:
                self._send(200, dashboard.refresh(body.get("baseRevision")))
            except ConfigConflict as exc:
                self._send(409, {"error": str(exc)})
            except (OSError, ValueError) as exc:
                self._send(422, {"error": str(exc)})

    return Handler


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    dashboard = Dashboard(args.repo)
    server = ThreadingHTTPServer(("127.0.0.1", args.port), handler_for(dashboard))
    print(f"Local: http://127.0.0.1:{server.server_port} (Ctrl+C to stop)", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
