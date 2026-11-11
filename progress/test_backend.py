"""Run with python3 -B -m unittest discover -s progress -p 'test_backend.py'."""
from copy import deepcopy
import hashlib
import http.client
from http.server import ThreadingHTTPServer
import json
from pathlib import Path
import tempfile
import threading
import unittest

from generate import collect_snapshot, generate, parse_imports, validate_config
from server import ConfigConflict, Dashboard, handler_for


def sample_config():
    return {
        "schemaVersion": 1,
        "categories": [{"id": "phd", "label": "PhD", "description": ""}],
        "projects": [{"id": "foundation", "categoryId": "phd", "parentId": None,
                      "label": "Foundation", "description": ""}],
        "approaches": [{"id": "current", "projectId": "foundation", "label": "Current approach",
                        "description": "", "environmentId": "xyin", "role": "active",
                        "entryModules": ["XYin.PhD.Basic"]}],
        "environments": [{"id": "xyin", "label": "XYin", "toolchain": "test", "note": ""}],
        "assignments": [{"id": "main", "pattern": "XYin/PhD/**", "projectId": "foundation",
                         "approachId": "current"}],
        "overrides": {}, "relations": [],
        "migrations": [{"id": "basic", "title": "Foundation migration", "sourcePaths": ["XYin/PhD/Basic.lean"],
                        "targetPaths": ["XYin/ForMathlib/Basic.lean"], "stage": "candidate",
                        "notes": "", "consumerProjectIds": ["foundation"], "adoptedProjectIds": []}],
    }


def fixture(root):
    (root / "XYin/PhD").mkdir(parents=True)
    (root / "XYin/PhD/Basic.lean").write_text("public import Mathlib.Algebra.Group.Basic\n\ntheorem example_one : True := by trivial\n")
    (root / "XYin.lean").write_text("import XYin.PhD.Basic\n")
    (root / "lean-toolchain").write_text("leanprover/lean4:test\n")
    web = root / "progress/web"
    web.mkdir(parents=True)
    (web / "template.html").write_text("<!doctype html><html><head><!--STYLE--></head><body><!--DATA--><!--MODEL--><!--APP--></body></html>")
    for name in ("style.css", "model.js", "app.js"):
        (web / name).write_text("")
    (root / "progress/config.json").write_text(json.dumps(sample_config(), ensure_ascii=False))


class ConfigValidationTests(unittest.TestCase):
    def test_valid(self):
        self.assertEqual(validate_config(sample_config()), [])

    def test_dangling_reference_and_wrong_approach(self):
        config = sample_config()
        config["projects"].append({"id": "other", "categoryId": "phd", "parentId": None,
                                   "label": "Other", "description": ""})
        config["overrides"]["XYin/PhD/Basic.lean"] = {"projectId": "other", "approachId": "current"}
        self.assertTrue(any("approach does not belong" in e for e in validate_config(config)))
        config["approaches"][0]["environmentId"] = "missing"
        self.assertTrue(any("environments" in e for e in validate_config(config)))

    def test_cycles_duplicates_and_adoption_subset(self):
        config = sample_config()
        config["projects"][0]["parentId"] = "foundation"
        config["categories"].append(deepcopy(config["categories"][0]))
        config["migrations"][0]["adoptedProjectIds"] = ["unlisted"]
        errors = validate_config(config)
        self.assertTrue(any("cycle" in e for e in errors))
        self.assertTrue(any("duplicated" in e for e in errors))
        self.assertTrue(any("planned consumers" in e for e in errors))

    def test_invalid_paths_and_unknown_fields(self):
        for value in ("/tmp/file.lean", "XYin/../escape.lean", "XYin/PhD\\x.lean", "XYin//A.lean"):
            config = sample_config()
            config["migrations"][0]["sourcePaths"] = [value]
            self.assertTrue(validate_config(config), value)
        config = sample_config()
        config["migrations"][0]["targetPaths"] = ["XYin/PhD/Target.lean"]
        self.assertTrue(validate_config(config))
        config["execute"] = "lake build"
        self.assertTrue(validate_config(config))

    def test_malformed_types_report_errors_not_exceptions(self):
        for key in ("categories", "projects", "approaches", "environments", "assignments", "overrides", "relations", "migrations"):
            config = sample_config()
            config[key] = None
            self.assertTrue(validate_config(config))
        config = sample_config()
        config["approaches"][0]["role"] = []
        config["migrations"][0]["stage"] = {}
        self.assertTrue(validate_config(config))


class SnapshotTests(unittest.TestCase):
    def test_imports_ignore_nested_comments_and_strings(self):
        source = '''/- import Nope\n /- public import Nope2 -/\n-/
public import Mathlib.A XYin.B -- import Nope3
import XYin.C
def s := "\nimport Nope4\n"
-- import Nope5
'''
        self.assertEqual(parse_imports(source), ["Mathlib.A", "XYin.B", "XYin.C"])

    def test_generate_read_only_sources_and_script_escaping(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture(root)
            (root / ".lake").mkdir()
            (root / ".lake/Hidden.lean").write_text("import Nope\n")
            source = root / "XYin/PhD/Basic.lean"
            before = source.read_bytes()
            config = sample_config()
            config["categories"][0]["label"] = "</script><img src=x onerror=alert(1)>\u2028"
            (root / "progress/config.json").write_text(json.dumps(config))
            state = generate(root)
            self.assertEqual(source.read_bytes(), before)
            self.assertEqual(len(state["snapshot"]["files"]), 2)
            basic = next(f for f in state["snapshot"]["files"] if f["path"] == "XYin/PhD/Basic.lean")
            self.assertEqual(basic["imports"], ["Mathlib.Algebra.Group.Basic"])
            html = (root / "progress/index.html").read_text()
            self.assertNotIn("</script><img", html)
            self.assertIn("\\u003c/script>", html)
            self.assertIn("\\u2028", html)

    def test_historical_receipt_source_drift(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture(root)
            draft = root / "XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts"
            draft.mkdir(parents=True)
            (draft / "A.lean").write_text("import Mathlib\n")
            receipt = {"source_sha256": {"A.lean": "old", "Missing.lean": "old"},
                       "build_exit_code": 0, "verified_at_utc": "2026-10-04"}
            (draft.parent / "AINTLIBBridgeReceipt.json").write_text(json.dumps(receipt))
            snapshot = collect_snapshot(root)
            evidence = next(e for e in snapshot["evidence"] if e["id"] == "aintlib-checkpoint")
            self.assertEqual(evidence["kind"], "historical")
            self.assertEqual(evidence["status"], "source-drift")
            self.assertEqual(evidence["sourceMatch"]["total"], 2)
            self.assertEqual(len(evidence["sourceMatch"]["changed"]), 1)
            self.assertEqual(len(evidence["sourceMatch"]["missing"]), 1)

    def test_old_overview_does_not_claim_new_migration(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture(root)
            (root / "PROJECT_OVERVIEW.md").write_text("Generated: 2026-11-04.\n")
            target = root / "XYin/ForMathlib/NumberTheory/NewMigration.lean"
            target.parent.mkdir(parents=True)
            target.write_text("import Mathlib\n")
            snapshot = collect_snapshot(root)
            overview = next(e for e in snapshot["evidence"] if e["id"] == "formathlib-overview")
            self.assertEqual(len(overview["scope"]), 18)
            self.assertNotIn(target.relative_to(root).as_posix(), overview["scope"])


class SaveTests(unittest.TestCase):
    def test_atomic_save_conflict_and_invalid_config_leave_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture(root)
            dashboard = Dashboard(root)
            before = (root / "XYin/PhD/Basic.lean").read_bytes()
            initial_revision = dashboard.state["revision"]
            config = sample_config()
            config["categories"][0]["label"] = "Research"
            saved = dashboard.save(config, initial_revision)
            self.assertNotEqual(initial_revision, saved["revision"])
            with self.assertRaises(ConfigConflict):
                dashboard.save(sample_config(), initial_revision)
            invalid = deepcopy(config)
            invalid["projects"][0]["categoryId"] = "missing"
            with self.assertRaises(ValueError):
                dashboard.save(invalid, saved["revision"])
            self.assertEqual(json.loads((root / "progress/config.json").read_text()), config)
            self.assertEqual((root / "XYin/PhD/Basic.lean").read_bytes(), before)
            config["categories"][0]["label"] = "External edit"
            (root / "progress/config.json").write_text(json.dumps(config))
            self.assertEqual(dashboard.get_state()["config"]["categories"][0]["label"], "External edit")

    def test_http_origin_protection_and_no_arbitrary_file_access(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture(root)
            dashboard = Dashboard(root)
            server = ThreadingHTTPServer(("127.0.0.1", 0), handler_for(dashboard))
            thread = threading.Thread(target=server.serve_forever, daemon=True)
            thread.start()
            host = f"127.0.0.1:{server.server_port}"

            def request(method, path, body=None, origin=None):
                connection = http.client.HTTPConnection("127.0.0.1", server.server_port)
                headers = {"Content-Type": "application/json"}
                if origin:
                    headers["Origin"] = origin
                connection.request(method, path, json.dumps(body) if body is not None else None, headers)
                response = connection.getresponse()
                status, payload = response.status, response.read()
                connection.close()
                return status, payload

            try:
                self.assertEqual(request("GET", "/")[0], 200)
                self.assertEqual(request("GET", "/../lean-toolchain")[0], 404)
                self.assertEqual(request("GET", "/config.json")[0], 404)
                payload = {"config": sample_config(), "baseRevision": dashboard.state["revision"]}
                self.assertEqual(request("PUT", "/api/config", payload)[0], 403)
                self.assertEqual(request("PUT", "/api/config", payload, "https://example.com")[0], 403)
                self.assertEqual(request("PUT", "/api/config", payload, "http://" + host)[0], 200)
                self.assertEqual(request("PUT", "/api/config", payload, "http://" + host)[0], 409)
                self.assertEqual(request("POST", "/api/refresh", {}, "http://" + host)[0], 200)
            finally:
                server.shutdown()
                server.server_close()
                thread.join()


if __name__ == "__main__":
    unittest.main()
