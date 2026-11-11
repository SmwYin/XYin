#!/usr/bin/env python3
"""Generate an offline dashboard. Reads Lean sources; never invokes or edits Lean."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import tempfile


SCHEMA_KEYS = {"schemaVersion", "categories", "projects", "approaches", "environments",
               "assignments", "overrides", "relations", "migrations"}
ID_RE = re.compile(r"^[a-zA-Z0-9][a-zA-Z0-9_-]*$")
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")
ROLES = {"active", "alternative", "reference", "shared"}
RELATIONS = {"alternative", "complementary", "mirror", "generalizes", "specializes",
             "equivalent_scope", "partial_integration", "unknown"}
STAGES = {"candidate", "preparing", "ready", "switching", "complete"}


def safe_path(value: object, pattern: bool = False) -> bool:
    if not isinstance(value, str) or not value or len(value) > 1000:
        return False
    if "\\" in value or any(ord(c) < 32 for c in value):
        return False
    parts = value.split("/")
    if any(p in ("", ".", "..") for p in parts) or PurePosixPath(value).is_absolute():
        return False
    if not pattern and any(c in value for c in "*?[]"):
        return False
    return value in ("XYin.lean", "XYinTest.lean") or value.startswith(("XYin/", "XYinTest/"))


def validate_config(config: object) -> list[str]:
    """Return validation errors. No inference, filesystem access, or mutation."""
    errors: list[str] = []
    if not isinstance(config, dict):
        return ["Configuration must be a JSON object"]
    if set(config) != SCHEMA_KEYS:
        errors.append("Configuration has missing or unknown fields")
    if type(config.get("schemaVersion")) is not int or config["schemaVersion"] != 1:
        errors.append("schemaVersion must be 1")
    sets: dict[str, dict] = {}
    fields = {
        "categories": {"id", "label", "description"},
        "projects": {"id", "categoryId", "parentId", "label", "description"},
        "approaches": {"id", "projectId", "label", "description", "environmentId", "role", "entryModules"},
        "environments": {"id", "label", "toolchain", "note"},
        "assignments": {"id", "pattern", "projectId", "approachId"},
        "relations": {"id", "fromApproachId", "toApproachId", "kind", "note"},
        "migrations": {"id", "title", "sourcePaths", "targetPaths", "stage", "notes",
                       "consumerProjectIds", "adoptedProjectIds"},
    }
    for name, required in fields.items():
        values = config.get(name)
        sets[name] = {}
        if not isinstance(values, list) or len(values) > 10000:
            errors.append(f"{name} must be an array containing at most 10000 items")
            continue
        for i, row in enumerate(values):
            prefix = f"{name}[{i}]"
            if not isinstance(row, dict):
                errors.append(f"{prefix} must be an object")
                continue
            if set(row) != required:
                errors.append(f"{prefix} has missing or unknown fields")
            ident = row.get("id")
            if not isinstance(ident, str) or not ID_RE.fullmatch(ident) or len(ident) > 100:
                errors.append(f"{prefix}.id is invalid")
            elif ident in sets[name]:
                errors.append(f"{prefix}.id is duplicated")
            else:
                sets[name][ident] = row
            for key in required & {"label", "description", "toolchain", "note", "title", "notes"}:
                value = row.get(key)
                if not isinstance(value, str) or len(value) > 10000 or (key in {"label", "title"} and not value.strip()):
                    errors.append(f"{prefix}.{key} must contain valid text")

    def ref(value, name, label, nullable=False):
        if nullable and value is None:
            return True
        valid = isinstance(value, str) and value in sets[name]
        if not valid:
            errors.append(f"{label} refers to an unknown entry in {name}")
        return valid

    def assignment(row, label):
        ref(row.get("projectId"), "projects", label)
        a = row.get("approachId")
        if ref(a, "approaches", label, nullable=True) and a is not None:
            if sets["approaches"][a].get("projectId") != row.get("projectId"):
                errors.append(f"{label}: the approach does not belong to the selected project")

    for ident, p in sets["projects"].items():
        ref(p.get("categoryId"), "categories", ident)
        parent = p.get("parentId")
        if ref(parent, "projects", ident, nullable=True) and parent is not None:
            if sets["projects"][parent].get("categoryId") != p.get("categoryId"):
                errors.append(f"{ident} and its parent project must belong to the same category")
        seen = {ident}
        while isinstance(parent, str) and parent in sets["projects"]:
            if parent in seen:
                errors.append(f"{ident} has a cycle in its project hierarchy")
                break
            seen.add(parent)
            parent = sets["projects"][parent].get("parentId")
    for ident, a in sets["approaches"].items():
        ref(a.get("projectId"), "projects", ident)
        ref(a.get("environmentId"), "environments", ident)
        if not isinstance(a.get("role"), str) or a["role"] not in ROLES:
            errors.append(f"{ident}.role is invalid")
        modules = a.get("entryModules")
        if not isinstance(modules, list) or len(modules) > 1000 or any(not isinstance(m, str) or not MODULE_RE.fullmatch(m) for m in modules):
            errors.append(f"{ident}.entryModules must be an array of module names")
    for ident, a in sets["assignments"].items():
        assignment(a, ident)
        if not safe_path(a.get("pattern"), pattern=True):
            errors.append(f"{ident}.pattern must be a safe relative source path")
    overrides = config.get("overrides")
    if not isinstance(overrides, dict) or len(overrides) > 10000:
        errors.append("overrides must be an object")
    else:
        for path, row in overrides.items():
            if not safe_path(path) or not path.endswith(".lean"):
                errors.append("overrides contains an invalid Lean path")
            if not isinstance(row, dict) or set(row) != {"projectId", "approachId"}:
                errors.append(f"{path} has invalid assignment fields")
            else:
                assignment(row, path)
    for ident, r in sets["relations"].items():
        ref(r.get("fromApproachId"), "approaches", ident)
        ref(r.get("toApproachId"), "approaches", ident)
        if r.get("fromApproachId") == r.get("toApproachId"):
            errors.append(f"{ident} cannot link an approach to itself")
        if not isinstance(r.get("kind"), str) or r["kind"] not in RELATIONS:
            errors.append(f"{ident}.kind is invalid")
    for ident, m in sets["migrations"].items():
        if not isinstance(m.get("stage"), str) or m["stage"] not in STAGES:
            errors.append(f"{ident}.stage is invalid")
        for key in ("sourcePaths", "targetPaths"):
            values = m.get(key)
            if not isinstance(values, list) or len(values) > 2000 or any(not safe_path(p) for p in values):
                errors.append(f"{ident}.{key} must be an array of safe source paths")
            elif key == "targetPaths" and any(not p.startswith("XYin/ForMathlib/") for p in values):
                errors.append(f"{ident} must target paths within XYin/ForMathlib/")
        for key in ("consumerProjectIds", "adoptedProjectIds"):
            values = m.get(key)
            if not isinstance(values, list) or len(values) > 10000 or any(not isinstance(x, str) for x in values):
                errors.append(f"{ident}.{key} must be an array of project IDs")
            else:
                if len(values) != len(set(values)):
                    errors.append(f"{ident}.{key} contains duplicate projects")
                for value in values:
                    ref(value, "projects", ident)
        consumers, adopted = m.get("consumerProjectIds"), m.get("adoptedProjectIds")
        if isinstance(consumers, list) and isinstance(adopted, list):
            if any(a not in consumers for a in adopted):
                errors.append(f"{ident}: adopted projects must be included among the planned consumers")
    return errors[:100]


def _without_comments_and_strings(text: str) -> str:
    """Preserve newlines while blanking nested Lean comments and quoted strings."""
    result, i, depth, string = [], 0, 0, False
    while i < len(text):
        c, pair = text[i], text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                i += 2
                continue
            if pair == "-/":
                depth -= 1
                result.extend("  ")
                i += 2
                continue
            result.append("\n" if c == "\n" else " ")
        elif string:
            if c == "\\" and i + 1 < len(text):
                result.extend("\n" if x == "\n" else " " for x in text[i:i + 2])
                i += 2
                continue
            if c == '"':
                string = False
            result.append("\n" if c == "\n" else " ")
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            i += 2
            continue
        elif pair == "--":
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            result.append(" " * (end - i))
            i = end
            continue
        elif c == '"':
            string = True
            result.append(" ")
        else:
            result.append(c)
        i += 1
    return "".join(result)


def parse_imports(text: str) -> list[str]:
    imports = []
    for match in re.finditer(r"^\s*(?:public\s+)?import\s+([^\n]+)", _without_comments_and_strings(text), re.MULTILINE):
        for module in match[1].split():
            if MODULE_RE.fullmatch(module) and module not in imports:
                imports.append(module)
    return imports


def _git(root: Path, *args: str) -> str:
    try:
        result = subprocess.run(["git", *args], cwd=root, capture_output=True, text=True,
                                timeout=10, env={**os.environ, "GIT_OPTIONAL_LOCKS": "0"})
        return result.stdout.strip() if result.returncode == 0 else ""
    except (OSError, subprocess.TimeoutExpired):
        return ""


def _load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def _historical_records(root: Path, files: dict) -> tuple[list, list, list]:
    evidence, boards, warnings = [], [], []
    overview = root / "PROJECT_OVERVIEW.md"
    if overview.is_file():
        content = overview.read_text(encoding="utf-8")
        date_match = re.search(r"Generated:\s*([\d-]+)", content)
        # Freeze the inventory named by this historical report. New migrations into
        # these directories must never inherit an older report's claimed coverage.
        nt = "XYin/ForMathlib/NumberTheory/"
        scope = []
        if date_match and date_match[1] == "2026-11-04":
            scope = ([nt + "ModularForms/QExpansion/" + name + ".lean" for name in
                      ("Basic", "CuspRepresentatives", "ChangeRepresentative", "Algebra", "ModularForm", "Order", "Degenerate")]
                     + [nt + "ModularFunctions/LaurentQExpansion/" + name + ".lean" for name in
                        ("Basic", "Algebra", "Convergence")]
                     + [nt + "ModularFunctions/JFunction/" + name + ".lean" for name in
                        ("Basic", "QExpansion", "Properties", "Lattice", "EllipticCurve")]
                     + [nt + "ModularForms/Discriminant/QExpansion.lean",
                        nt + "ModularForms/EisensteinSeries/QExpansion.lean",
                        "XYin/ForMathlib/RingTheory/PowerSeries/HasCoeffsIn.lean"])
        evidence.append({"id": "formathlib-overview", "label": "ForMathlib NT / RT historical review",
                         "kind": "historical", "date": date_match[1] if date_match else "",
                         "environmentId": "xyin", "status": "historical-report",
                         "scope": scope, "sourcePath": "PROJECT_OVERVIEW.md",
                         "summary": "The historical overview covers NumberTheory / RingTheory, not the entire repository. This scan indexes the report without running a build."})
    board_rel = ".mathlib-quality/cox11-1/board"
    board = root / board_rel
    if (board / "tickets.json").is_file():
        try:
            tickets = _load_json(board / "tickets.json")
            statuses, dates = {}, []
            for path in sorted((board / "files").glob("*.md")) + [board / "tickets.md"]:
                current = None
                for line in path.read_text(encoding="utf-8").splitlines():
                    match = re.match(r"### \[(C11-[A-Z0-9-]+)\]", line)
                    if match:
                        current = match[1]
                    elif current and (match := re.match(r"- \*\*Status\*\*: *(\w+)(.*)", line)):
                        statuses[current] = match[1]
                        if date := re.search(r"\d{4}-\d{2}-\d{2}", match[2]):
                            dates.append(date[0])
                        current = None
            counts = dict(Counter(statuses.get(t["id"], "unknown") for t in tickets))
            boards.append({"id": "cox11", "label": "Cox 11.1 task records", "counts": counts,
                           "sourcePath": board_rel + "/tickets.json"})
            evidence.append({"id": "cox11-board", "label": "Cox 11.1 historical ticket records",
                             "kind": "historical", "date": max(dates, default=""),
                             "environmentId": "xyin", "status": "historical-record",
                             "scope": sorted({t["file"] for t in tickets if t.get("file") in files}),
                             "sourcePath": board_rel + "/files/Main.md",
                             "summary": "Counts are recalculated from each ticket's Status field, including proof and cleanup tasks. They do not represent a fresh verification of the current source."})
            warnings.append("The Cox board header contains an old summary. This dashboard recalculates individual ticket statuses; task completion is separate from current build evidence.")
        except (OSError, ValueError, KeyError, TypeError) as exc:
            warnings.append(f"Could not read Cox task records: {exc}")
    else:
        warnings.append("Local .mathlib-quality/Cox task records are unavailable. That directory is not tracked by Git; other dashboard data remains available.")
    receipt_rel = "XYin/PhD/Test/ModularPolynomialCurve/AINTLIBBridgeReceipt.json"
    receipt_file = root / receipt_rel
    if receipt_file.is_file():
        try:
            receipt = _load_json(receipt_file)
            scope, matched, changed, missing = [], 0, [], []
            prefix = "XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/"
            hashes = receipt.get("source_sha256", {})
            for name, expected in hashes.items():
                path = prefix + name
                scope.append(path)
                actual = files.get(path)
                if not actual:
                    missing.append(path)
                elif actual["sha256"] == expected:
                    matched += 1
                else:
                    changed.append(path)
            evidence.append({"id": "aintlib-checkpoint", "label": "AINTLIB cumulative checkpoint",
                             "kind": "historical", "date": receipt.get("verified_at_utc", ""),
                             "environmentId": "aintlib", "status": "source-drift" if changed or missing else "historical-source-match",
                             "scope": scope, "sourcePath": receipt_rel,
                             "summary": f"Historical build exit code: {receipt.get('build_exit_code', 'unknown')}. Source matches: {matched}/{len(hashes)}; {len(changed)} changed, {len(missing)} missing. The dependency environment has not been rechecked; matching source does not establish a passing current build.",
                             "toolchain": receipt.get("toolchain", ""),
                             "sourceMatch": {"matched": matched, "total": len(hashes), "changed": changed, "missing": missing}})
            if changed or missing:
                warnings.append("Source covered by the historical AINTLIB checkpoint has changed or is missing. See the verification records for details.")
        except (OSError, ValueError, TypeError) as exc:
            warnings.append(f"Could not read AINTLIB historical records: {exc}")
    return evidence, boards, warnings


def collect_snapshot(repo_root: Path | str) -> dict:
    root = Path(repo_root).resolve()
    candidates = [root / "XYin.lean", root / "XYinTest.lean"]
    for directory in (root / "XYin", root / "XYinTest"):
        if directory.is_dir() and not directory.is_symlink():
            candidates.extend(directory.rglob("*.lean"))
    files = []
    for path in sorted(set(candidates)):
        if not path.is_file() or path.is_symlink() or not path.resolve().is_relative_to(root):
            continue
        rel = path.relative_to(root).as_posix()
        raw = path.read_bytes()
        text = raw.decode("utf-8", errors="replace")
        files.append({"path": rel, "module": rel[:-5].replace("/", "."),
                      "imports": parse_imports(text), "lines": len(text.splitlines()),
                      "sha256": hashlib.sha256(raw).hexdigest()})
    evidence, boards, warnings = _historical_records(root, {f["path"]: f for f in files})
    toolchain_file = root / "lean-toolchain"
    return {"schemaVersion": 1, "generatedAt": datetime.now(timezone.utc).isoformat(),
            "repoRoot": str(root), "git": {"branch": _git(root, "branch", "--show-current"),
            "head": _git(root, "rev-parse", "HEAD"),
            "dirty": bool(_git(root, "status", "--porcelain", "--untracked-files=normal"))},
            "toolchain": toolchain_file.read_text(encoding="utf-8").strip() if toolchain_file.exists() else "",
            "files": files, "evidence": evidence, "boards": boards, "warnings": warnings}


def _atomic_write(path: Path, content: str | bytes) -> None:
    data = content.encode("utf-8") if isinstance(content, str) else content
    with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".dashboard-", delete=False) as temp:
        temporary = Path(temp.name)
        try:
            temp.write(data)
            temp.flush()
            os.fsync(temp.fileno())
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def _json_for_script(value: object) -> str:
    return json.dumps(value, ensure_ascii=False).replace("<", "\\u003c").replace("\u2028", "\\u2028").replace("\u2029", "\\u2029")


def render_html(progress: Path, state: dict) -> str:
    web = progress / "web"
    template = (web / "template.html").read_text(encoding="utf-8")
    replacements = {
        "<!--STYLE-->": "<style>\n" + (web / "style.css").read_text(encoding="utf-8") + "\n</style>",
        "<!--MODEL-->": "<script>\n" + (web / "model.js").read_text(encoding="utf-8") + "\n</script>",
        "<!--APP-->": "<script>\n" + (web / "app.js").read_text(encoding="utf-8") + "\n</script>",
        "<!--DATA-->": "<script>window.XYIN_DATA = " + _json_for_script(state) + ";</script>",
    }
    for placeholder, replacement in replacements.items():
        if placeholder not in template:
            raise ValueError(f"HTML template is missing {placeholder}")
        template = template.replace(placeholder, replacement)
    return template


def generate(repo_root: Path | str) -> dict:
    root = Path(repo_root).resolve()
    progress = root / "progress"
    raw = (progress / "config.json").read_bytes()
    config = json.loads(raw)
    errors = validate_config(config)
    if errors:
        raise ValueError("Invalid configuration: " + "; ".join(errors))
    state = {"config": config, "snapshot": collect_snapshot(root),
             "revision": hashlib.sha256(raw).hexdigest()}
    html = render_html(progress, state)
    _atomic_write(progress / "snapshot.json", json.dumps(state["snapshot"], ensure_ascii=False, indent=2) + "\n")
    _atomic_write(progress / "index.html", html)
    return state


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    state = generate(args.repo)
    print(f"Generated {args.repo.resolve() / 'progress/index.html'} ({len(state['snapshot']['files'])} Lean files; no build run)")
