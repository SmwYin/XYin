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
from unittest.mock import patch

from generate import collect_snapshot, discover_formathlib_projects, generate, parse_imports, validate_config
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


def discovery_config():
    config = sample_config()
    config["categories"].append({"id": "formathlib", "label": "Shared library", "description": "Keep my category name"})
    config["projects"].append({"id": "others-support", "categoryId": "phd", "parentId": None,
                               "label": "Support", "description": ""})
    config["assignments"] = [
        {"id": ident, "pattern": pattern, "projectId": "others-support", "approachId": None}
        for ident, pattern in (("fallback-xyin", "XYin/**/*.lean"),
                               ("fallback-tests", "XYinTest/**/*.lean"),
                               ("entry-xyin", "XYin.lean"), ("entry-tests", "XYinTest.lean"))
    ] + config["assignments"]
    return config


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

    def test_optional_discovery_metadata_is_backward_compatible_and_validated(self):
        self.assertEqual(validate_config(sample_config()), [])
        config = sample_config()
        config["discoveredForMathlibDirectories"] = ["Analysis", "LinearAlgebra"]
        self.assertEqual(validate_config(config), [])
        for values in (None, ["Analysis", "Analysis"], ["../Outside"], ["Hidden/File"],
                       [".Hidden"], ["."], ["Bad*Glob"], ["Bad?Glob"], ["Bad[Glob]"],
                       ["Back\\Slash"], ["Control\nName"], ["a" * 1001]):
            config["discoveredForMathlibDirectories"] = values
            self.assertTrue(validate_config(config), values)


class DiscoveryTests(unittest.TestCase):
    def test_adds_empty_directory_and_preserves_all_manual_rows_and_precedence(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("Analysis", "Algebra", ".Hidden", "Bad[Glob]"):
                (root / "XYin/ForMathlib" / name).mkdir(parents=True)
            (root / "XYin/ForMathlib/Linked").symlink_to(root / "XYin/ForMathlib/Algebra", target_is_directory=True)
            config = discovery_config()
            config["assignments"].extend([
                {"id": "manual-analysis", "pattern": "XYin/ForMathlib/Analysis/**", "projectId": "foundation", "approachId": "current"},
                {"id": "manual-algebra", "pattern": "XYin/ForMathlib/Algebra/Special/**/*.lean", "projectId": "foundation", "approachId": "current"},
            ])
            config["overrides"]["XYin/ForMathlib/Algebra/Override.lean"] = {"projectId": "foundation", "approachId": "current"}
            before = deepcopy(config)
            result, report = discover_formathlib_projects(config, root)
            self.assertEqual(config, before)
            self.assertEqual(result["categories"], before["categories"])
            self.assertEqual(result["overrides"], before["overrides"])
            self.assertEqual(report["directories"], ["Algebra", "Analysis"])
            self.assertEqual(report["projectsAdded"], ["fm-algebra"])
            self.assertEqual(report["rulesAdded"], ["fm-algebra"])
            self.assertEqual(result["assignments"][4]["id"], "fm-algebra")
            original_rules = [r for r in result["assignments"] if r["id"] not in report["rulesAdded"]]
            self.assertEqual(original_rules, before["assignments"])
            self.assertTrue(any("Bad[Glob]" in warning for warning in report["warnings"]))
            self.assertNotIn("Linked", result["discoveredForMathlibDirectories"])
            self.assertEqual(validate_config(result), [])

    def test_tombstones_preserve_deleted_or_narrowed_items_after_refresh(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            topic = root / "XYin/ForMathlib/Analysis"
            topic.mkdir(parents=True)
            config, _ = discover_formathlib_projects(discovery_config(), root)
            config["projects"] = [p for p in config["projects"] if p["id"] != "fm-analysis"]
            config["assignments"] = [r for r in config["assignments"] if r["id"] != "fm-analysis"]
            result, report = discover_formathlib_projects(config, root)
            self.assertEqual(result, config)
            self.assertEqual(report["projectsAdded"], [])
            self.assertEqual(report["directories"], [])
            topic.rmdir()
            result, _ = discover_formathlib_projects(config, root)
            self.assertEqual(result["discoveredForMathlibDirectories"], ["Analysis"])

    def test_project_reuse_ambiguous_labels_and_missing_category(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "XYin/ForMathlib/Analysis").mkdir(parents=True)
            config = discovery_config()
            config["projects"].append({"id": "my-analysis", "categoryId": "formathlib", "parentId": None,
                                       "label": "Analysis", "description": "Keep this description"})
            result, report = discover_formathlib_projects(config, root)
            self.assertEqual(report["projectsAdded"], [])
            rule = next(r for r in result["assignments"] if r["id"] in report["rulesAdded"])
            self.assertEqual(rule["projectId"], "my-analysis")
            self.assertEqual(result["projects"], config["projects"])
            config["projects"].append({**config["projects"][-1], "id": "second-analysis"})
            result, report = discover_formathlib_projects(config, root)
            self.assertEqual(result, config)
            self.assertTrue(report["warnings"])
            result, report = discover_formathlib_projects(sample_config(), root)
            self.assertEqual(result, sample_config())
            self.assertTrue(report["warnings"])

    def test_collision_safe_ids_and_stop_at_manual_fallback(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("New Topic", "New-Topic"):
                (root / "XYin/ForMathlib" / name).mkdir(parents=True)
            config = discovery_config()
            config["assignments"][1]["pattern"] = "XYinTest/Custom/**"
            config["projects"].append({"id": "fm-new-topic", "categoryId": "phd", "parentId": None,
                                       "label": "Unrelated", "description": ""})
            result, report = discover_formathlib_projects(config, root)
            self.assertEqual(len(set(report["projectsAdded"])), 2)
            self.assertNotIn("fm-new-topic", report["projectsAdded"])
            self.assertEqual(result["assignments"][0], config["assignments"][0])
            self.assertEqual(result["assignments"][3:], config["assignments"][1:])
            self.assertEqual(validate_config(result), [])

    def test_generator_idempotence_and_external_configuration_race(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture(root)
            (root / "XYin/ForMathlib/Analysis").mkdir(parents=True)
            path = root / "progress/config.json"
            path.write_text(json.dumps(discovery_config()))
            first = generate(root)
            self.assertEqual(first["discovery"]["projectsAdded"], ["fm-analysis"])
            raw = json.dumps(first["config"], separators=(",", ":")).encode()
            path.write_bytes(raw)
            second = generate(root)
            self.assertEqual(path.read_bytes(), raw)
            self.assertEqual(second["discovery"]["directories"], [])
            # A user edits the configuration while scanning; that edit must win.
            (root / "XYin/ForMathlib/Topology").mkdir()
            external = deepcopy(first["config"])
            external["categories"][0]["label"] = "External edit"
            original_collect = collect_snapshot
            def concurrent_edit(repo_root):
                snapshot = original_collect(repo_root)
                path.write_text(json.dumps(external))
                return snapshot
            with patch("generate.collect_snapshot", side_effect=concurrent_edit):
                with self.assertRaises(ConfigConflict):
                    generate(root)
            self.assertEqual(json.loads(path.read_text()), external)

    def test_server_reads_do_not_discover_and_stale_refresh_has_no_effect(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture(root)
            (root / "XYin/ForMathlib/Analysis").mkdir(parents=True)
            path = root / "progress/config.json"
            raw = json.dumps(discovery_config()).encode()
            path.write_bytes(raw)
            dashboard = Dashboard(root)
            self.assertEqual(path.read_bytes(), raw)
            self.assertEqual(dashboard.get_state()["config"], discovery_config())
            with self.assertRaises(ConfigConflict):
                dashboard.refresh("stale-revision")
            self.assertEqual(path.read_bytes(), raw)
            result = dashboard.refresh(dashboard.state["revision"])
            self.assertEqual(result["discovery"]["projectsAdded"], ["fm-analysis"])
            external = deepcopy(result["config"])
            external["categories"][0]["label"] = "External edit"
            external_raw = json.dumps(external).encode()
            path.write_bytes(external_raw)
            (root / "XYin/ForMathlib/Topology").mkdir()
            dashboard.get_state()
            self.assertEqual(path.read_bytes(), external_raw)
            self.assertNotIn("Topology", dashboard.state["config"]["discoveredForMathlibDirectories"])


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
    def test_external_edit_during_save_is_retained(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture(root)
            dashboard = Dashboard(root)
            source = root / "XYin/PhD/Basic.lean"
            source_before = source.read_bytes()
            config_path = root / "progress/config.json"
            snapshot_before = (root / "progress/snapshot.json").read_bytes()
            html_before = (root / "progress/index.html").read_bytes()
            original_revision = dashboard.state["revision"]
            submitted = sample_config()
            submitted["categories"][0]["label"] = "Browser draft"
            external = sample_config()
            external["categories"][0]["label"] = "External editor change"
            external_bytes = json.dumps(external).encode("utf-8")

            def edit_during_scan(repo_root):
                snapshot = collect_snapshot(repo_root)
                config_path.write_bytes(external_bytes)
                return snapshot

            with patch("server.collect_snapshot", side_effect=edit_during_scan):
                with self.assertRaises(ConfigConflict):
                    dashboard.save(submitted, original_revision)
            self.assertEqual(config_path.read_bytes(), external_bytes)
            self.assertEqual((root / "progress/snapshot.json").read_bytes(), snapshot_before)
            self.assertEqual((root / "progress/index.html").read_bytes(), html_before)
            self.assertEqual(dashboard.state["revision"], original_revision)
            self.assertEqual(source.read_bytes(), source_before)

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
                self.assertEqual(request("POST", "/api/refresh", {"baseRevision": "stale"}, "http://" + host)[0], 409)
                self.assertEqual(request("POST", "/api/refresh", {"baseRevision": []}, "http://" + host)[0], 400)
                self.assertEqual(request("POST", "/api/refresh", {"extra": True}, "http://" + host)[0], 400)
                self.assertEqual(request("POST", "/api/refresh", {"baseRevision": dashboard.state["revision"]}, "http://" + host)[0], 200)
                self.assertEqual(request("POST", "/api/refresh", {}, "http://" + host)[0], 200)
            finally:
                server.shutdown()
                server.server_close()
                thread.join()


if __name__ == "__main__":
    unittest.main()
