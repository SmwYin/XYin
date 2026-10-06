#!/usr/bin/env python3
"""Compile the retained bridge files in an existing, isolated pinned AINTLIB worktree.

This does not install dependencies, reset a checkout, or change the XYin toolchain.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


AINTLIB_REV = "ab1451487da02cd4483d0e2cdb2cc9e44bbbac17"
MATHLIB_REV = "300d0e535721bc098547106fc297d8ba2a63f6bb"
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
LIBRARY_CONFIG = '''
[[lean_lib]]
name = "AINTLIBDrafts"
[lean_lib.leanOptions]
autoImplicit = false
relaxedAutoImplicit = false
'''


def output(args, cwd, env):
    return subprocess.check_output(args, cwd=cwd, env=env, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worktree", required=True, type=Path)
    parser.add_argument("--elan-home", type=Path)
    parser.add_argument("--lake", type=Path, help="Optional exact pinned Lake binary.")
    args = parser.parse_args()
    worktree = args.worktree.resolve(strict=True)
    env = os.environ.copy()
    if args.elan_home:
        env["ELAN_HOME"] = str(args.elan_home.resolve(strict=True))
    lake = str(args.lake.resolve(strict=True)) if args.lake else "lake"
    lake_version = output([lake, "--version"], worktree, env)
    if "4.35.0-rc3" not in lake_version:
        raise SystemExit("The compiler must use the recorded Lean version.")

    if output(["git", "rev-parse", "HEAD"], worktree, env) != AINTLIB_REV:
        raise SystemExit("The AINTLIB worktree must be at the exact recorded revision.")
    if (worktree / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise SystemExit("Unexpected AINTLIB toolchain.")
    mathlib = worktree / ".lake/packages/mathlib"
    if output(["git", "rev-parse", "HEAD"], mathlib, env) != MATHLIB_REV:
        raise SystemExit("The mathlib dependency must be at the exact recorded revision.")
    dirty_sources = output(["git", "diff", "--name-only", "HEAD"], worktree, env).splitlines()
    if any(name != "lakefile.toml" for name in dirty_sources):
        raise SystemExit("Tracked AINTLIB sources differ from the recorded revision.")
    if output(["git", "diff", "--name-only", "HEAD"], mathlib, env):
        raise SystemExit("Tracked mathlib sources differ from the recorded revision.")

    source_dir = Path(__file__).resolve().parent / "AINTLIBDrafts"
    source_files = sorted(source_dir.glob("*.lean"))
    if not source_files:
        raise SystemExit("No retained bridge sources found.")
    target_dir = worktree / "AINTLIBDrafts"
    target_dir.mkdir(exist_ok=True)
    hashes = {}
    source_check_counts = {}
    expected_axiom_checks = 0
    sanity_examples = 0
    for source in source_files:
        target = target_dir / source.name
        content = source.read_bytes()
        source_text = content.decode("utf-8")
        source_check_counts[source.name] = len(re.findall(r"^#print axioms\s", source_text,
                                                        flags=re.MULTILINE))
        expected_axiom_checks += source_check_counts[source.name]
        sanity_examples += len(re.findall(r"^example(?:\s|\()", source_text,
                                         flags=re.MULTILINE))
        if source.resolve() != target.resolve():
            target.write_bytes(content)
        hashes[source.name] = hashlib.sha256(content).hexdigest()

    config = worktree / "lakefile.toml"
    text = config.read_text()
    original_config = subprocess.check_output(["git", "show", "HEAD:lakefile.toml"],
                                              cwd=worktree, env=env, text=True)
    if text == original_config:
        config.write_text(text + LIBRARY_CONFIG)
    elif text != original_config + LIBRARY_CONFIG:
        raise SystemExit("The existing Lake configuration differs from the recorded bridge setup.")

    targets = ["AINTLIBDrafts." + source.stem for source in source_files]
    log_path = worktree / "yzero-bridge-build.log"
    with log_path.open("w") as log:
        status = subprocess.run([lake, "build", *targets], cwd=worktree, env=env,
                                stdout=log, stderr=subprocess.STDOUT).returncode
    log_text = log_path.read_text()
    allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
    axiom_checks = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log_text)
    axiom_free_checks = re.findall(
        r"'([^']+)' does not depend on any axioms", log_text
    )
    observed_check_count = len(axiom_checks) + len(axiom_free_checks)
    observed_axioms = sorted({name.strip() for _, names in axiom_checks
                              for name in names.split(",") if name.strip()})
    unexpected_axioms = sorted(set(observed_axioms) - allowed_axioms)
    forbidden_axiom = "sorryAx" in log_text
    bridge_diagnostics = re.findall(
        r"^(?:warning|error): AINTLIBDrafts/.*$", log_text, flags=re.MULTILINE
    )
    changed_sources = [source.name for source in source_files
                       if hashlib.sha256(source.read_bytes()).hexdigest() != hashes[source.name]]
    changed_target_sources = [source.name for source in source_files
                              if not (target_dir / source.name).is_file()
                              or hashlib.sha256((target_dir / source.name).read_bytes()).hexdigest()
                              != hashes[source.name]]
    inventory_changed = sorted(source.name for source in source_dir.glob("*.lean")) != sorted(hashes)
    module_checks = {}
    module_check_failures = []
    for source in source_files:
        trace_path = worktree / ".lake/build/lib/lean/AINTLIBDrafts" / (source.stem + ".trace")
        try:
            trace = json.loads(trace_path.read_text())
            module_log = "\n".join(entry["message"] for entry in trace["log"])
            module_axioms = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",
                                      module_log)
            module_axiom_free = re.findall(r"'([^']+)' does not depend on any axioms", module_log)
            count = len(module_axioms) + len(module_axiom_free)
            axioms = sorted({name.strip() for _, names in module_axioms
                             for name in names.split(",") if name.strip()})
            diagnostics = [entry["message"] for entry in trace["log"]
                           if entry.get("level") in {"warning", "error"}]
            module_checks[source.name] = {
                "expected_axiom_check_count": source_check_counts[source.name],
                "observed_axiom_check_count": count,
                "observed_axioms": axioms,
                "axiom_free_declarations": sorted(set(module_axiom_free)),
                "audited_declarations": sorted({name for name, _ in module_axioms}
                                               | set(module_axiom_free)),
                "diagnostics": diagnostics,
            }
            if (count != source_check_counts[source.name] or diagnostics
                    or set(axioms) - allowed_axioms):
                module_check_failures.append(source.name)
        except (OSError, ValueError, KeyError, TypeError) as exc:
            module_checks[source.name] = {"trace_error": str(exc)}
            module_check_failures.append(source.name)
    receipt = {
        "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "aintlib_revision": AINTLIB_REV,
        "mathlib_revision": MATHLIB_REV,
        "toolchain": TOOLCHAIN,
        "lake_version": lake_version,
        "targets": targets,
        "source_sha256": hashes,
        "source_file_count": len(source_files),
        "sanity_example_count": sanity_examples,
        "sources_changed_during_build": changed_sources,
        "target_sources_changed_during_build": changed_target_sources,
        "source_inventory_changed_during_build": inventory_changed,
        "per_module_checks": module_checks,
        "module_check_failures": module_check_failures,
        "strict_lean_options": {"autoImplicit": False, "relaxedAutoImplicit": False},
        "build_exit_code": status,
        "sorryAx_in_build_output": forbidden_axiom,
        "observed_axioms": observed_axioms,
        "audited_declarations": sorted({name for name, _ in axiom_checks} | set(axiom_free_checks)),
        "axiom_free_declarations": sorted(set(axiom_free_checks)),
        "unexpected_axioms": unexpected_axioms,
        "expected_axiom_check_count": expected_axiom_checks,
        "observed_axiom_check_count": observed_check_count,
        "bridge_diagnostics": bridge_diagnostics,
        "build_log": str(log_path),
    }
    receipt_path = worktree / "yzero-bridge-receipt.json"
    receipt_path.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(receipt, ensure_ascii=False, indent=2))
    if (status or forbidden_axiom or unexpected_axioms or bridge_diagnostics or changed_sources
            or changed_target_sources or inventory_changed or module_check_failures
            or observed_check_count < expected_axiom_checks):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
