# Cleanup worker rules — XYin, 2026-09-26 (read fully before starting)

The user asked: implement the 2026-09-25 overview's recommendations — "do everything that is not dangerous".
You are one of several workers. Each worker owns a disjoint set of files and works in a private sandbox.

## 1. Where you work
- Your sandbox `SB` (given in your task) is a full private copy of the project: sources, the cloned
  `.lake/build`, and `.lake/packages` (a symlink to the shared, read-only mathlib build).
- Do every edit and every build **inside SB only**. Never edit the main tree
  `/Users/dfa25dxu/Projects/Lean/XYin` (reading its `.mathlib-quality/` reports is fine).
  The orchestrator merges your owned files back after checking them.
- `SB.base` (the same path with `.base` appended) is a pristine copy of the sources at sandbox creation.
  To revert a file: `cp SB.base/<path> SB/<path>`.
- Never write under `SB/.lake/packages`, never run `lake update`, `lake clean`, `lake exe cache …`,
  never edit `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`. No git commands at all.
- Only edit, create or delete files inside your **owned set** (given in your task). You may add import
  lines to / remove import lines from `XYin.lean` for files you add or delete. Everything else is read-only.
- Scratch experiments: put them in `SB/.scratch/` (not under `XYin/`), run with `lake env lean <file>`.
  Import only the Mathlib modules you need (`import Mathlib` costs ≈ 2.5 min).

## 2. Building and checking (run all commands from SB)
- Fast single-file check: `lake env lean XYin/Path/To/File.lean` (uses the built `.olean`s of its imports).
- After editing a file that other files import, rebuild it before checking its importers:
  `lake build XYin.Path.To.File` (only what changed gets rebuilt).
- At most ONE `lake build` / `lake env lean` process at a time from you (the machine is shared by
  three workers; 12 cores, 24 GB RAM). Never run builds in the background in parallel.
- **Final gate (mandatory):** `lake build` (both default targets, `XYin` and `XYinTest`) in SB must end
  with `Build completed successfully`. If you cannot make a change work, revert it — a smaller green
  result is always better than a larger red one.
- The lean-lsp MCP tools (`lean_loogle`, `lean_leansearch`, `lean_local_search`, `lean_run_code`, …)
  may be available; they are attached to the MAIN tree, so use them only for mathlib search and
  standalone snippets, never to check your sandbox files. grep over `SB/.lake/packages/mathlib/Mathlib/`
  is always authoritative.

## 3. Safety policy ("not dangerous")
DO:
- Delete declarations that are mathlib duplicates, project duplicates, one-line wrappers/aliases, trivial
  `rfl`/`simpa` restatements, dead variables/imports/comments, template or scratch junk — after checking with
  `grep -rnw NAME SB/XYin SB/XYinTest SB/XYin.lean SB/XYinTest.lean` that nothing outside your set uses them
  (also check dot-notation `.NAME` uses), and after retargeting every use inside your set.
- Add missing API (simp families, closure lemmas, bridges, helpers, `@[ext]`, instances) and use it to shorten
  proofs. Additive changes are always allowed, anywhere in your owned set.
- Replace hand-rolled definitions/proofs with the mathlib API identified in the reports, when the proof works.
- Unify duplicates inside your set; make a private original public when it is re-proved elsewhere or is useful API.
- Fix stale comments/docstrings, unused imports, duplicated headers, deprecated syntax (`simp (config := …)`).
- Weaken hypotheses/typeclasses when the proof compiles unchanged and no caller breaks.

DON'T (dangerous — skip and list under "deferred" in your report):
- Delete **genuine mathematics** that is not available elsewhere (in pinned mathlib or in the project), even if
  currently unused. Keep it (you may tidy it). Genuine = a non-trivial statement with a real proof.
- Change the **name or statement** of any declaration used outside your owned set (grep first). Headline results
  must keep name and statement: `theorem_11_9_i`, `theorem_11_9_ii`, `theorem_11_9_ii_pointwise`,
  `theorem_11_18_i/ii/iii/iv_degree/iv_leadingCoeff/v`, `theorem_11_23`, `singularModulus_isIntegral`,
  `modularPolynomial_three`, `modularPolynomialThreeExplicit`, `modularPolynomial_three_of_complex_swap`,
  `lattice_eq_of_g₂_eq_of_g₃_eq`, `j_surjective`, `j_eq_iff_exists_sl2_smul_eq`, `card_coxMatrix`,
  `PeriodPair.weierstrassCurve_j`, `UpperHalfPlane.ellipticCurve_j`, `laurentqExpansion_coeff_eq_circleIntegral`,
  `exists_int_coeff_j_eq_principal_part_add_tsum_with_initial`, the explicit-coefficient lemmas of
  `jFunction/qexp_coeffs.lean`. (The single `sorry`, `dim_gen_cong_levels`, may be restated if it gets strictly
  better, e.g. a weaker hypothesis.)
- Rename public declarations for style only (the overview's naming-hygiene items) — defer. Renaming a
  placeholder name (`asdf`, `auxasdf`, `foo`…) of a declaration used only inside your set is fine.
- Change definitions in a way that changes their meaning; changing the *form* of a definition is allowed only
  if every use inside your set is updated and nothing outside your set can notice (e.g. it is only used in your
  set, or all external uses go through lemmas whose statements you keep).
- Introduce `sorry`, `admit`, `axiom`, `native_decide`, `set_option maxHeartbeats`/`maxRecDepth`/`synthInstance`
  increases, or `@[simp]` lemmas that loop.
- Delete the in-progress files `XYin/PhD/ModularFunctions/CuspPeriod.lean`, `Cusps.lean` or their declarations.
- Slow down kernel computations: if you touch anything reduced by `decide +kernel`/`rfl` proofs
  (`qExpansion_tactic/Qj.lean`, `link.lean`, `Cox/LevelThree.lean`, `jFunction/qexp_coeffs.lean`), time the
  affected files before and after (`time lake env lean F`); revert if more than 1.5× slower.

## 4. Style bar (mathlib conventions)
`fun x ↦ …`; lines ≤ 100 chars; docstrings on every new public def and main lemma; `theorem` for props;
term mode or short tactic proofs where natural; no non-terminal `simp` without `only`; keep the copyright
header + module docstring convention of the file; files in `XYin/PhD/Modularforms/` use the module system
(`module`, `public import`, `public section`/`@[expose]`) — keep it consistent there.

## 5. Evidence (read-only, main tree)
`/Users/dfa25dxu/Projects/Lean/XYin/.mathlib-quality/overview/analysis-2026-09-25/`:
`step4-analytic.md`, `step4-cox-compute.md` (mathlib replacements), `step5-duplications.md` (pairwise duplicate
table with verdicts + 77 helper statements, §6 per file), `step6-generalization.md`, `step7-api-analytic.md`,
`step7-api-cox.md` (missing lemmas with exact statements; **[C]** = scratch-compiled), `step8-junk.md` (junk,
per-file §3, non-declaration junk §4). Per-file inventories: `…/inventory-2026-09-25/<Module.Path>.md`.
Line numbers there refer to the 2026-09-25 tree (= your `SB.base`, except the 2026-09-26 Phase-0 changes:
`ScratchGS.lean` and `XYin/Basic.lean` deleted; the three test/example files moved to `XYinTest/`).
`grep -n` the reports for each of your file names. Treat every item as a hypothesis to verify, not an order;
refuted items are listed in the reports too (e.g. `jLaurentSeriesMod p = transformedJSeries 1 (sigmaZero p)` is
FALSE; `matrixStar ≠ adjugate`; `interpolationAt ≠ Lagrange.interpolate`).

## 6. Report (mandatory)
Write `SB/CLEANUP_REPORT.md` (full detail) and return a digest of at most 70 lines:
1. Final `lake build` result in SB (last 2 lines) — if not green, say so first.
2. Files changed / added / deleted, with line counts before → after.
3. Done items, one line each (what, where, lines saved, mathlib lemma or new helper used).
4. New public API added (name + one-line statement).
5. Kept on purpose: genuine-but-unused mathematics (names).
6. Deferred, with reason — especially **follow-ups that need edits outside your owned set** (file:line + what).
7. Perf measurements for any kernel-computation file you touched.
