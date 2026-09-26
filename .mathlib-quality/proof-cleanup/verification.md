# Final verification — broader proof cleanup

This turn compares against `/tmp/xyin-proof-cleanup-before/XYin`, after the earlier
modular-functions migration and structural splitting. Earlier uncommitted work was preserved.

## Outcome

- Inspected 83 Lean files; changed 56 and retained 27 after inspection.
- 23,837 → 19,649 source lines: net reduction 4,188 (including obsolete proof comments).
- 353 existing theorem/lemma bodies differ after stripping comments and normalizing whitespace.
- All existing public signatures remain unchanged. Eight bundled-definition proof fields changed;
  their mathematical data and maps did not. Ten private helpers and one shared public holomorphy
  lemma were added; six unused private helpers were removed.
- Existing admissions decreased from 15 to 1. The remaining declaration is
  `dim_gen_cong_levels` in `XYin/PhD/Modularforms/DimensionFormulas.lean:198`.

The per-file table is in `summary.md`; machine-readable coverage and source checks are in
`scoreboard.json` and `source-gates.json`. Batch reports give the actual mathematical API
replacements rather than treating file length as evidence of proof quality.

## Build and source gates

| Gate | Actual invocation/evidence | Result |
| --- | --- | --- |
| Baseline build | `lake build`; `/tmp/xyin-proof-cleanup-baseline.log` | Exit 0; 3,916 jobs |
| Per-file Lean checks | `lake env lean <file>`; commands/logs in each batch report | All changed files passed |
| Final cumulative build | `lake build`; `/tmp/xyin-proof-cleanup-final-build.log` | Exit 0; 3,917 jobs |
| Signature/trust audit | `python3 /tmp/xyin-final-source-gates.py`; `source-gates.json` | Exit 0; no signature mismatch, new admission, axiom, native proof or resource-limit raise |
| Whitespace check | `git diff --check` | Exit 0 |
| Independent review | `independent-review.md`, frozen source hashes | Five redundancy findings fixed; none unresolved |
| Final source/hash comparison | SHA-256 comparison of all 56 reviewed files | Zero differences from reviewed source |

The full build includes the project's configured mathlib standard linters. It passes with
warnings; this is not a claim of a warning-free repository. Existing header/deprecation/style
warnings remain, and the now-shortened `dim_modforms_lvl_one` retains its public named `hk`
hypothesis even though mathlib's stronger theorem makes it unused. The remaining admission is
also reported by Lean. No linter was disabled to suppress these diagnostics.

`build-result.txt` retains the final build receipt. Failed intermediate proof attempts were
corrected before integration; the final source is the version checked by both the independent
review and the cumulative build.

## Compiled axiom audit

Command: `lake env lean /tmp/xyin-audit-all.lean`, exit **0**.
The exact audit source is retained as `axiom-audit.lean.txt`; full output is `axiom-audit.txt`.
It traverses all theorem constants whose originating module belongs to `XYin`, then computes
their transitive axiom dependencies.

- **2,461 project theorem constants audited.** This includes generated declarations, so it is
  larger than the lexical declaration count in the source inventory.
- **2,460** use only a subset of `propext`, `Classical.choice`, `Quot.sound`.
- The sole exception is the original `dim_gen_cong_levels`, which still depends on `sorryAx`.
- Explicit checks of `E4E6_coeff_zero_eq_zero`, `Delta_E4_eqn`, `dim_modforms_lvl_one`,
  `j_mdifferentiable`, `jModularFunction`, the cusp-growth equivalence,
  `Cox.UpperHalfPlaneFunctionField.toMeromorphicField_eq_ratFunc`, and
  `Cox.theorem_11_9_ii` all have only the standard three axioms.

The earlier Dimension worker audit saw inherited `sorryAx` through the then-unfinished E4/E6
coefficient lemma. The final compiled audit supersedes it: that coefficient lemma is now proved.
The first final-audit attempt used one incorrect namespace in an explicit `#print axioms`;
that scratch command was corrected and the complete audit rerun successfully.

## Simplify pass — all changed Lean files

Outcome: **ISSUES-FOUND-AND-FIXED**.
Review: **fresh independent reviewer**, with coordinator inspection of actual patches.

Issues identified:
- Five private coefficient/coercion wrappers became unused after shared-API rewrites.
- Three callers repeated the same j-holomorphy proof.
- A shorter broad AC simplification increased elaboration cost in the j-factorization proof.

Fixes:
- Removed the five unused wrappers in `CyclicSublattice`, `DiagonalLaurent`, and `IntegralDescent`.
- Added the documented shared `j_mdifferentiable` next to `j`; retained the old qualified
  `ModularFunction.j_mdifferentiable` as a compatibility wrapper.
- Used targeted `simp only` followed by `ring` for factorization; final cost is 860 heartbeats,
  compared with 2,301 before cleanup and 8,400 in the discarded broad-simp attempt.

Verification: the full build and source gates above include all these fixes. The changed
follow-up files also passed direct profiler checks (`final-followup-profiler.json`).
Unresolved review findings: **none**. The existing general-level dimension admission is
explicitly outside this proof-shortening completion claim.

## Performance checks and limits

Every changed-file batch was profiled; actual commands and measurements are in the batch reports,
`root-profiler.json`, and `final-followup-profiler.json`. Scratch profiling/counting options were
not added to project source. Measurements used the same pinned mathlib APIs, and no project
heartbeat/depth limits were raised.

Representative deterministic improvements:

- Fourier growth estimate: 11,707 → 3,299 heartbeats.
- j slash invariance: 4,871 → 2,424 heartbeats.
- j constant coefficient: 5,354 → 2,404 heartbeats.

One deliberate cost tradeoff remains: `jN_differentiableAt` uses 5,072 rather than 2,509
heartbeats after sharing holomorphy and simplifying its proof structure. It remains far below
the unchanged limit and is explicitly documented in `jfunction.md`. No overall wall-clock
speedup is claimed: concurrent compilation and import-cache state affect those timings.

No commit, push, environment reset, or model-setting change was performed.
