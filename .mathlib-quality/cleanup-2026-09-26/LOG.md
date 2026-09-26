# Cleanup log — 2026-09-26 ("do everything that is not dangerous")

Backup of the pre-cleanup tree: `.mathlib-quality/backups/pre-cleanup-2026-09-26.tar.gz`
(all sources incl. the 15 git-untracked files, lakefile, manifest, overview, .mathlib-quality).
Restore a file: `tar -xzf .mathlib-quality/backups/pre-cleanup-2026-09-26.tar.gz <path>`.

Method: each worker edits a disjoint set of files in a private copy-on-write sandbox
(`/Users/dfa25dxu/Projects/Lean/.xyin-sandboxes/<name>`), must end with a green `lake build` there,
and is merged back with `sbx.sh merge` (refuses on conflicts / outside-ownership edits), followed by a
full `lake build` and the headline axiom audit (`AxiomCheck.lean`) in the main tree.

## Baseline (2026-09-26)
- `lake build`: green, 3917 jobs. Sorries: 1 (`dim_gen_cong_levels`). Headline axiom audit: 22/22 standard.

## Phase 0 (orchestrator, main tree)
- Deleted `ScratchGS.lean` (9 `#check`s) and `XYin/Basic.lean` (`def hello`), dropped `import XYin.Basic`.
- New test library `XYinTest` (lakefile `[[lean_lib]] XYinTest`, `defaultTargets = ["XYin", "XYinTest"]`):
  moved `Tactic2/LaurentQExpSimpTests`, `Tactic2/QExpSimpConditionTests`, `qExpansion_tactic/Examples`
  from the library into `XYinTest/`; root `XYinTest.lean`; removed their imports from `XYin.lean`.
- `lake build`: green, 3918 jobs.

## Workers
| Worker | Owned set | Status |
|---|---|---|
| mf | `Modularforms/**` | **merged** — 4,263 → 1,236 lines (16 files deleted); build green 3711 jobs; axioms 22/22; report-mf.md |
| lqe | `LaurentQExpansion/*`, `IntegralPowerSeries/*`, `uniqueness.lean` | **merged** — 69 new API decls, −227 lines on surviving decls, 16 dead decls removed; build green 3710 jobs; axioms 22/22; report-lqe.md |
| coxa | Cox HNF, CyclicSublattice(+Classification), CoxMatrices/{Basic,Cardinality}, ModularFunction/LevelJ, LatticeJ | **merged** — 3,380 → 2,957 lines; big new HNF/CoxMatrix API; build green 3710 jobs; axioms 22/22; report-coxa.md |
| coxb | Cox CoxMatrices/LaurentExpansion, FormalCoxProduct, LPE, DiagonalLaurent, SymmetricCubicLaurent, Kronecker, KroneckerFrobenius, LevelThree, ModularPolynomial/IntegralDescent | **merged** — 3,584 → 2,374 lines (−1,210; new `LaurentSeriesAux.lean`); one `jLaurentSeriesWidth` replaces 6 series defs; LevelThree 35 jet lemmas → 1 `decide +kernel` (≈0.86× time); build green 3712 jobs; axioms 22/22; report-coxb.md |
| jq | `jFunction/**`, `qExpansion_tactic/**`, `Tactic2/**`, `XYinTest/**` | **merged** — set 2,163 → 1,706 lines; engine on mathlib `σ`/`Array.ofFn`/`Finset` sums (kernel time within noise, ≤1.18× wall, ≤1.04× CPU); explicit integer witness for j's Laurent coefficients; 25 private helpers gone; tactic aliases → attribute registrations; 67 test warnings fixed; build green 3713 jobs; axioms OK; report-jq.md |
| mfn | `ModularFunctions/**` | **merged** — +≈170 API decls (1,611 → 2,919 lines incl. new `Algebra.lean`: `ModularFunction Γ` is an AddCommGroup/CommRing/Field/ℂ-algebra; `range_toMeromorphicField = subfield Γ`); growth closure set; build green 3711 jobs; axioms 22/22; report-mfn.md |
| coxc | ModularPolynomial/{AnalyticSupport,Construction,Interpolation,Irreducibility}, Arithmetic, SingularModuli, Cox/ModularFunction(+CuspData), UHPFF, ModularFunctionField, umbrellas | **merged** — 3,098 → 2,505 lines; A15 dedupe, Lagrange, general associated-±1 lemma, 11.9(i) field form; build green 3710 jobs; axioms 22/22; report-coxc.md |
| fina | integration wave A: follow-ups in the merged Cox (coxa+coxc sets), ModularFunctions, Modularforms files (not coxb/jq files) | **merged** + its verified post-merge patch — 17 files, −93 lines; new `Cox.theorem_11_9_ii_subfield` (Γ₀(N)-modular functions = ℂ(j, j_N) as subfields), `Cox.theorem_11_9_i_subfield`; Cox duplicates of mfn API removed; build green 3714 jobs; axioms OK; report-fina.md |
| sorry | fill `dim_gen_cong_levels` (Sturm bound for finite-index Γ via `ModularForm.norm`); owns `Modularforms/DimensionFormulas.lean` + new `Modularforms/SturmBound.lean` | **merged — sorry FILLED** (0 sorries now); new `SturmBound.lean` (260 lines): Sturm bound for arithmetic Γ, `FiniteDimensional ℂ (ModularForm Γ k)` instance; build green 3714 jobs; axioms 24/24; report-sorry.md |
| finb | integration wave B: remaining cross-folder follow-ups (whole tree; no other worker running) | **merged** — explicit `jIntCoeff`, `natScale` unified, global `FunLike (ℍ→ℂ)` instance + `qExpansion_ext` deleted, `transformedJSeries_injective`, lint 0 issues; report-finb.md |

## Final state (2026-09-26 evening)
- `lake build`: green, 3713 jobs, 0 warnings, 0 errors. `sorry`/`admit`: 0. `axiom`: 0. `maxHeartbeats`: 0.
- Axiom audit (`AxiomCheck.lean`): 27/27 standard. Lines 19,732 → 15,924; files 83 → 69; `@[simp]` 83 → 161.
- Sandboxes deleted; `Lint.lean` kept here for re-running the mathlib environment linters.
