# Structural refactor — 2026-09-21

This pass surveys all project Lean modules for useful file splits, proof decomposition, and targeted cleanup. It is not a new exhaustive mathlib suitability review; the older overview and its evidence are preserved.

## Baseline

- `lake build`: passed (3918 jobs), log `/tmp/xyin-overview-baseline.log`.
- 78 Lean modules under `XYin/`, 24194 source lines, 1758 lexical named declarations.
- 19 active `sorry` tokens after excluding nested comments and strings. Existing proof gaps are baseline debt, not new failures.
- Cached dependencies were present; cache download was unnecessary. LSP returned diagnostics/partial states; authoritative checks use actual Lake builds.

## Selected work

| Target | Reason | Action |
|---|---|---|
| `Modularforms/summable_lems` | 1763 lines mixing three mathematical roles | Split into Basic, Reciprocal, QExpansion; retain compatibility import. |
| `Cox/ModularFunction` | Cusp data, level transforms, and level-one rationality share one file | Split CuspData and LevelJ from level-one proofs. |
| `CoxMatrices.exists_coxMatrix_reduction` | Repeats HNF orientation and matrix conversion | Reuse existing helpers; 60 → 12 source lines. |
| `CoxMatrices.rankTwoContent_mul_sl` | Duplicates HNF divisibility support | Expose the existing HNF theorem; delete three copied private helpers. |
| `tsumderivWithin` | Repeated local uniform derivative and majorant arguments | Share HasDerivAt result; use ContinuousMap norm and one geometric majorant proof. |
| `DimensionFormulas.weight_two_zero` | 112-line proof now covered by mathlib | Use levelOne_weight_two_rank_zero and rank_zero_iff_forall_zero. |
| Eisenstein cusp/q-expansion lemmas | Commented obsolete arguments and three sorrys | Use mathlib qExpansion_coeff_unique, canonical Taylor expansion, and inverse q-parameter. |
| `Summability.a1` | Geometric-series identity with a sorry | Prove using existing summable geometric series. |

## Other candidates retained

| Candidate | Decision |
|---|---|
| `LaurentQExpansion/LaurentQExpansion` (810 lines) | API is cohesive and below size limit; a future split should distinguish Laurent support from q-coordinate analysis. |
| `Cox/CoxMatrices/LaurentExpansion.laurentqExpansion_coxAction_coeff_aux` | Worth a general monomial-substitution helper, but needs a separate mathematical API pass. |
| `Modularforms/eta` transformation proofs | No matching S-transform theorem found in pinned mathlib; decomposition requires new analytic API. |
| `ModularFunctions/MeromorphicField` (662 lines) | General germ field versus upper-half-plane specialization is a valid future boundary; current size is moderate. |
| `Cox/LevelThree` (878 lines) | Mostly coherent finite polynomial computation; length alone does not justify decomposition. |
| `Cox/Kronecker`, `LatticeJ`, `CyclicSublattice` | Large but coherent developments; no selected exact-duplication win comparable to HNF. |
| `Modularforms/Eisenstein` | Targeted reuse reduces it below 1000 lines, so no extra module split is needed in this pass. |
| Remaining DimensionFormulas proof gaps | Independent formalization work, preserved rather than hidden by cleanup. |

## Complete file-level inventory

Counts are lexical source inventory, not a claim that every declaration was mathematically reviewed. Declaration spans are approximate. `XYin.lean` is the root import facade; unimported `ScratchGS.lean` is outside library inventory and unchanged.

| Baseline module | Lines before | Lines after | Named declarations before | Existing sorrys before |
|---|---:|---:|---:|---:|
| `Basic.lean` | 1 | 1 | 1 | 0 |
| `PhD/Cox/Arithmetic.lean` | 359 | 359 | 20 | 0 |
| `PhD/Cox/CoxMatrices/Basic.lean` | 971 | 897 | 75 | 0 |
| `PhD/Cox/CoxMatrices/Cardinality.lean` | 299 | 299 | 20 | 0 |
| `PhD/Cox/CoxMatrices/LaurentExpansion.lean` | 438 | 438 | 23 | 0 |
| `PhD/Cox/CoxMatrices.lean` | 14 | 14 | 0 | 0 |
| `PhD/Cox/CyclicSublattice/Classification.lean` | 423 | 423 | 27 | 0 |
| `PhD/Cox/CyclicSublattice.lean` | 671 | 671 | 73 | 0 |
| `PhD/Cox/DiagonalLaurent.lean` | 370 | 370 | 20 | 0 |
| `PhD/Cox/FormalCoxProduct.lean` | 272 | 272 | 15 | 0 |
| `PhD/Cox/HermiteNormalForm.lean` | 472 | 473 | 24 | 0 |
| `PhD/Cox/Kronecker.lean` | 793 | 793 | 63 | 0 |
| `PhD/Cox/KroneckerFrobenius.lean` | 241 | 241 | 14 | 0 |
| `PhD/Cox/LatticeJ.lean` | 691 | 691 | 51 | 0 |
| `PhD/Cox/LaurentPolynomialEvaluation.lean` | 176 | 176 | 10 | 0 |
| `PhD/Cox/LevelThree.lean` | 878 | 878 | 108 | 0 |
| `PhD/Cox/ModularFunction.lean` | 883 | 449 | 55 | 0 |
| `PhD/Cox/ModularFunctionField.lean` | 197 | 197 | 15 | 0 |
| `PhD/Cox/ModularPolynomial/AnalyticSupport.lean` | 106 | 106 | 5 | 0 |
| `PhD/Cox/ModularPolynomial/Construction.lean` | 444 | 445 | 43 | 0 |
| `PhD/Cox/ModularPolynomial/IntegralDescent.lean` | 372 | 372 | 26 | 0 |
| `PhD/Cox/ModularPolynomial/Interpolation.lean` | 649 | 649 | 37 | 0 |
| `PhD/Cox/ModularPolynomial/Irreducibility.lean` | 158 | 158 | 11 | 0 |
| `PhD/Cox/ModularPolynomial.lean` | 16 | 16 | 0 | 0 |
| `PhD/Cox/Section11BC.lean` | 22 | 22 | 0 | 0 |
| `PhD/Cox/SingularModuli.lean` | 250 | 250 | 15 | 0 |
| `PhD/Cox/SymmetricCubicLaurent.lean` | 452 | 452 | 38 | 0 |
| `PhD/Cox/UpperHalfPlaneFunctionField.lean` | 292 | 293 | 30 | 0 |
| `PhD/IntegralPowerSeries/IntegralPowerSeries.lean` | 240 | 240 | 32 | 0 |
| `PhD/LaurentQExpansion/Algebra.lean` | 451 | 451 | 25 | 0 |
| `PhD/LaurentQExpansion/LaurentQExpansion.lean` | 810 | 810 | 49 | 0 |
| `PhD/ModularFunctions/Basic.lean` | 97 | 97 | 11 | 0 |
| `PhD/ModularFunctions/Congruence.lean` | 150 | 150 | 9 | 0 |
| `PhD/ModularFunctions/CuspGrowth.lean` | 114 | 114 | 7 | 0 |
| `PhD/ModularFunctions/CuspPeriod.lean` | 62 | 62 | 3 | 0 |
| `PhD/ModularFunctions/Cusps.lean` | 88 | 88 | 5 | 0 |
| `PhD/ModularFunctions/FieldAction.lean` | 149 | 149 | 14 | 0 |
| `PhD/ModularFunctions/GrowthAtCusp.lean` | 73 | 73 | 5 | 0 |
| `PhD/ModularFunctions/JInvariant.lean` | 68 | 68 | 5 | 0 |
| `PhD/ModularFunctions/MeromorphicField.lean` | 662 | 662 | 61 | 0 |
| `PhD/ModularFunctions/NormalFormGrowth.lean` | 66 | 66 | 2 | 0 |
| `PhD/ModularFunctions/NormalFormSlash.lean` | 97 | 97 | 6 | 0 |
| `PhD/Modularforms/AtImInfty.lean` | 27 | 27 | 3 | 0 |
| `PhD/Modularforms/BigO.lean` | 149 | 149 | 7 | 0 |
| `PhD/Modularforms/Delta.lean` | 598 | 598 | 40 | 0 |
| `PhD/Modularforms/DimensionFormulas.lean` | 604 | 509 | 28 | 10 |
| `PhD/Modularforms/E2.lean` | 181 | 181 | 18 | 0 |
| `PhD/Modularforms/Eisenstein.lean` | 1068 | 940 | 71 | 4 |
| `PhD/Modularforms/Eisensteinqexpansions.lean` | 342 | 343 | 15 | 0 |
| `PhD/Modularforms/ForMathlib_Cusps.lean` | 21 | 21 | 2 | 0 |
| `PhD/Modularforms/IsCuspForm.lean` | 181 | 181 | 15 | 0 |
| `PhD/Modularforms/NormNumI.lean` | 207 | 207 | 16 | 1 |
| `PhD/Modularforms/ResToImagAxis.lean` | 480 | 480 | 39 | 0 |
| `PhD/Modularforms/SlashActionAuxil.lean` | 310 | 310 | 27 | 0 |
| `PhD/Modularforms/clog_arg_lems.lean` | 180 | 180 | 7 | 0 |
| `PhD/Modularforms/csqrt.lean` | 79 | 79 | 5 | 0 |
| `PhD/Modularforms/equivs.lean` | 46 | 46 | 6 | 0 |
| `PhD/Modularforms/eta.lean` | 172 | 172 | 4 | 0 |
| `PhD/Modularforms/exp_lems.lean` | 36 | 36 | 3 | 0 |
| `PhD/Modularforms/iteratedderivs.lean` | 169 | 169 | 6 | 0 |
| `PhD/Modularforms/multipliable_lems.lean` | 149 | 149 | 13 | 0 |
| `PhD/Modularforms/qExpansion_lems.lean` | 205 | 205 | 15 | 3 |
| `PhD/Modularforms/summable_lems.lean` | 1763 | 16 | 86 | 1 |
| `PhD/Modularforms/tsumderivWithin.lean` | 305 | 138 | 11 | 0 |
| `PhD/Modularforms/upperhalfplane.lean` | 21 | 21 | 2 | 0 |
| `PhD/Tactic2/LaurentQExpSimpTests.lean` | 63 | 63 | 0 | 0 |
| `PhD/Tactic2/QExpSimpAttr.lean` | 3 | 3 | 0 | 0 |
| `PhD/Tactic2/QExpSimpConditionTests.lean` | 55 | 55 | 0 | 0 |
| `PhD/Tactic2/qexp_simp.lean` | 207 | 207 | 27 | 0 |
| `PhD/jFunction/Deltaqexpansions.lean` | 337 | 337 | 41 | 0 |
| `PhD/jFunction/jInvariantLink.lean` | 81 | 81 | 7 | 0 |
| `PhD/jFunction/jLevelN.lean` | 212 | 212 | 15 | 0 |
| `PhD/jFunction/jfunction.lean` | 602 | 602 | 66 | 0 |
| `PhD/jFunction/qexp_coeffs.lean` | 163 | 163 | 24 | 0 |
| `PhD/qExpansion_tactic/Examples.lean` | 65 | 65 | 0 | 0 |
| `PhD/qExpansion_tactic/Qj.lean` | 304 | 304 | 28 | 0 |
| `PhD/qExpansion_tactic/link.lean` | 438 | 438 | 43 | 0 |
| `uniqueness.lean` | 334 | 334 | 15 | 0 |

## Refactor boundaries and compatibility

- `summable_lems` keeps its import path as a facade over `Summability.QExpansion`; all 86 declarations remain available. Basic → Reciprocal → QExpansion forms a linear dependency chain. The sole private `aux` remains beside `vector_norm_bound`.
- The 55 original Cox modular-function declarations retain their namespaces and mathematical statements. CuspData supplies raw-expression closure; LevelJ constructs the bundled `levelJModularFunction`; the original file proves level-one rationality using the new bundled definition.
- Moving `CuspData.polynomialIn` earlier exposed a short-name collision; references to the function are now explicitly `Cox.polynomialIn`. This changes resolution spelling, not mathematical meaning.
- `CoxMatrices.Basic` no longer imports the level-one rationality or lattice-classification proofs. Construction explicitly imports ModularFunction; UpperHalfPlaneFunctionField explicitly imports LatticeJ for `j_surjective`.
- `multipliable_lems` imports Basic and mathlib's logarithmic product API. Eisensteinqexpansions explicitly imports QExpansion. The product module's project dependency closure drops four substantive dependencies: BigO, iteratedderivs, tsumderivWithin, upperhalfplane.
- `Matrix.rankTwoContent_dvd_mul_right` is intentionally made public; its two supporting lemmas remain private. Three duplicate private lemmas are removed from CoxMatrices.
- No definitions or public mathematical statements are weakened. Existing names are retained, including older nonstandard names. Module-system files retain `module`, `public import`, and `@[expose] public section`.

## Decomposition and helper hygiene

| Proof body, including `by` | Before | After |
|---|---:|---:|
| `weight_two_zero` | 112 | 4 |
| `hasDerivAt_tsum_fun` | 28 | 14 |
| `derivWithin_tsum_fun'` | 27 | 2 |
| `iter_deriv_comp_bound3` | 66 | 21 |
| `iter_deriv_comp_bound2` | 72 | 5 |

The compact majorant construction remains one coherent 21-line argument: use the sup norm of the exponential on the compact set, prove that norm is strictly below one, and dominate each derivative by a polynomial times a geometric series. Further one-use wrappers would duplicate existing ContinuousMap API. The derivative-bound theorem is now a five-line application of that majorant at order `k + 1`.

No new helper was needed. Existing HNF helpers already separate orientation, conversion, and reduction; the reduction theorem now composes them. Their private visibility is retained. The shared public rank-two-content divisibility theorem is stated for arbitrary integer 2×2 matrices, without Cox-specific assumptions. New proof dependencies were checked against their exact source signatures.

Searches verified `ContinuousMap.norm_lt_iff`, `norm_coe_le_norm`, `summable_norm_pow_mul_geometric_of_norm_lt_one`, `hasDerivAt_of_tendstoLocallyUniformlyOn`, `ModularForm.levelOne_weight_two_rank_zero`, `ModularFormClass.qExpansion_coeff_unique`, and `hasSum_qExpansion_of_norm_lt`. The SmoothSeries interface requires a global majorant and cannot directly replace the per-compact hypothesis here. `fun_prop`, direct `simpa`, and explicit power inequalities succeeded; `gcongr` did not progress on the norm-power comparison. No resource limits were raised.

## Cleanup audit and simplify pass

Scope is the selected proof clusters, split boundaries, and their affected imports, not a claim of whole-repository mathlib-style conformance. Copyright/module descriptions were supplied for the newly split modules and the two cleanup files plus Eisenstein. Existing unrelated style warnings and the 15 remaining proof gaps are retained.

Two unused-instance-name warnings in Eisenstein (`inst_1`, `hn`) arise because the repaired proofs need fewer assumptions than the legacy signatures. The signatures are deliberately retained for compatibility; no artificial proof dependence or linter suppression was added. Older unrelated deprecations in that file are outside the chosen cleanup cluster.

Simplify outcome: **PASS-THROUGH**, fresh independent read-only reviewer after the fixes. The reviewer compared the start-of-turn snapshot, checked all moved declarations and private/section boundaries, verified the actual mathlib replacement types, and found no remaining source issue. The full build supplies the elaboration/caller gate; source normalization alone is not claimed to prove elaborated type equivalence.

Definition protection: no new mathematical definitions or changed definition bodies (the existing public API and normal-form modular-function framework are preserved). Theorem protection: mathematical signatures retained, apart from explicit qualification of previously unqualified names. Comment protection: discarded obsolete commented-out proof attempts only when superseded by actual proofs; split modules retain explanatory source comments.

## Performance check

The final derivative file and an isolated copy of the final weight-two proof were profiled with `-Dprofiler=true -Dprofiler.threshold=100`; both compiled and emitted no declaration/tactic over 100ms. Four exact repaired q-expansion proofs were also profiled in an isolated file with the pinned command syntax `#count_heartbeats in`:

| Declaration | Heartbeats reported |
|---|---:|
| `cuspfunc_lim_coef` | 190 |
| `cuspfunc_Zero` | 125 |
| `modfom_q_exp_cuspfunc` | 145 |
| `q_exp_unique` | 226 |

The four-proof probe compiled successfully with no >=100ms proof event; import time is excluded. These are final-proof measurements, not a claim of measured before/after speedup (three originals were `sorry`). Profiling wrappers are only in `/tmp`; no instrumentation was added to repository source.

Final build and axiom results are appended below.


## Final verification

- `lake build XYin XYin.PhD.Modularforms.summable_lems`: **PASS**, exit 0, 3916 jobs. This includes the complete library and explicitly checks the retained compatibility facade.
- `git diff --check`: **PASS**.
- All 83 internal module dependencies form a DAG.
- A source-header check preserved all 251 named declarations across the five principal groups (86 summability, 55 Cox modular functions, 11 derivatives, 28 dimension formulas, 71 Eisenstein declarations), modulo `Cox.polynomialIn` qualification. No names are lost or added in those groups.
- Source counts: 78 → 83 modules; 24,194 → 23,837 lines, a net reduction of **357 lines** despite adding module documentation. The largest Lean file is now 940 lines.
- Active `sorry` tokens: **19 → 15**. Removed `a1`, `cuspfunc_lim_coef`, `cuspfunc_Zero`, `q_exp_unique`; no new placeholder, axiom declaration, native proof, or limit raise.
- The final CoxMatrices profile also passed with no >=100ms proof event; an earlier concurrent profiling attempt encountered an import temporarily absent during rebuild and was rerun only after the build completed.
- Initial integration failures were resolved: `Cox.polynomialIn` qualification, the new mathlib/local cusp-submodule name collision, and explicit LatticeJ import for `j_surjective`. No known build failure remains.

Build/profiling evidence is recorded in `/tmp/xyin-overview-final-build.log`, `/tmp/xyin-overview-qexp-profiles.log`, `/tmp/xyin-overview-cox-profile.log`, `/tmp/xyin-tsum-cleanup-profile.log`, and `/tmp/xyin-weight-two-cleanup-profile.log`. Machine-readable inventories and structural gates are adjacent to this report. Pre-existing uncommitted modular-function work was preserved; no commit or push was performed.

Axiom gate: `lake env lean /tmp/xyin-overview-axioms.lean` **PASS**, exit 0. All 19 checked declarations depend only on `[propext, Classical.choice, Quot.sound]`, including the four repaired proofs, `weight_two_zero`/`dim_weight_two`, the derivative and majorant results, HNF/Cox reduction interfaces, `levelJModularFunction`, and Cox Theorems 11.9(i)/(ii). The remaining 15 `sorry`s elsewhere are not claimed to be axiom-free. Detailed output: `/tmp/xyin-overview-axioms.log`.
