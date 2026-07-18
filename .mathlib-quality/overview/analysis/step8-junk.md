# Step 8 — Junk identification

Method: every "unused in file" declaration from the 44 inventories was collected (152 names) and
grep-verified project-wide with word-boundary patterns (`grep -rnE "\b<name>\b" XYin/ XYin.lean
ScratchGS.lean`, excluding `XYin/PhD/Modularforms/` and `.lake`). Unicode-subscript names
(`diagonal_eval₂`, `weierstrassCurve_c₆`) and namespaced short names (`.sum`, `.shift`,
`.coeff_zero`) were re-checked with exact fixed-string greps. Instance/simp/dot-notation
invisible usage was checked by hand (see entries 55, 68, 78).

## REMOVE — dead code (grep-verified: no occurrence outside definition site / doc-comment)

1. **`hello`** (XYin/Basic.lean:1) — REMOVE — lakefile scaffold stub, 1 grep hit (def only) — delete `XYin/Basic.lean` and the `import XYin.Basic` line in `XYin.lean:1`.
2. **`ScratchGS.lean`** (project root, 11 lines) — REMOVE — orphan scratch file: 9 `#check` lines and one import, not imported by anything (not in `XYin.lean`) — delete the file.
3. **`XYin/PhD/ModularFunctions/Basic.lean`** (0 bytes) — REMOVE — empty file, only effect is a no-op import — delete file, delete `import XYin.PhD.ModularFunctions.Basic` (XYin.lean:5), remove the now-empty `ModularFunctions/` directory.
4. **`invariantsDetermineLattice`** (XYin/uniqueness.lean:328) — REMOVE — 1-line restatement of `lattice_eq_of_g₂_eq_of_g₃_eq`; docstring references nonexistent `talk4.lean`; 1 grep hit — delete the theorem (and its stale docstring). The file itself is live (`LatticeJ.lean:11` imports it).
5. **`HasIntegralQExpansion.sum`** (XYin/PhD/IntegralPowerSeries/HasIntegralQExpansion.lean:29) — REMOVE — **contains a `sorry`** and is used nowhere (1 grep hit); removing it removes a sorry from the project — delete.
6. **`IsIntegralPowerSeries.shift`** (HasIntegralQExpansion.lean:25) — REMOVE — 1 grep hit; a 1-line wrapper over `IntegralPowerSeriesSubring.mul_mem` with no consumer — delete.
7. **`IsIntegralPowerSeries_X_pow`** (HasIntegralQExpansion.lean:15) — REMOVE — only consumer is entry 6 (cascade) — delete with it.
8. **`HasIntegralQExpansion` + `HasIntegralQExpansion_ofPowerSeries`** (HasIntegralQExpansion.lean:6, 9) with consumers **`Delta_hasIntegralQExpansion`, `E4_hasIntegralQExpansion`, `E6_hasIntegralQExpansion`, `j_hasIntegralQExpansion`** (jFunction/jfunction.lean:639, 642, 645, 648) — REMOVE (speculative closed subgraph) — `ofPowerSeries`'s only 3 uses are the Delta/E4/E6 theorems; those 4 theorems are used nowhere; the integrality facts they express are carried by the *used* `*_isIntegralPowerSeries` lemmas and `j_laurentQExpansion_isIntegral` — delete the 4 jfunction theorems and retire `HasIntegralQExpansion.lean` entirely (with entries 5–7 the file is then empty); fix `jfunction.lean:9` to import `XYin.PhD.IntegralPowerSeries.IntegralPowerSeries` directly, and see entry 47 for `LaurentQExpansion.lean:2`.
9. **`mem_powerSeriesMapSubmodule_iff_coeff`** (XYin/PhD/IntegralPowerSeries/IntegralPowerSeries.lean:47) — REMOVE — speculative submodule infrastructure, 1 grep hit — delete.
10. **`powerSeriesMapAlgHom_injective`** (IntegralPowerSeries.lean:89) — REMOVE — 1 grep hit, no consumer — delete.
11. **`mem_modularFormQExpansionSubmodule_iff_coeff`** (IntegralPowerSeries.lean:211) — REMOVE — speculative modular-form-submodule layer never consumed — delete (with entry 12).
12. **`modularFormQExpansionLinearMap`** (IntegralPowerSeries.lean:218) — REMOVE — 1 grep hit; built for a future that never came — delete.
13. **`order`** (XYin/PhD/LaurentQExpansion/LaurentQExpansion.lean:666) — REMOVE — generic-named (`theorem order`!) duplicate characterization of `poleOrder` via `meromorphicOrderAt`; the used form is `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder`; 1 grep hit — delete (or, if kept, rename to `poleOrder_eq_toNat_neg_meromorphicOrderAt`).
14. **`cuspFunction_to_analyticAt_meromorphicAt`** (LaurentQExpansion.lean:788) — REMOVE — 1-line wrapper (`analyticAt_...poleRemoved ... |>.meromorphicAt`), 1 grep hit — delete; callers can use the analytic sibling directly.
15. **`I∞` local notation** (LaurentQExpansion.lean:14) — REMOVE — declared and then never used (1 grep hit in file) — delete the line.
16. **test 5 duplicate example** (XYin/PhD/Tactic2/LaurentQExpSimpTests.lean:35–40) — REMOVE — verbatim byte-for-byte duplicate of test 4 (lines 28–33) — delete one copy.
17. **`jIntegralLaurentSeries_map_complex`** (XYin/PhD/Cox/Kronecker.lean:176) — REMOVE — series-level restatement of the used `jIntCoeff_spec`, 1 grep hit — delete.
18. **`specializeJMod_varX`** (Kronecker.lean:499) — REMOVE — not `@[simp]` (unlike its used-invisibly sibling `varY`), 1 grep hit — delete (or tag `@[simp]` if the pair is wanted as API; see entry 68).
19. **`transformedJSeries_one_sigmaZero_eq_primeLower_pow`** (XYin/PhD/Cox/KroneckerFrobenius.lean:176) — REMOVE — stepping stone that the final `theorem_11_18_v` proof does not use; 1 grep hit — delete.
20. **`cyclicSublattice_hnf_matrix`** (XYin/PhD/Cox/CyclicSublattice/Classification.lean:341) — REMOVE — 1-line duplicate of `hermiteNormalForm_matrix_eq_inclusionMatrix` (which also powers the kept `@[simp]` entry 78); 1 grep hit — delete.
21. **`ratFuncEvalJ_injective`** (XYin/PhD/Cox/UpperHalfPlaneFunctionField.lean:110) — REMOVE — unused (1 grep hit) and trivially recoverable: any ring hom out of the field `RatFunc ℂ` is injective (`RingHom.injective`) — delete.
22. **`Delta_qExpansion_coeff_zero_aux`** (XYin/PhD/jFunction/Deltaqexpansions.lean:92) — REMOVE — private, 1 grep hit, superseded by the tactic-computed route in qexp_coeffs — delete.
23. **`transportedBasis_apply_coe`** (XYin/PhD/Cox/CyclicSublattice.lean:350) — REMOVE — `private @[simp]`, so it can only fire inside this file, and no later in-file `simp` touches `transportedBasis` goals per the inventory — delete; re-run `lake build` to confirm no in-file simp relied on it.
24. **Duplicated copyright header** (XYin/PhD/Cox/DiagonalLaurent.lean:1–10) — REMOVE — the 5-line copyright block appears twice back-to-back — delete lines 6–10.
25. **`#min_imports`** (IntegralPowerSeries.lean:238) — REMOVE — leftover debugging command — delete the line.

## INLINE

26. **`meromorphicOrderAt_cuspFunction_eq_neg_poleOrder`** (LaurentQExpansion.lean:662) — INLINE — body is a single call to `..._of_ne_zero`; exactly 2 call sites (Cox/ModularFunction.lean ×2) — inline the `_of_ne_zero` form at both sites and delete, or keep if the shorter name is judged worth it.

## REPLACE — imports / hygiene

27. **`import XYin.PhD.Cox.FormalCoxProduct`** (XYin/PhD/Cox/ModularPolynomial/Construction.lean:6) — REPLACE — Construction uses nothing from FormalCoxProduct (grep: no `formalCox*`/`reindex_bijective`/`zeta` in file); but IntegralDescent.lean consumes `formalCoxPolynomial_coeff_isInteger` *transitively through Construction* — move the import to `ModularPolynomial/IntegralDescent.lean` and rebuild.
28. **`import XYin.PhD.Modularforms.Eisenstein` + `import XYin.PhD.IntegralPowerSeries.HasIntegralQExpansion`** (LaurentQExpansion/LaurentQExpansion.lean:1–2) — REPLACE — no Eisenstein identifier (`E4`, `E6`, …) and no `HasIntegralQExpansion`/`IsIntegralPowerSeries` identifier occurs in the file; the file only needs `Mathlib.NumberTheory.ModularForms.QExpansion` (currently supplied transitively) — swap both for the Mathlib import. **Caution**: the `open … IntegralPowerSeries` on line 11 becomes an unknown-namespace error (delete it too), and downstream files (`Algebra.lean`, Cox files, `link.lean`) that consumed Eisenstein transitively must import it directly. Verify with `lake build`.
29. **`set_option linter.style.header false`** (qExpansion_tactic/link.lean:4, qExpansion_tactic/Examples.lean:3, LaurentQExpansion/LaurentQExpansion.lean:7, IntegralPowerSeries/IntegralPowerSeries.lean:3) — REPLACE — add the standard copyright header to these 4 files and drop the linter escape.
30. **`-- double check` TODO** (LaurentQExpansion.lean:798) — REPLACE — unresolved review marker above `exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt` — review the lemma once and delete the comment.

## KEEP-INTENTIONAL — terminal results, documentation-grade facts, API symmetry

31. **`theorem_11_18_i`** (Cox/Arithmetic.lean:22) — KEEP-INTENTIONAL — terminal Cox Thm 11.18(i).
32. **`theorem_11_18_ii`** (Arithmetic.lean:28) — KEEP-INTENTIONAL — terminal Cox Thm 11.18(ii).
33. **`theorem_11_18_iv_degree`** (Arithmetic.lean:310) — KEEP-INTENTIONAL — terminal Cox Thm 11.18(iv).
34. **`theorem_11_18_v`** (KroneckerFrobenius.lean:229) — KEEP-INTENTIONAL — terminal Kronecker congruence, Cox Thm 11.18(v).
35. **`theorem_11_9_ii`** (Cox/ModularFunctionField.lean:165) — KEEP-INTENTIONAL — terminal Cox Thm 11.9(ii).
36. **`modularPolynomial_three`** (Arithmetic.lean:351) — KEEP-INTENTIONAL — terminal explicit Φ₃, Cox equation (11.22).
37. **`card_coxMatrix`** (CoxMatrices/Cardinality.lean:291) — KEEP-INTENTIONAL — terminal counting formula (σ₁-type divisor sum).
38. **`singularModulus_isIntegral`** (Cox/SingularModuli.lean:245) — KEEP-INTENTIONAL — headline theorem: singular moduli are algebraic integers.
39. **`j_eq_iff_exists_sl2_smul_eq`** (Cox/LatticeJ.lean:603) — KEEP-INTENTIONAL — headline characterization `j τ = j τ' ↔ SL₂(ℤ)-equivalence`.
40. **`cusp_laurent_finitePrincipalPart`** (Cox/ModularFunction.lean:123) — KEEP-INTENTIONAL — documented interpretation "meromorphic at the cusp = finite principal part"; API endpoint of the modular-function definition.
41. **`j_cuspFunction_not_analyticAt`** (jfunction.lean:698) — KEEP-INTENTIONAL — documents that `j` genuinely has a pole (complements the used `j_cuspFunction_meromorphicAt`).
42. **`jN_cuspFunction_meromorphicAt`** (jFunction/jLevelN.lean:200) — KEEP-INTENTIONAL — headline result named in the module docstring (line 20).
43. **`ellipticCurve_j`** (jFunction/jInvariantLink.lean:82) — KEEP-INTENTIONAL — the terminal theorem of the file: the Weierstrass-model `j` equals the analytic `j`.
44. **`weierstrassCurve_c₆`** (jInvariantLink.lean:45) — KEEP-INTENTIONAL — API symmetry: sibling `weierstrassCurve_c₄` is used at line 66; `c₆ = 216·g₃` is a documented computed fact.
45. **`E6_int_link`** (qExpansion_tactic/link.lean:186) — KEEP-INTENTIONAL — API symmetry: `E4_int_link` is used at link.lean:494.
46. **`bN_eq`** (Cox/HermiteNormalForm.lean:338) — KEEP-INTENTIONAL — HNF-basis uniqueness; the HNF file is billed as a "reusable rank-two HNF API" (Section11BC docstring).
47. **13 q-coefficient lemmas in qexp_coeffs.lean** — `ramanujanTau_one/_two/_three` (:29/:33/:37), `Delta_qExpansion_coeff_two/…/_five` (:54/:60/:66/:72), `j_laurentQExpansion_coeff_neg_one/…/_three` (:146/:149/:152/:155/:158), `exists_int_coeff_j_eq_principal_part_add_tsum_with_initial` (:122) — KEEP-INTENTIONAL — documentation-grade computed facts (τ(2) = −24, j-coefficients 744, 196884, 21493760, 864299970, …) certifying the q-expansion tactic; the last is the file's terminal expansion theorem.
48. **`hasCoeffsIn_one` / `hasCoeffsIn_neg` / `hasCoeffsIn_sub` / `hasCoeffsIn_C_algebraMap`** (IntegralPowerSeries.lean:56/:75/:79/:83) — KEEP-INTENTIONAL — ring-closure API family; sibling `hasCoeffsIn_mul` is used (jfunction.lean).
49. **`laurentqExpansion.coeff_of_qExpansion`** (LaurentQExpansion.lean:575), **`laurentqExpansion.coeff_zero`** (:587), **`laurentqExpansion.to_qExpansion_eq_powerSeriesPart`** (:721) — KEEP-INTENTIONAL — core bridge API between `laurentqExpansion` and Mathlib's `qExpansion` (sibling `eq_qExpansion_iff` is used 3× in Algebra.lean).
50. **`laurentqExpansion_coeff_eq_circleIntegral`** (LaurentQExpansion.lean:819) — KEEP-INTENTIONAL — substantive contour-integral coefficient formula; a natural API endpoint.
51. **Tactic test files** — `QExpSimpConditionTests.lean` (8 examples), `LaurentQExpSimpTests.lean` (tests 1–4, 6–8), `qExpansion_tactic/Examples.lean` (4 examples incl. the deliberate `#check qexp_coeff …` demos at :12–:23) — KEEP-INTENTIONAL — regression/demo files for the two tactic frameworks (the only genuine junk there is entry 16).
52. **`qexp_simp` tactic (both arg forms)** (Tactic2/qexp_simp.lean) and **`register_simp_attr qexp_simps`** (Tactic2/QExpSimpAttr.lean) — KEEP-INTENTIONAL/KEEP-USED — user-facing entry points; `@[qexp_simps]` is applied 10+ times in qexp_simp.lean, and the tactic is exercised by both test files.
53. **`#qexp` command + `qexp_coeff` term elabs** (qExpansion_tactic/Qj.lean) — KEEP-USED — exercised by Examples.lean:12–23.
54. **`instance : DecidableEq (CoxMatrix m)`** (CoxMatrices/Basic.lean:114) — KEEP-INTENTIONAL — instances are used invisibly by `Finset`/`Fintype` machinery over `CoxMatrix`; do not remove without a full build check.
55. **`coe_smulLatticeEquiv_apply` / `coe_smulLatticeEquiv_symm_apply`** (LatticeJ.lean:90/:95) — KEEP-INTENTIONAL — `@[simp]` coercion API for `smulLatticeEquiv`, which is used (CyclicSublattice.lean:248–276); public simp lemmas can fire invisibly downstream.

## KEEP-USED — unused in defining file, grep-verified cross-file usage

56. **`inclusionMatrix_content_eq_one`** (CoxMatrices/Basic.lean) — KEEP-USED-AT CyclicSublattice/Classification.lean.
57. **`one_lt_card_coxMatrix`** (CoxMatrices/Basic.lean) — KEEP-USED-AT Arithmetic.lean.
58. **`gamma0RightCosetsFintype`** (CoxMatrices/Basic.lean:153) — KEEP-USED — *instance*, consumed invisibly by `∏ c : Gamma0RightCosets m` (ModularPolynomial/Construction.lean:209 and elsewhere).
59. **`exists_rightCosetMul_baseRightCoset_eq`** — KEEP-USED-AT ModularPolynomial/Irreducibility.lean.
60. **`rightCosetEval_smul`, `rightCosetEval_equiv`, `rightCosetTranslate_sigmaZero`, `j_act_sigmaZero`** (CoxMatrices/Basic.lean) — KEEP-USED-AT Construction/Interpolation/UpperHalfPlaneFunctionField.
61. **`exists_sl2_mul_eq_coxMatrix`** — KEEP-USED-AT SingularModuli.lean.
62. **`zeta_isPrimitiveRoot`, `jIntCoeff_neg_one`, `laurentqExpansion_coxAction`** (CoxMatrices/LaurentExpansion.lean) — KEEP-USED-AT DiagonalLaurent/FormalCoxProduct/Kronecker/LevelThree/IntegralDescent/UpperHalfPlaneFunctionField (`laurentqExpansion_coxAction` is additionally a designated terminal result).
63. **`reindex_bijective`** (LaurentExpansion.lean:428) — KEEP-USED-AT FormalCoxProduct.lean:169.
64. **`theorem_11_23`** (Classification.lean:398) — KEEP-USED-AT Arithmetic.lean:39–45 (×4).
65. **`j_ofLatticeEq`, `j_scale`** (CyclicSublattice.lean) — KEEP-USED-AT Classification.lean; **`dual_sub_j`, `dual_base_j`** — KEEP-USED-AT Arithmetic.lean:41–47.
66. **`range_toLin_matrix_eq`, `index_eq_natAbs_det`, `quotient_isAddCyclic_iff_rankTwoContent_eq_one`** (HermiteNormalForm.lean) — KEEP-USED-AT CyclicSublattice(+Classification); **`Submodule.hermiteNormalForm`** (:467) — KEEP-USED-AT CyclicSublattice.lean:57 via **dot notation** `S.carrier.hermiteNormalForm …` (invisible to plain name-grep).
67. **`primeCoxMatrixEquiv_symm_apply_of_lt/_last`, `jUnitLaurentSeriesMod_pow_prime`, `specializeJMod_injective`, `specializeJMod_modularPolynomial_eq_formal`** (Kronecker.lean) — KEEP-USED-AT KroneckerFrobenius.lean.
68. **`jIntegralLaurentSeries_coeff`** (Kronecker.lean:172) and **`specializeJMod_varY`** (:506) — KEEP-INTENTIONAL — `@[simp]` rfl-lemmas on live defs; may fire invisibly in later `simp` calls (inventory "used by" tracking cannot see simp firing).
69. **`j_surjective`** (LatticeJ.lean:699) — KEEP-USED-AT Classification/Construction/UpperHalfPlaneFunctionField (also terminal).
70. **`laurentSeriesMapRingHom_coeff`, `bivariateSpecializeLaurent_map_apply`, `polynomial_eval₂_laurentSeries_injective`** (LaurentPolynomialEvaluation.lean) — KEEP-USED-AT Kronecker.lean.
71. **`modularPolynomial_three_of_complex_swap`** (LevelThree.lean) — KEEP-USED-AT Arithmetic.lean:353 (proves eq. (11.22)).
72. **`RationalInTwo`** (ModularFunction.lean:61) — KEEP-USED-AT Interpolation.lean:610, 641.
73. **`levelJ_isGamma0ModularFunction`, `theorem_11_9_i`** (ModularFunction.lean) — KEEP-USED-AT ModularFunctionField/AnalyticSupport/Interpolation (`theorem_11_9_i` used at Interpolation.lean:644; also terminal).
74. **`coxLinearFactor_coeff_cuspMeromorphicAt`, `polynomial_prod_coeff_cuspMeromorphicAt`, `periodic_comp_of_slashInvariant_one`** (AnalyticSupport.lean) — KEEP-USED-AT Construction/Interpolation/IntegralDescent.
75. **All 12 flagged Construction.lean decls** (`BivariatePolynomial.varX/varY/eval_swap/coeff_coeff_swap/map_swap/diagonal_eval/diagonal_map/diagonal_eval₂/diagonal_swap`, `modularPolynomialC_rightCosetProduct/_eval_levelJ_j/_natDegree`) — KEEP-USED-AT Arithmetic/Kronecker/KroneckerFrobenius/LevelThree/DiagonalLaurent/SingularModuli/SymmetricCubicLaurent/Interpolation/Irreducibility (every one has ≥1 cross-file call site).
76. **`modularPolynomial_monic`** (IntegralDescent.lean:362) — KEEP-USED-AT Arithmetic.lean:135; **`theorem_11_9_ii_pointwise`** (Interpolation.lean) — KEEP-USED-AT ModularFunctionField.lean:170; **`modularPolynomialC_irreducibleInX`** (Irreducibility.lean) — KEEP-USED-AT Arithmetic.lean (×3); **`modularPolynomialC_diagonal_leadingCoeff_pow`** (DiagonalLaurent.lean) — KEEP-USED-AT Arithmetic.lean; **`formalCoxPolynomial_coeff_isInteger`** (FormalCoxProduct.lean:251) — KEEP-USED-AT IntegralDescent.lean; **`symmetric_bidegree_three_eq_zero_of_laurent_coeff`** (SymmetricCubicLaurent.lean) — KEEP-USED-AT LevelThree.lean.
77. **`rightCosetRoot_injective`, `precompAlgEquiv_rightCosetRoot`** (UpperHalfPlaneFunctionField.lean) — KEEP-USED-AT Irreducibility.lean; **`algebraMap_ratFunc`** (:118) — KEEP-INTENTIONAL (`@[simp]` rfl-lemma unfolding the `Algebra (RatFunc ℂ) FunctionField` instance — standard practice).
78. **`toCoxMatrix_inclusionMatrix`** (Classification.lean:95), **`CoxMatrix.toCyclicSublattice_carrier`** (:215), **`map_carrier`** (CyclicSublattice.lean:192), **`ofLatticeEq_carrier`** (:203) — KEEP-INTENTIONAL — public `@[simp]` rfl-API on live definitions; may fire invisibly.
79. **Algebra.lean's flagged five** (`laurentqExpansion_neg/_finset_sum/_finset_prod/_nat_mul_coeff/_nat_mul_coeff_of_not_dvd`) — KEEP-USED-AT IntegralDescent/DiagonalLaurent/Kronecker (all five have cross-file call sites).
80. **LaurentQExpansion.lean's flagged sum/prod/nat_mul family** (`meromorphicAt_cuspFunction_finset_sum/_finset_prod/_nat_mul/_of_nat_mul`, `poleOrder_nat_mul`) — KEEP-USED-AT AnalyticSupport/Interpolation/IntegralDescent/Construction/ModularFunction/DiagonalLaurent/Algebra; **`laurentqExpansion.eq_qExpansion_iff`** — KEEP-USED-AT Algebra.lean (×3).
81. **`E4_pow_three_isIntegralPowerSeries`, `ramanujanTau`, `IsIntegralPowerSeriesmod`, `hasCoeffsIn_mul`** — KEEP-USED-AT jfunction/qexp_coeffs/link/Deltaqexpansions.
82. **`j_modularGroup_smul`, `j_eq_qjCoeffs_tsum`, `j_cuspFunction_meromorphicAt`, `j_laurentQExpansion_isIntegral`** (jfunction.lean) — KEEP-USED-AT 6+ Cox files / qexp_coeffs.
83. **`jN_slash_invariant`** (jLevelN.lean:87) — KEEP-USED-AT ModularFunction.lean:475; **`jN_differentiableAt`** — KEEP-USED-AT ModularFunction/ModularFunctionField/Construction/UpperHalfPlaneFunctionField.
84. **`deltaOverQCoeffInt`, `qoverDeltaCoeffInt`** (Qj.lean) — KEEP-USED-AT link.lean (19 and 18 hits); **`Delta_qxp_coeff_link`, `ramanujanTau_link`, `qj_qxp_coeff_link`** (link.lean) — KEEP-USED-AT qexp_coeffs.lean / LevelThree.lean.

## Summary

| Verdict | Count (entries) | Notes |
|---|---|---|
| REMOVE | 25 (entries 1–25; ~34 declarations + 2 files + 1 empty file + hygiene lines) | incl. one sorried lemma (`HasIntegralQExpansion.sum`) |
| INLINE | 1 (entry 26) | |
| REPLACE | 4 (entries 27–30; 2 import fixes, 4 header escapes, 1 TODO) | all need `lake build` verification |
| KEEP-INTENTIONAL | 25 (entries 31–55, 68, 77–78 partial) | terminal theorems, coefficient documentation, simp/API symmetry |
| KEEP-USED | 29 (entries 56–84, covering ~75 declarations) | every one has a named cross-file call site |

### Grep evidence trail

Every REMOVE verdict was grep-verified project-wide (`XYin/**/*.lean`, `XYin.lean`, `ScratchGS.lean`;
`XYin/PhD/Modularforms/` and `.lake` excluded) with word-boundary patterns. Hit counts for REMOVE
declarations (occurrences at definition site / module-docstring mention only):

`hello` 1; `invariantsDetermineLattice` 1; `HasIntegralQExpansion.sum` 1; `IsIntegralPowerSeries.shift` 1;
`IsIntegralPowerSeries_X_pow` 2 (def + entry-6 consumer); `HasIntegralQExpansion_ofPowerSeries` 4 (def + 3 uses
inside the co-removed Delta/E4/E6 theorems); `Delta_hasIntegralQExpansion` 1; `E4_hasIntegralQExpansion` 1;
`E6_hasIntegralQExpansion` 1; `j_hasIntegralQExpansion` 1; `mem_powerSeriesMapSubmodule_iff_coeff` 1;
`powerSeriesMapAlgHom_injective` 1; `mem_modularFormQExpansionSubmodule_iff_coeff` 1;
`modularFormQExpansionLinearMap` 1; `order` 1 (in-file, LQE:666); `cuspFunction_to_analyticAt_meromorphicAt` 1;
`I∞` 1 (declaration line only); `jIntegralLaurentSeries_map_complex` 1; `specializeJMod_varX` 1;
`transformedJSeries_one_sigmaZero_eq_primeLower_pow` 1; `cyclicSublattice_hnf_matrix` 1;
`ratFuncEvalJ_injective` 1; `Delta_qExpansion_coeff_zero_aux` 1; `transportedBasis_apply_coe` 1 (private simp).

False-positive sources controlled for: substring collisions (`card_coxMatrix` vs `one_lt_card_coxMatrix`,
`modularPolynomial_three` vs `..._of_complex_swap`, `hermiteNormalForm` family) via `\b` boundaries;
unicode-subscript names re-checked with `-F`; doc-comment mentions (qexp_coeffs.lean:16–20, jLevelN.lean:19–20)
distinguished from real uses by line inspection; invisible uses caught by hand: instance `gamma0RightCosetsFintype`
(big operators), dot-notation `Submodule.hermiteNormalForm` (CyclicSublattice.lean:57), simp-set firing
(all public `@[simp]` lemmas kept).
