# Cross-set follow-ups (collected from worker reports; assign to the owning worker or the final wave)

## From mf (Modularforms, merged)
- [jq] `qExpansion_tactic/link.lean:250`: inline `qExpansion_ext` as `congrArg (qExpansion 1) h`; then [final] delete `qExpansion_ext` (now in `Modularforms/`).
- [jq] `jFunction/Deltaqexpansions.lean:41-52`: private `E4/E6_qExpansion_coeff_aux` → `congr_fun E4_q_exp n` / `E6_q_exp` (now public in Eisenstein.lean).
- [jq] `Deltaqexpansions.lean:272-275`: use `coe_Delta : ⇑Delta = ModularForm.discriminant` instead of re-deriving it.
- [coxa-followup/final] `Cox/LatticeJ.lean:216,266`: use `coe_Delta`; `LatticeJ.lean:215 Delta_eq_E4_E6` belongs in `Eisenstein.lean` (name clash prevents adding it there now).
- [coxb] `Cox/LevelThree.lean:67` needs `Mathlib.Tactic.NormNum.BigOperators` (a `ring_nf` closing `∑ x : Fin 0, 0`); add the import directly; then [final] drop the re-export from `Eisenstein.lean`.
- [jq + coxb, then final] global `instance : FunLike (ℍ → ℂ) ℍ ℂ` (now in Eisenstein.lean) is still needed by `jfunction.lean:197-201` and `Cox/CoxMatrices/LaurentExpansion.lean:241` (they apply the FunLike-generic `qExpansion_coeff_unique` to plain functions). Give them a local instance / use a non-FunLike lemma, then delete the global instance.
- [deferred naming] root-level `α`/`β`/`negI`, `ModularGroup.modular_negI_*`, `Filter.eventually_atImInfty` → `UpperHalfPlane.eventually_atImInfty`, `E₂_*` names now about mathlib's `E2`.

## From coxa (Cox HNF / lattices / CoxMatrices, merged)
- [coxc] `SingularModuli.lean:155–186` → `CoxMatrix.act_eq_smul_of_mul_eq` (~25 lines); `:141` → start from `Matrix.rankTwoContent_fin_two_of`.
- [coxb] `Kronecker.lean:58,67,78`, `CoxMatrices/LaurentExpansion.lean:313,324,339,349` → `CoxMatrix.ext` / `d_dvd` / `div_d` / `coprime_gcd_b`.
- [coxc] `UpperHalfPlaneFunctionField.lean:211` → `CoxMatrix.ext`.
- [coxb] `LevelThree.lean:733–738` → `card_coxMatrix_of_prime`.
- [coxc] `Arithmetic.lean:284` → `levelJ_apply`.
- [jq] `jLevelN.lean:33–38` → host an ℕ-scaling helper (step5 row 74); LevelJ now uses mathlib `posRealAction`.
- [final] `tendsto_atImInfty_coeff_zero` helper (IsCuspForm.lean is deleted — put it in ForMathlib_Cusps/Eisenstein) makes LatticeJ's `E4_tendsto_atImInfty_aux` a one-liner; hoist `Delta_eq_E4_E6` into Eisenstein/Delta.
- [deferred] Dedekind ψ as an ArithmeticFunction (does not shorten the CRT proof; ℕ product formula exposed instead); `rankTwoContent` redefinition (SingularModuli unfolds the Nat.gcd form; equality lemma added); G-22/23/24(ii) generalisations; style renames.

## From lqe (LaurentQExpansion / Algebra / IntegralPowerSeries / uniqueness, merged)
- [coxb] `IntegralDescent.lean:25–59, 181` → `laurentqExpansion_pow/_polynomial_eval`, `meromorphicAt_cuspFunction_polynomial_eval/_neg`, `laurentqExpansion.order_eq_neg_poleOrder`.
- [coxb] `DiagonalLaurent.lean:28–40, 152–185` → same lemmas at width m.
- [coxb] `CoxMatrices/LaurentExpansion.lean:124–131, 143–184` → `eventually_ne_zero_and_norm_lt_one`, `meromorphicOrderAt_comp_const_mul_pow j_cuspFunction_meromorphicAt hη hr`.
- [coxb] `LevelThree.lean:126`, [coxc/final] `AnalyticSupport.lean:48`, [final] `LevelJ.lean:291` → the new lemmas.
- [coxc/final] `CuspData.lean:86–95, 115–134` → `cuspFunction_comp₂/comp_eventuallyEq`, `MeromorphicAt.polynomial_eval`.
- [coxc/final] `Cox/ModularFunction.lean:63–73` → `cuspFunction_comp₂_eventuallyEq h (fun x y ↦ x - a*y^m)`; `:132–144` → `(poleOrder_lt_iff hm).2`.
- [mfn/final] `ModularFunctions/Congruence.lean:36–48` private `ModularFunction.periodic_comp_ofComplex_of_vadd` → delete, use root `periodic_comp_ofComplex_of_vadd`.
- [jq] `jfunction.lean:208–211, 226, 321 (publicise as qjCoeffs_cast), 337–349 (qj_periodic), 440–451, 478–502`; `Deltaqexpansions.lean:80, 107–111, 246–255`; `jLevelN.lean:103–114, 144, 177–181`; `qexp_coeffs.lean:46–51, 138–141`; `link.lean:156–166, 200–206, 226–230, 234–239`; `XYinTest/Tactic2/LaurentQExpSimpTests` → the `coeff_*'` lemmas. (Replacements verified in scratch by lqe: see report-lqe.md §6.)
- Note: `@[simp]` deliberately NOT put on `cuspFunction_const` (broke AnalyticSupport:53) nor on `coeff_toIntegralPowerSeries_cast`/`coeff_toHasCoeffsInPowerSeries` (broke jfunction:210).
- [deferred] `laurentqExpansion.*` namespace / `to_qExpansion` renames; `poleOrder_add_le/_mul_le`; the `substMonomial` bridge; `PowerSeries.lifts`; generalised `IsIntegralPowerSeriesmod`.

## From coxc (Cox modular polynomial / function fields, merged)
- [final: Laurent API] CuspData private `meromorphicAt_polynomial_eval` + 3rd component of `CuspData.polynomialIn` → `MeromorphicAt.polynomial_eval` / `meromorphicAt_cuspFunction_polynomial_eval`.
- [final: Laurent API] Cox/ModularFunction `cuspFunction_sub_const_mul_pow_eventuallyEq` → `cuspFunction_comp₂_eventuallyEq`; `cuspData_sub_const_mul_pow` → `meromorphicAt_cuspFunction_sub/const_mul/pow`; `poleOrder_lt_of_neg_lt_…` → `poleOrder_lt_iff`.
- [final: Laurent API] AnalyticSupport `cuspMeromorphicSubring.neg_mem'` → `meromorphicAt_cuspFunction_neg`.
- [coxb] IntegralDescent :31–52 → `laurentqExpansion_polynomial_eval`; :177–183 → `(cuspMeromorphicSubring _).neg_mem (coxRoot_cuspMeromorphicAt m σ)`; `.2.2 1` at :33, :47 → `.meromorphicAt_cuspFunction_one`; :240–243 → `(coxPhiFunction_coeff_cuspData m n).periodic`. DiagonalLaurent `.2.2 1` at :30, :161, :179.
- [final: MFn API] Construction `coxPhiFunction_coeff_modularFunction` → `ofSL2ZHolomorphic`; MFF `toMeromorphicField_eq_div_of` germ proof → `MeromorphicField.ofMeromorphic_eq_of_eventuallyEq`/`ofMeromorphic_mul`; `Cox.…holomorphicFunction_ext` → `HolomorphicFunction.ext`; `Cox.slash_zero_eq_comp/iff` → mfn's `SL_slash_zero_eq(_iff)`; `ModularFunction.j_mdifferentiable` now unused.
- [final] CoxMatrices/Basic.lean:530 → `hf.apply_smul`; Classification.lean:185–186 → `modularPolynomialC_eval_eq_zero_iff`.
- [coxb/final] LevelThree:753–757 needs `modularPolynomial_map_complex_swap` (lives in Arithmetic, downstream) → move it to IntegralDescent; LevelThree:742/750 and Kronecker:504/522 `simp only [BivariatePolynomial.map]` → `coe_mapRingHom`/`map_neg`/`map_sub`; move `import FormalCoxProduct` from Construction:7 to IntegralDescent; IntegralDescent:265 lemma belongs in Construction; UHPFF `transformed_*` → public `transformedJSeries_injective` in LaurentExpansion.
- [deferred] G-13/14 `𝕜 → E`, G-30, G-9, G-10, `CuspData` as a structure, naming items.

## From mfn (ModularFunctions, merged) — exact code in report-mfn.md §6 (first three compiled in mfn's sandbox)
- [final] `ModularFunctionField.lean:56–86` (`toMeromorphicField_eq_div_of`, germ internals) → 31→13 lines with `ofMeromorphic_*` / `ofMeromorphic_eq_iff`.
- [final] `Construction.lean:261–277` → `ModularFunction.ofLevelOneHolomorphic`; `LevelJ.lean:313–319` → `ofGamma0Holomorphic`; `ModularFunctionField.lean:162–169`, `UHPFF:48–52` → the `toMeromorphicField_of…Holomorphic` lemmas.
- [final] `AnalyticSupport`/`CuspData` `periodic_comp_of_slashInvariant_one` ≡ `periodic_comp_ofComplex_of_slashInvariant`.
- [final] UHPFF:36–41 `constant` → `algebraMap ℂ HolomorphicFunction`; UHPFF:118–125, :252–261 → `precomp_algebraMap_eq_of_forall`.
- [final] `HolomorphicFunction.ext` (now `@[ext]`) at UHPFF:122, :259, Arithmetic:65, Interpolation:457, Irreducibility:35 (and replace coxc's `Cox.…holomorphicFunction_ext`).
- [final] `sl2_det_pos` at Cox ModularFunction.lean:410, Construction:217, Interpolation:84.
- [final] `ModularForm.SL_slash_zero_eq(_iff)` at Cox ModularFunction:87/350, CuspData:108/147, Interpolation:258/286, Construction:206, LatticeJ:585 (and replace coxc's `Cox.slash_zero_eq_comp/iff`).
- [final] Congruence private `ModularFunction.periodic_comp_ofComplex_of_vadd` → root `periodic_comp_ofComplex_of_vadd` (LaurentQExpansion).
- [final, headline-level new result] state Thm 11.9(ii) as a subfield statement using `ModularFunction.range_toMeromorphicField` / `subfield (Gamma0 N)` (additive corollary; keep `theorem_11_9_ii`).
- [deferred] SL₂ MulAction for `precomp` (right action → needs ᵐᵒᵖ); `IsMeromorphicAt.infty_iff`; `meromorphic'` → NF predicate; naming anonymous instances.

## From coxb (Kronecker / LevelThree / Laurent evaluation cluster, merged)
- [final-B] UHPFF `transformed_leading` (≈:140–147) = new `transformedJSeries_coeff_neg_sq`; UHPFF ≈:152, :186 → `zeta_ne_zero`; then drop the redundant `-(a²) ≤ k` clause from `transformedJSeries_coeff` (blocked only by UHPFF ≈:143–147, :163).
- [final-B] `modularPolynomialC_coeff_polynomialIn` (IntegralDescent ≈:134) belongs beside `modularPolynomialC_specializeY` in Construction (Construction's aux lemma is private).
- [final-B] Eisenstein: the global FunLike instance and the `NormNum.BigOperators` re-export are no longer needed by coxb's files; only `jfunction.lean` still needs the instance (jq).
- [final-B / jq] LevelThree jets duplicate `qExpansion_tactic/Qj.lean` (merge only if no perf loss).
- [deferred] `substMonomial` bridge (no net deletion; design in report-coxb.md); `coxPhiFunction_coeff_laurentqExpansion_widthM` (38 lines) would collapse with a `laurentqExpansionRingHom` (refuted as a bundled hom by step5); G-26; style renames.
- [final report] PROJECT_OVERVIEW.md still names the deleted series (update the overview at the end).

## From jq (jFunction / qExpansion_tactic / Tactic2 / tests, merged)
- [final-B] `CoxMatrices/LaurentExpansion.lean:30–36`: define `jIntCoeff n := if n < -1 then 0 else qjCoeffs (n+1).toNat` (explicit witness; removes `Classical.choose`); `jIntCoeff_spec := j_laurentQExpansion_coeff n`; `jIntCoeff_neg_one` → `simp [jIntCoeff, qjCoeffs_zero]`; `:284–286` → `j_laurentQExpansion_coeff_of_neg_one_le`; `:191–192` → `qj_apply`.
- [final-B] `Kronecker.lean:149–157` → `if_pos` after the redefinition; `LevelThree.lean:122–130` → `rw [← jIntCoeff_spec, j_laurentQExpansion_coeff_sub_one, ← qjCoeffs_cast, qjCoeffs_eq_qjCoeffInt]` (TIME LevelThree).
- [final-B] `LatticeJ.lean:615` → `qj_apply`; `LevelJ.lean:29–39` `natScaleUpperHalfPlane N` is the same term as jq's `UpperHalfPlane.natScale ↑N` (so `levelJ_apply` is `rfl`); likewise `Arithmetic.lean:199–202`.
- [final-B] `Eisenstein.lean`: delete `qExpansion_ext` (0 users); the global `FunLike (ℍ → ℂ)` instance: jq verified none of its 341 declarations use it; coxb made LaurentExpansion use a local `letI` — try deleting the global instance (and its stale docstring).
- [deferred] `weierstrassCurve_j` via `j_of_isShortNF` refuted (not shorter); G-17; test/`jN` renames; `fun_prop` registration; Γ(1)→𝒮ℒ migration.
