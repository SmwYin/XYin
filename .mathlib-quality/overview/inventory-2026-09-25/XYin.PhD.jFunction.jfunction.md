# Inventory: XYin/PhD/jFunction/jfunction.lean  (504 lines)

Defines the modular invariant `j = E4³/Δ`, its SL₂(ℤ)-invariance, the regularization `qj = q·j`, and proves via `deltaOverQ = Δ/q` (an invertible integral power series) that `qExpansion 1 qj` has integer coefficients `qjCoeffs`, constant term 1, and that `j` has a simple pole at ∞ with integral Laurent coefficients (`j_poleOrder`, `j_laurentQExpansion_isIntegral`). This is the analytic source of all "integer coefficients of j" facts used by the Cox development.

## Declarations

### `local notation "𝕢"`
- **Type**: notation for `Periodic.qParam`
- **What**: q-parameter notation. **How**: `local notation`. **Hypotheses**: none. **Uses from project**: []. **Used by**: Delta_hasSum_aux, Delta_shift_hasSum_aux, …
- **Visibility**: local. **Lines**: 39. **Notes**: mathlib uses the same local notation (QExpansion.lean).

### `private lemma cuspFunction_apply_zero_of_tendsto`
- **Type**: `{f : ℍ → ℂ} {a : ℂ} (hf : Tendsto f atImInfty (nhds a)) : cuspFunction 1 f 0 = a`
- **What**: If f has a limit a at i∞ then its cusp function takes the value a at q = 0.
- **How**: `cuspFunction 1 f 0 = limUnder (𝓝[≠] 0) (f ∘ ofComplex ∘ invQParam 1)`; compose `hf` with mathlib `tendsto_comap_im_ofComplex` (UpperHalfPlane/FunctionsBoundedAtInfty.lean:78) and `Periodic.invQParam_tendsto` (Analysis/Complex/Periodic.lean:104), then `Tendsto.limUnder_eq`.
- **Hypotheses**: f → a along `atImInfty`.
- **Uses from project**: []
- **Used by**: cuspFunction_deltaShiftedQSeries_zero_aux, integralDeltaOverQ_constantCoeff_isUnit_aux, cuspFunction_deltaOverQ_zero_aux, cuspFunction_qOverDelta_zero_aux
- **Visibility**: private
- **Lines**: 43–48, body 5 lines
- **Notes**: Generally useful (any h>0); mathlib only has `UpperHalfPlane.cuspFunction_apply_zero` (QExpansion.lean:107, needs analyticity+periodicity, gives `valueAtInfty f`) and `Periodic.cuspFunction_zero_eq_limUnder_nhds_ne` (Periodic.lean:123). Candidate for upstream / project ForMathlib.

### `def j`
- **Type**: `ℍ → ℂ` (:= `fun τ ↦ (E4 τ) ^ 3 / Delta τ`)
- **What**: The classical modular invariant j(τ) = E₄(τ)³/Δ(τ).
- **How**: definition.
- **Hypotheses**: none
- **Uses from project**: [E4 (Deltaqexpansions.lean:36), Delta (Modularforms/Delta.lean:170)]
- **Used by**: j_mdifferentiable, j_slash_invariant, qj, E4_pow_three_mul_qOverDelta_eq_qj, qj_vadd_one_aux, qj_div_qParam_eq_j_aux, j_eq_qjCoeffs_tsum, inv_mul_cuspFunction_qj_eq_j_aux, j_cuspFunction_meromorphicAt, j_poleOrder, j_cuspFunction_not_analyticAt, j_poleRemoved, j_to_qExpansion, j_laurentQExpansion_*
- **Visibility**: public
- **Lines**: 51
- **Notes**: No mathlib j-function (searched `jInvariant|j-invariant|modular invariant` in Mathlib/NumberTheory: none; `WeierstrassCurve.j` is algebraic). Root-level single-letter name `j` collides with bound variables project-wide (509 raw grep hits).

### `lemma j_mdifferentiable`
- **Type**: `MDiff j`
- **What**: j is holomorphic on ℍ.
- **How**: quotient of the holomorphic forms E4³ and Δ with `Δ_ne_zero`; `MDifferentiable.div`, `ModularFormClass.holo`.
- **Hypotheses**: none
- **Uses from project**: [j, E4, Delta, Δ_ne_zero (Delta.lean:44)]
- **Used by**: qj_differentiableAt_of_im_pos
- **Visibility**: public
- **Lines**: 54–57, body 3 lines
- **Notes**: re-exported as `ModularFunction.j_mdifferentiable` (ModularFunctions/JInvariant.lean:24). 9 external uses.

### `lemma j_slash_invariant`
- **Type**: `(γ : SL(2, ℤ)) : j ∣[(0 : ℤ)] γ = j`
- **What**: j is a weight-0 modular function for SL₂(ℤ).
- **How**: j = f/Δ with f = E4·E4·E4 of weight 12; mathlib `div_slash_SL2` (SlashActions.lean:215) with weights 12−12; `slash_action_eq'` for f and Delta via `CongruenceSubgroup.mem_Gamma_one`.
- **Hypotheses**: none
- **Uses from project**: [j, E4, Delta]
- **Used by**: j_modularGroup_smul
- **Visibility**: public
- **Lines**: 60–73, body 13 lines
- **Notes**: 3 external uses (JInvariant.lean bundles `jModularFunction`).

### `lemma j_modularGroup_smul`
- **Type**: `(γ : SL(2, ℤ)) (z : ℍ) : j (γ • z) = j z`
- **What**: Pointwise SL₂(ℤ)-invariance.
- **How**: evaluate j_slash_invariant at z; `SL_slash_apply` with weight 0.
- **Hypotheses**: none
- **Uses from project**: [j, j_slash_invariant]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 76–78
- **Notes**: 7 external uses (jLevelN.lean:90, Cox/ModularFunction.lean:404, …).

### `def deltaOverQ`
- **Type**: `ℍ → ℂ` (:= `fun z ↦ ∏' n : ℕ, (1 - cexp (2πi (n+1) z)) ^ 24`)
- **What**: Δ/q as the Euler product ∏(1−qⁿ)²⁴.
- **How**: definition.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: deltaOverQ_eq_qParam_inv_mul_Delta, deltaOverQ_eq_qParam_inv_smul_Delta, deltaOverQ_ne_zero, deltaOverQ_tendsto_atImInfty, deltaShiftedQSeries_eq_deltaOverQ, cuspFunction_deltaShiftedQSeries_zero_aux, deltaOverQ_isIntegralPowerSeries, coeTo_integralDeltaOverQ, qOverDelta, deltaOverQ_analyticAt_aux, cuspFunction_deltaOverQ_zero_aux, cuspFunction_qOverDelta_eq_inv_aux, deltaOverQ_inv_analyticAt_aux, integralDeltaOverQ_mul_qExpansion_qOverDelta
- **Visibility**: public
- **Lines**: 81–82
- **Notes**: mathlib expresses the same product as `∏' n, (1 - eta_q n τ)^24` (Discriminant.lean, `discriminant_eq_q_prod`). 5 external uses (link.lean).

### `lemma deltaOverQ_eq_qParam_inv_mul_Delta`
- **Type**: `deltaOverQ = (fun z ↦ 1 / cexp (2πi z)) * Delta`
- **What**: deltaOverQ is Δ divided by q.
- **How**: unfold `Delta_apply`, `Δ` (product formula) and cancel.
- **Hypotheses**: none
- **Uses from project**: [deltaOverQ, Delta, Delta_apply (Delta.lean:191), Δ (Delta.lean:26)]
- **Used by**: deltaOverQ_eq_qParam_inv_smul_Delta, E4_pow_three_mul_qOverDelta_eq_qj
- **Visibility**: public
- **Lines**: 85–88
- **Notes**: —

### `private lemma deltaOverQ_eq_qParam_inv_smul_Delta`
- **Type**: `(z : ℍ) : deltaOverQ z = (𝕢 1 (z : ℂ))⁻¹ • Delta z`
- **What**: Pointwise version in `qParam` notation.
- **How**: `congrFun` of the previous lemma, `simp [Periodic.qParam]`.
- **Hypotheses**: none
- **Uses from project**: [deltaOverQ, Delta, deltaOverQ_eq_qParam_inv_mul_Delta]
- **Used by**: deltaOverQ_ne_zero, deltaShiftedQSeries_eq_deltaOverQ, deltaShiftedQSeries_hasSum_aux
- **Visibility**: private
- **Lines**: 90–93
- **Notes**: two formulations (`1 / cexp` vs `(𝕢 1 z)⁻¹ •`) of one fact.

### `lemma deltaOverQ_ne_zero`
- **Type**: `(z : ℍ) : deltaOverQ z ≠ 0`
- **What**: The Euler product never vanishes on ℍ.
- **How**: q⁻¹ ≠ 0 and `Δ_ne_zero`.
- **Hypotheses**: none
- **Uses from project**: [deltaOverQ, deltaOverQ_eq_qParam_inv_smul_Delta, Δ_ne_zero, Delta]
- **Used by**: integralDeltaOverQ_mul_qExpansion_qOverDelta
- **Visibility**: public
- **Lines**: 96–98
- **Notes**: 0 external uses.

### `lemma deltaOverQ_tendsto_atImInfty`
- **Type**: `Tendsto deltaOverQ atImInfty (nhds (1 : ℂ))`
- **What**: Δ/q → 1 at i∞.
- **How**: `simpa [deltaOverQ] using Delta_boundedfactor` (Delta.lean:151), itself mathlib `ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow`.
- **Hypotheses**: none
- **Uses from project**: [deltaOverQ, Delta_boundedfactor (Delta.lean:151)]
- **Used by**: integralDeltaOverQ_constantCoeff_isUnit_aux, qOverDelta_tendsto_atImInfty, cuspFunction_deltaOverQ_zero_aux
- **Visibility**: public
- **Lines**: 101–102
- **Notes**: —

### `def deltaShiftedQSeries`
- **Type**: `ℍ → ℂ` (:= `fun z ↦ ∑' n, (qExpansion 1 Delta).coeff (n+1) * cexp(2πi z)^n`)
- **What**: The q-series of Δ with the vanishing constant term stripped and divided by q.
- **How**: definition.
- **Hypotheses**: none
- **Uses from project**: [Delta]
- **Used by**: deltaShiftedQSeries_eq_deltaOverQ, deltaShiftedQSeries_hasSum_aux, cuspFunction_deltaShiftedQSeries_hasSum_aux, cuspFunction_deltaShiftedQSeries_zero_aux, deltaShiftedQSeries_analyticAt_aux, deltaShiftedQSeries_qExpansion_coeff, deltaOverQ_isIntegralPowerSeries, deltaOverQ_analyticAt_aux
- **Visibility**: public
- **Lines**: 105–106
- **Notes**: exists only to prove analyticity of `cuspFunction 1 deltaOverQ` (see 167). 2 external uses (link.lean:249–250).

### `private lemma Delta_qExpansion_coeff_zero_aux`
- **Type**: `(qExpansion 1 Delta).coeff 0 = 0`
- **What**: Δ is a cusp form: τ(0) = 0.
- **How**: `qExpansion_coeff` + mathlib `CuspFormClass.cuspFunction_apply_zero` (QExpansion.lean:402).
- **Hypotheses**: none
- **Uses from project**: [Delta]
- **Used by**: Delta_shift_hasSum_aux
- **Visibility**: private
- **Lines**: 108–110
- **Notes**: mathlib `CuspFormClass.qExpansion_coeff_zero` (`QExpansion.lean:408`) is this statement verbatim.

### `private lemma Delta_hasSum_aux`
- **Type**: `(z : ℍ) : HasSum (fun m ↦ (qExpansion 1 Delta).coeff m • 𝕢 1 z ^ m) (Delta z)`
- **What**: The q-expansion of Δ converges to Δ.
- **How**: mathlib `UpperHalfPlane.hasSum_qExpansion` (QExpansion.lean:189) with periodicity `SlashInvariantFormClass.periodic_comp_ofComplex`, `holo`, `bdd_at_infty`.
- **Hypotheses**: none
- **Uses from project**: [Delta]
- **Used by**: Delta_shift_hasSum_aux
- **Visibility**: private
- **Lines**: 112–116
- **Notes**: —

### `private lemma Delta_shift_hasSum_aux`
- **Type**: `(z : ℍ) : HasSum (fun m ↦ (qExpansion 1 Delta).coeff (m+1) • 𝕢 1 z ^ m) ((𝕢 1 z)⁻¹ • Delta z)`
- **What**: The shifted series converges to Δ/q.
- **How**: `hasSum_nat_add_iff' 1` drops the zero term (Delta_qExpansion_coeff_zero_aux), then `HasSum.const_smul` by q⁻¹ and `pow_succ`.
- **Hypotheses**: none
- **Uses from project**: [Delta, Delta_hasSum_aux, Delta_qExpansion_coeff_zero_aux]
- **Used by**: deltaShiftedQSeries_eq_deltaOverQ, deltaShiftedQSeries_hasSum_aux
- **Visibility**: private
- **Lines**: 118–129, body 11 lines
- **Notes**: —

### `lemma deltaShiftedQSeries_eq_deltaOverQ`
- **Type**: `deltaShiftedQSeries = deltaOverQ`
- **What**: The shifted q-series equals the Euler product.
- **How**: both equal q⁻¹·Δ: `Delta_shift_hasSum_aux.tsum_eq` and deltaOverQ_eq_qParam_inv_smul_Delta.
- **Hypotheses**: none
- **Uses from project**: [deltaShiftedQSeries, deltaOverQ, deltaOverQ_eq_qParam_inv_smul_Delta, Delta_shift_hasSum_aux]
- **Used by**: deltaShiftedQSeries_hasSum_aux, cuspFunction_deltaShiftedQSeries_zero_aux, deltaOverQ_isIntegralPowerSeries, deltaOverQ_analyticAt_aux
- **Visibility**: public
- **Lines**: 132–135
- **Notes**: 1 external use (link.lean:250).

### `private lemma deltaShiftedQSeries_hasSum_aux`
- **Type**: `(z : ℍ) : HasSum (fun m ↦ (qExpansion 1 Delta).coeff (m+1) • 𝕢 1 z ^ m) (deltaShiftedQSeries z)`
- **What**: Convergence of the defining series of deltaShiftedQSeries.
- **How**: rewrite to deltaOverQ and use Delta_shift_hasSum_aux.
- **Hypotheses**: none
- **Uses from project**: [deltaShiftedQSeries, Delta, deltaShiftedQSeries_eq_deltaOverQ, deltaOverQ_eq_qParam_inv_smul_Delta, Delta_shift_hasSum_aux]
- **Used by**: cuspFunction_deltaShiftedQSeries_hasSum_aux, deltaShiftedQSeries_qExpansion_coeff
- **Visibility**: private
- **Lines**: 137–141
- **Notes**: —

### `private lemma cuspFunction_deltaShiftedQSeries_hasSum_aux`
- **Type**: `∀ {q : ℂ}, ‖q‖ < 1 → q ≠ 0 → HasSum (fun n ↦ (qExpansion 1 Delta).coeff (n+1) • q ^ n) (cuspFunction 1 deltaShiftedQSeries q)`
- **What**: The series converges to the cusp function on the punctured unit disc.
- **How**: q = 𝕢 1 τ with τ = invQParam 1 q (mathlib `Periodic.qParam_right_inv`, `im_invQParam_pos_of_norm_lt_one`), `Periodic.cuspFunction_eq_of_nonzero` (Periodic.lean:119), `ofComplex_apply_of_im_pos`; transport deltaShiftedQSeries_hasSum_aux.
- **Hypotheses**: 0 < |q| < 1.
- **Uses from project**: [deltaShiftedQSeries, Delta, deltaShiftedQSeries_hasSum_aux]
- **Used by**: deltaShiftedQSeries_analyticAt_aux
- **Visibility**: private
- **Lines**: 143–159, body 13 lines
- **Notes**: the "cusp function at nonzero q = f(invQParam q)" gadget (152–158) is repeated in jLevelN.lean:151–154 and LaurentQExpansion.lean:330ff.

### `private lemma cuspFunction_deltaShiftedQSeries_zero_aux`
- **Type**: `cuspFunction 1 deltaShiftedQSeries 0 = 1`
- **What**: Value 1 at the cusp.
- **How**: cuspFunction_apply_zero_of_tendsto + Delta_boundedfactor after rewriting to deltaOverQ.
- **Hypotheses**: none
- **Uses from project**: [deltaShiftedQSeries, cuspFunction_apply_zero_of_tendsto, deltaShiftedQSeries_eq_deltaOverQ, deltaOverQ, Delta_boundedfactor]
- **Used by**: deltaShiftedQSeries_analyticAt_aux
- **Visibility**: private
- **Lines**: 161–165
- **Notes**: duplicate of cuspFunction_deltaOverQ_zero_aux (256) modulo the equality of functions.

### `private lemma deltaShiftedQSeries_analyticAt_aux`
- **Type**: `AnalyticAt ℂ (cuspFunction 1 deltaShiftedQSeries) 0`
- **What**: The cusp function of Δ/q is analytic at 0 (so Δ/q has a genuine q-expansion).
- **How**: Builds `HasFPowerSeriesOnBall (update F 0 (c 0)) (.ofScalars ℂ c) 0 1` by hand: radius ≥ 1 through `FormalMultilinearSeries.le_radius_of_summable` from summability of the series for |q|<1, pointwise `HasSum` from cuspFunction_deltaShiftedQSeries_hasSum_aux; identifies `c 0 = τ(1) = 1 = F 0` via `Delta_q_one_term` and the zero lemma, removes the `update` with `update_eq_self_iff`, then `.analyticAt`.
- **Hypotheses**: none
- **Uses from project**: [deltaShiftedQSeries, Delta, cuspFunction_deltaShiftedQSeries_hasSum_aux, cuspFunction_deltaShiftedQSeries_zero_aux, Delta_q_one_term (Eisenstein.lean:374)]
- **Used by**: deltaShiftedQSeries_qExpansion_coeff, deltaOverQ_analyticAt_aux
- **Visibility**: private
- **Lines**: 167–195, body 28 lines
- **Notes**: Lines 174–190 are a verbatim re-derivation of mathlib's *private* `UpperHalfPlane.hasFPowerSeriesOnBall_update` (`QExpansion.lean:239–241`, hypothesis `∀ τ, HasSum (c m • 𝕢 h τ ^ m) (f τ)`). Since it is private, the copy is forced; upstreaming it as public would delete 143–195 (≈50 lines) leaving `hasFPowerSeriesOnBall_update one_pos deltaShiftedQSeries_hasSum_aux` + value at 0.

### `lemma deltaShiftedQSeries_qExpansion_coeff`
- **Type**: `(n : ℕ) : (qExpansion 1 deltaShiftedQSeries).coeff n = (qExpansion 1 Delta).coeff (n + 1)`
- **What**: The q-expansion of Δ/q is the shift of that of Δ: coefficients τ(n+1).
- **How**: mathlib `UpperHalfPlane.qExpansion_coeff_unique` (QExpansion.lean:691) with the analyticity and HasSum lemmas.
- **Hypotheses**: none
- **Uses from project**: [deltaShiftedQSeries, Delta, deltaShiftedQSeries_analyticAt_aux, deltaShiftedQSeries_hasSum_aux]
- **Used by**: deltaOverQ_isIntegralPowerSeries
- **Visibility**: public
- **Lines**: 198–201
- **Notes**: 1 external use (link.lean).

### `lemma deltaOverQ_isIntegralPowerSeries`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 deltaOverQ)`
- **What**: Δ/q has integer q-expansion coefficients (τ(n+1)).
- **How**: witness `integralDelta.coeff (n+1)`; the cast identity from `coeTo_of_toIntegralPowerSeries Delta_isIntegralPowerSeries` and the shift lemma.
- **Hypotheses**: none
- **Uses from project**: [IsIntegralPowerSeries, int_iff, integralDelta (Deltaqexpansions.lean:295), deltaOverQ, deltaShiftedQSeries_eq_deltaOverQ, deltaShiftedQSeries_qExpansion_coeff, coeTo_of_toIntegralPowerSeries, Delta_isIntegralPowerSeries]
- **Used by**: integralDeltaOverQ, coeTo_integralDeltaOverQ
- **Visibility**: public
- **Lines**: 205–211, body 5 lines
- **Notes**: lines 210–211 are the cast-coefficient pattern again.

### `def integralDeltaOverQ`
- **Type**: `PowerSeries ℤ` (:= `toIntegralPowerSeries deltaOverQ_isIntegralPowerSeries`)
- **What**: The ℤ-lift of the q-expansion of Δ/q.
- **How**: choice via toIntegralPowerSeries.
- **Hypotheses**: none
- **Uses from project**: [toIntegralPowerSeries, deltaOverQ_isIntegralPowerSeries]
- **Used by**: coeTo_integralDeltaOverQ, integralDeltaOverQ_constantCoeff_isUnit_aux, integralDeltaOverQ_isUnit_aux, integralDeltaOverQ_mul_qExpansion_qOverDelta, qOverDelta_isIntegralPowerSeries_aux
- **Visibility**: public
- **Lines**: 214
- **Notes**: never characterized coefficientwise (`integralDeltaOverQ.coeff n = ramanujanTau (n+1)` is provable from 208 but unstated). Computable twin `deltaOverQCoeffInt` (Qj.lean:117). 0 external uses.

### `lemma coeTo_integralDeltaOverQ`
- **Type**: `(coeToComplexPowerSeries.ringHom ℤ) integralDeltaOverQ = qExpansion 1 deltaOverQ`
- **What**: Complexification recovers the q-expansion.
- **How**: `coeTo_of_toIntegralPowerSeries`.
- **Hypotheses**: none
- **Uses from project**: [coeToComplexPowerSeries.ringHom, integralDeltaOverQ, deltaOverQ, coeTo_of_toIntegralPowerSeries, deltaOverQ_isIntegralPowerSeries]
- **Used by**: integralDeltaOverQ_constantCoeff_isUnit_aux, integralDeltaOverQ_mul_qExpansion_qOverDelta
- **Visibility**: public
- **Lines**: 217–219
- **Notes**: 1 external use (link.lean).

### `private lemma integralDeltaOverQ_constantCoeff_isUnit_aux`
- **Type**: `IsUnit (constantCoeff integralDeltaOverQ : ℤ)`
- **What**: The constant term of the integral Δ/q is 1, a unit.
- **How**: `(qExpansion 1 deltaOverQ).coeff 0 = cuspFunction 1 deltaOverQ 0 = 1` (cuspFunction_apply_zero_of_tendsto + deltaOverQ_tendsto_atImInfty), pulled back through the cast.
- **Hypotheses**: none
- **Uses from project**: [integralDeltaOverQ, deltaOverQ, cuspFunction_apply_zero_of_tendsto, deltaOverQ_tendsto_atImInfty, coeTo_integralDeltaOverQ, coeToComplexPowerSeries.ringHom]
- **Used by**: integralDeltaOverQ_isUnit_aux
- **Visibility**: private
- **Lines**: 221–229, body 8 lines
- **Notes**: `hcoeff0C` duplicates cuspFunction_deltaOverQ_zero_aux (256).

### `private lemma integralDeltaOverQ_isUnit_aux`
- **Type**: `IsUnit integralDeltaOverQ`
- **What**: Δ/q is a unit in ℤ⟦q⟧.
- **How**: mathlib `PowerSeries.isUnit_iff_constantCoeff` (RingTheory/PowerSeries/Inverse.lean:111).
- **Hypotheses**: none
- **Uses from project**: [integralDeltaOverQ, integralDeltaOverQ_constantCoeff_isUnit_aux]
- **Used by**: qOverDelta_isIntegralPowerSeries_aux
- **Visibility**: private
- **Lines**: 231–233
- **Notes**: —

### `def qOverDelta`
- **Type**: `ℍ → ℂ` (:= `fun z ↦ 1 / deltaOverQ z`)
- **What**: q/Δ, the reciprocal Euler product.
- **How**: definition.
- **Hypotheses**: none
- **Uses from project**: [deltaOverQ]
- **Used by**: E4_pow_three_mul_qOverDelta_eq_qj, qOverDelta_tendsto_atImInfty, cuspFunction_qOverDelta_zero_aux, cuspFunction_qOverDelta_eq_inv_aux, qOverDelta_cuspFunction_analyticAt, integralDeltaOverQ_mul_qExpansion_qOverDelta, qOverDelta_isIntegralPowerSeries_aux, qj_isIntegralPowerSeries_aux, qj_isBoundedAtImInfty, qj_qExpansion_coeff_zero
- **Visibility**: public
- **Lines**: 236
- **Notes**: `1 / _` rather than `_⁻¹` forces `one_div` rewrites (254, 267, 297). 1 external use (link.lean:362).

### `def qj`
- **Type**: `ℍ → ℂ` (:= `(fun z ↦ cexp (2πi z)) * j`)
- **What**: q·j, the holomorphic-at-∞ regularization of j.
- **How**: definition.
- **Hypotheses**: none
- **Uses from project**: [j]
- **Used by**: E4_pow_three_mul_qOverDelta_eq_qj, qj_isIntegralPowerSeries, qjCoeffs, qj_coeff_cast_aux, qj_vadd_one_aux, qj_periodic, qj_differentiableAt_of_im_pos, qj_mdifferentiable, qj_isBoundedAtImInfty, hasSum_qExpansion_qj, qjCoeffs_hasSum_aux, qj_eq_tsum_aux, qj_div_qParam_eq_j_aux, qj_qExpansion_coeff_zero, qj_cuspFunction_differentiableOn_aux, qj_cuspFunction_analyticAt, inv_mul_cuspFunction_qj_eq_j_aux, j_poleOrder, j_poleRemoved, j_to_qExpansion
- **Visibility**: public
- **Lines**: 239
- **Notes**: uses raw `cexp` instead of `𝕢 1 z`; every later lemma unfolds `Periodic.qParam` (387, 450, 480). 40 external uses.

### `lemma E4_pow_three_mul_qOverDelta_eq_qj`
- **Type**: `E4 ^ 3 * qOverDelta = qj`
- **What**: The factorization q·j = E₄³ · (q/Δ).
- **How**: unfold, `deltaOverQ_eq_qParam_inv_mul_Delta`, `ring`.
- **Hypotheses**: none
- **Uses from project**: [E4, qOverDelta, deltaOverQ_eq_qParam_inv_mul_Delta, qj, j, Delta]
- **Used by**: qj_isIntegralPowerSeries, qj_isBoundedAtImInfty, qj_qExpansion_coeff_zero
- **Visibility**: public
- **Lines**: 242–246
- **Notes**: 2 external uses (link.lean).

### `private lemma deltaOverQ_analyticAt_aux`
- **Type**: `AnalyticAt ℂ (cuspFunction 1 deltaOverQ) 0`
- **What**: Cusp function of Δ/q analytic at 0.
- **How**: transfer from deltaShiftedQSeries.
- **Hypotheses**: none
- **Uses from project**: [deltaOverQ, deltaShiftedQSeries_eq_deltaOverQ, deltaShiftedQSeries_analyticAt_aux]
- **Used by**: deltaOverQ_inv_analyticAt_aux, integralDeltaOverQ_mul_qExpansion_qOverDelta
- **Visibility**: private
- **Lines**: 248–249
- **Notes**: —

### `lemma qOverDelta_tendsto_atImInfty`
- **Type**: `Tendsto qOverDelta atImInfty (nhds (1 : ℂ))`
- **What**: q/Δ → 1 at i∞.
- **How**: `Tendsto.inv₀` of deltaOverQ_tendsto_atImInfty.
- **Hypotheses**: none
- **Uses from project**: [qOverDelta, deltaOverQ, deltaOverQ_tendsto_atImInfty]
- **Used by**: cuspFunction_qOverDelta_zero_aux, qj_isBoundedAtImInfty
- **Visibility**: public
- **Lines**: 252–254
- **Notes**: 1 external use.

### `private lemma cuspFunction_deltaOverQ_zero_aux`
- **Type**: `cuspFunction 1 deltaOverQ 0 = 1`
- **What**: Value of Δ/q at the cusp.
- **How**: cuspFunction_apply_zero_of_tendsto.
- **Hypotheses**: none
- **Uses from project**: [deltaOverQ, cuspFunction_apply_zero_of_tendsto, deltaOverQ_tendsto_atImInfty]
- **Used by**: cuspFunction_qOverDelta_eq_inv_aux, deltaOverQ_inv_analyticAt_aux
- **Visibility**: private
- **Lines**: 256–257
- **Notes**: —

### `private lemma cuspFunction_qOverDelta_zero_aux`
- **Type**: `cuspFunction 1 qOverDelta 0 = 1`
- **What**: Value of q/Δ at the cusp.
- **How**: cuspFunction_apply_zero_of_tendsto.
- **Hypotheses**: none
- **Uses from project**: [qOverDelta, cuspFunction_apply_zero_of_tendsto, qOverDelta_tendsto_atImInfty]
- **Used by**: cuspFunction_qOverDelta_eq_inv_aux, qj_qExpansion_coeff_zero
- **Visibility**: private
- **Lines**: 259–260
- **Notes**: —

### `private lemma cuspFunction_qOverDelta_eq_inv_aux`
- **Type**: `cuspFunction 1 qOverDelta = fun q ↦ (cuspFunction 1 deltaOverQ q)⁻¹`
- **What**: Cusp function of the reciprocal is the reciprocal of the cusp function.
- **How**: q = 0 by the two value lemmas; q ≠ 0 by unfolding `Periodic.cuspFunction` (pointwise inverse).
- **Hypotheses**: none
- **Uses from project**: [qOverDelta, deltaOverQ, cuspFunction_deltaOverQ_zero_aux, cuspFunction_qOverDelta_zero_aux]
- **Used by**: qOverDelta_cuspFunction_analyticAt
- **Visibility**: private
- **Lines**: 262–267
- **Notes**: mathlib has `cuspFunction_smul/neg/add/sub/mul` (QExpansion.lean:440–461) but no `cuspFunction_inv`/`div` — candidate general lemma.

### `private lemma deltaOverQ_inv_analyticAt_aux`
- **Type**: `AnalyticAt ℂ (fun q ↦ (cuspFunction 1 deltaOverQ q)⁻¹) 0`
- **What**: Inverse of an analytic nonvanishing function is analytic.
- **How**: `AnalyticAt.inv` with value 1 ≠ 0.
- **Hypotheses**: none
- **Uses from project**: [deltaOverQ, deltaOverQ_analyticAt_aux, cuspFunction_deltaOverQ_zero_aux]
- **Used by**: qOverDelta_cuspFunction_analyticAt
- **Visibility**: private
- **Lines**: 269–271
- **Notes**: —

### `lemma qOverDelta_cuspFunction_analyticAt`
- **Type**: `AnalyticAt ℂ (cuspFunction 1 qOverDelta) 0`
- **What**: q/Δ has a convergent q-expansion.
- **How**: rewrite by cuspFunction_qOverDelta_eq_inv_aux.
- **Hypotheses**: none
- **Uses from project**: [qOverDelta, cuspFunction_qOverDelta_eq_inv_aux, deltaOverQ_inv_analyticAt_aux]
- **Used by**: integralDeltaOverQ_mul_qExpansion_qOverDelta, qj_isIntegralPowerSeries_aux, qj_qExpansion_coeff_zero
- **Visibility**: public
- **Lines**: 274–275
- **Notes**: 1 external use (link.lean).

### `private lemma E4_pow_three_isModularForm_aux`
- **Type**: `∃ f : ModularForm (Subgroup.map (mapGL ℝ) (Gamma 1)) 12, (f : ℍ → ℂ) = E4 ^ 3`
- **What**: E₄³ is (the coercion of) a weight-12 modular form.
- **How**: witness `E4.mul (E4.mul E4)` + `ModularForm.coe_mul`.
- **Hypotheses**: none
- **Uses from project**: [E4]
- **Used by**: E4_pow_three_cuspFunction_analyticAt
- **Visibility**: private
- **Lines**: 277–282
- **Notes**: unnecessary ∃-wrapper: `E4.pow 3` with `ModularForm.coe_pow` (used in Deltaqexpansions.lean:270) is the witness.

### `lemma E4_pow_three_cuspFunction_analyticAt`
- **Type**: `AnalyticAt ℂ (cuspFunction 1 (E4 ^ 3)) 0`
- **What**: E₄³ has a convergent q-expansion.
- **How**: mathlib `ModularFormClass.analyticAt_cuspFunction_zero` (QExpansion.lean:153) on the witness form.
- **Hypotheses**: none
- **Uses from project**: [E4, E4_pow_three_isModularForm_aux]
- **Used by**: qj_isIntegralPowerSeries_aux, qj_qExpansion_coeff_zero
- **Visibility**: public
- **Lines**: 285–288
- **Notes**: 1 external use (link.lean).

### `lemma integralDeltaOverQ_mul_qExpansion_qOverDelta`
- **Type**: `(coeToComplexPowerSeries.ringHom ℤ) integralDeltaOverQ * qExpansion 1 qOverDelta = 1`
- **What**: The q-expansions of Δ/q and q/Δ are mutually inverse.
- **How**: mathlib `UpperHalfPlane.qExpansion_mul` (QExpansion.lean:466) turns the product into `qExpansion 1 (deltaOverQ * qOverDelta) = qExpansion 1 1`, then `qExpansion_one` (:515); the pointwise product is 1 by deltaOverQ_ne_zero.
- **Hypotheses**: none
- **Uses from project**: [coeToComplexPowerSeries.ringHom, integralDeltaOverQ, qOverDelta, deltaOverQ, coeTo_integralDeltaOverQ, deltaOverQ_analyticAt_aux, qOverDelta_cuspFunction_analyticAt, deltaOverQ_ne_zero]
- **Used by**: qOverDelta_isIntegralPowerSeries_aux
- **Visibility**: public
- **Lines**: 291–298, body 7 lines
- **Notes**: 1 external use (link.lean).

### `private lemma qOverDelta_isIntegralPowerSeries_aux`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 qOverDelta)`
- **What**: q/Δ has integer coefficients (inverse of a unit in ℤ⟦q⟧).
- **How**: `Units.map` of the ring hom sends `u⁻¹` to the inverse; `Units.inv_eq_of_mul_eq_one_right`.
- **Hypotheses**: none
- **Uses from project**: [IsIntegralPowerSeries, qOverDelta, integralDeltaOverQ_isUnit_aux, coeToComplexPowerSeries.ringHom, integralDeltaOverQ_mul_qExpansion_qOverDelta]
- **Used by**: qj_isIntegralPowerSeries_aux
- **Visibility**: private
- **Lines**: 300–306, body 5 lines
- **Notes**: —

### `private lemma qj_isIntegralPowerSeries_aux`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 (E4 ^ 3 * qOverDelta))`
- **What**: Integrality of the product form.
- **How**: `qExpansion_mul` + `hasCoeffsIn_mul` (IntegralPowerSeries.lean:84) with E4_pow_three_isIntegralPowerSeries.
- **Hypotheses**: none
- **Uses from project**: [IsIntegralPowerSeries, E4, qOverDelta, E4_pow_three_cuspFunction_analyticAt, qOverDelta_cuspFunction_analyticAt, hasCoeffsIn_mul, E4_pow_three_isIntegralPowerSeries (Deltaqexpansions.lean:76), qOverDelta_isIntegralPowerSeries_aux]
- **Used by**: qj_isIntegralPowerSeries
- **Visibility**: private
- **Lines**: 308–312
- **Notes**: —

### `theorem qj_isIntegralPowerSeries`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 qj)`
- **What**: q·j has an integral q-expansion — the integrality of the j-function.
- **How**: transport along E4_pow_three_mul_qOverDelta_eq_qj.
- **Hypotheses**: none
- **Uses from project**: [IsIntegralPowerSeries, qj, E4_pow_three_mul_qOverDelta_eq_qj, qj_isIntegralPowerSeries_aux]
- **Used by**: qjCoeffs, qj_coeff_cast_aux
- **Visibility**: public
- **Lines**: 315–316
- **Notes**: used by qexp_coeffs.lean:50; `▸` with `simpa` is fragile.

### `def qjCoeffs`
- **Type**: `ℕ → ℤ` (:= `fun n ↦ (toIntegralPowerSeries qj_isIntegralPowerSeries).coeff n`)
- **What**: The integer q-expansion coefficients of q·j: `qjCoeffs 0 = 1, 1 ↦ 744, 2 ↦ 196884, …`.
- **How**: coefficients of the choice-lift.
- **Hypotheses**: none
- **Uses from project**: [toIntegralPowerSeries, qj_isIntegralPowerSeries]
- **Used by**: qj_coeff_cast_aux, qjCoeffs_hasSum_aux, infSumQj_summable_aux, qj_eq_tsum_aux, qjCoeffs_tsum_div_qParam_aux, j_eq_qjCoeffs_tsum, j_laurentQExpansion_isIntegral
- **Visibility**: public
- **Lines**: 319
- **Notes**: One of three "integer coefficients of j": `qjCoeffs : ℕ → ℤ` (here, choice), `Cox.jIntCoeff : ℤ → ℤ` (Cox/CoxMatrices/LaurentExpansion.lean:31, choice from `j_laurentQExpansion_isIntegral`), `qjCoeffInt : ℕ → ℤ` (qExpansion_tactic/Qj.lean:141, computable). Used outside jFunction/: nowhere (0 hits). Bridges: `qjCoeffs n = qj_qexpansion.coeff n` only as *private* qexp_coeffs.lean:46; `jIntCoeff (n-1) = qjCoeffInt n` only as *private* LevelThree.lean:122; no `jIntCoeff ↔ qjCoeffs` lemma anywhere.

### `private lemma qj_coeff_cast_aux`
- **Type**: `(n : ℕ) : ((qjCoeffs n : ℤ) : ℂ) = (qExpansion 1 qj).coeff n`
- **What**: Specification of qjCoeffs.
- **How**: `congrArg (coeff n) (coeTo_of_toIntegralPowerSeries _)`.
- **Hypotheses**: none
- **Uses from project**: [qjCoeffs, qj, coeTo_of_toIntegralPowerSeries, qj_isIntegralPowerSeries]
- **Used by**: qjCoeffs_hasSum_aux, j_laurentQExpansion_isIntegral
- **Visibility**: private
- **Lines**: 321–323
- **Notes**: should be the public spec lemma of qjCoeffs; being private, qexp_coeffs.lean:48–50 re-proves it.

### `private lemma qj_vadd_one_aux`
- **Type**: `(τ : ℍ) : qj ((1 : ℝ) +ᵥ τ) = qj τ`
- **What**: q·j is 1-periodic on ℍ.
- **How**: E4 and Delta are 1-periodic by mathlib `SlashInvariantForm.vAdd_apply_of_mem_strictPeriods` (ModularForms/Identities.lean:26); `cexp(2πi(τ+1)) = cexp(2πiτ)` by `Complex.exp_two_pi_mul_I`.
- **Hypotheses**: none
- **Uses from project**: [qj, j, E4, Delta]
- **Used by**: qj_periodic
- **Visibility**: private
- **Lines**: 325–334, body 9 lines
- **Notes**: —

### `lemma qj_periodic`
- **Type**: `Periodic (qj ∘ UpperHalfPlane.ofComplex) 1`
- **What**: The complex extension of q·j has period 1.
- **How**: case split `0 < im w`: use qj_vadd_one_aux with `ofComplex_apply_of_im_pos`; else both sides are the junk value (`ofComplex_apply_of_im_nonpos`).
- **Hypotheses**: none
- **Uses from project**: [qj, qj_vadd_one_aux]
- **Used by**: hasSum_qExpansion_qj, qj_cuspFunction_differentiableOn_aux
- **Visibility**: public
- **Lines**: 337–349, body 12 lines
- **Notes**: same case-split skeleton as jLevelN.lean:103–114; a general `Periodic (f ∘ ofComplex) h` from `∀ τ, f (h +ᵥ τ) = f τ` is missing (mathlib's `SlashInvariantFormClass.periodic_comp_ofComplex`, QExpansion.lean:120, needs a bundled form; JInvariant.lean:28–32 works around by bundling). Used by jLevelN.lean:106.

### `lemma qj_differentiableAt_of_im_pos`
- **Type**: `∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (qj ∘ UpperHalfPlane.ofComplex) z`
- **What**: The complex extension of q·j is holomorphic on the open upper half-plane.
- **How**: `cexp(2πi τ)` is MDiff (`Complex.differentiable_exp.mdifferentiable`, `UpperHalfPlane.mdifferentiable_coe`), multiply by j_mdifferentiable, unpack with mathlib `UpperHalfPlane.mdifferentiableAt_iff` (UpperHalfPlane/Manifold.lean:72).
- **Hypotheses**: im z > 0.
- **Uses from project**: [qj, j_mdifferentiable]
- **Used by**: qj_mdifferentiable
- **Visibility**: public
- **Lines**: 352–358, body 5 lines
- **Notes**: proves `MDiff qj` internally then unpacks; `qj_mdifferentiable` (361) repacks it. Used by jLevelN.lean:119.

### `lemma qj_mdifferentiable`
- **Type**: `MDiff qj`
- **What**: q·j is holomorphic on ℍ.
- **How**: `UpperHalfPlane.mdifferentiable_iff` (Manifold.lean:79) from the pointwise lemma.
- **Hypotheses**: none
- **Uses from project**: [qj, qj_differentiableAt_of_im_pos]
- **Used by**: hasSum_qExpansion_qj, qj_cuspFunction_differentiableOn_aux
- **Visibility**: public
- **Lines**: 361–364
- **Notes**: could be `hexp.mul j_mdifferentiable` directly with the pointwise version derived from it.

### `private lemma E4_pow_three_isBoundedAtImInfty_aux`
- **Type**: `IsBoundedAtImInfty (fun z : ℍ ↦ E4 z ^ 3)`
- **What**: E₄³ is bounded at i∞.
- **How**: `ModularFormClass.bdd_at_infty` and `IsBoundedAtImInfty.mul` twice.
- **Hypotheses**: none
- **Uses from project**: [E4]
- **Used by**: qj_isBoundedAtImInfty
- **Visibility**: private
- **Lines**: 366–369
- **Notes**: = `bdd_at_infty (E4.pow 3)` after `coe_pow`.

### `lemma qj_isBoundedAtImInfty`
- **Type**: `IsBoundedAtImInfty qj`
- **What**: q·j is bounded at i∞.
- **How**: q/Δ → 1 gives `IsBoundedAtImInfty qOverDelta` via `Tendsto.isBigO_one`; multiply with E₄³ bounded.
- **Hypotheses**: none
- **Uses from project**: [qj, qOverDelta, qOverDelta_tendsto_atImInfty, E4_pow_three_mul_qOverDelta_eq_qj, E4_pow_three_isBoundedAtImInfty_aux]
- **Used by**: hasSum_qExpansion_qj, qj_cuspFunction_differentiableOn_aux
- **Visibility**: public
- **Lines**: 372–377, body 5 lines
- **Notes**: used by jLevelN.lean:132.

### `lemma hasSum_qExpansion_qj`
- **Type**: `{τ : ℍ} : HasSum (fun m ↦ (qExpansion 1 qj).coeff m • 𝕢 1 τ ^ m) (qj τ)`
- **What**: The q-expansion of q·j converges to q·j.
- **How**: mathlib `UpperHalfPlane.hasSum_qExpansion` (QExpansion.lean:189) with periodicity, holomorphy, boundedness.
- **Hypotheses**: none
- **Uses from project**: [qj, qj_periodic, qj_mdifferentiable, qj_isBoundedAtImInfty]
- **Used by**: qjCoeffs_hasSum_aux
- **Visibility**: public
- **Lines**: 380–383
- **Notes**: 1 external use.

### `private lemma qjCoeffs_hasSum_aux`
- **Type**: `(z : ℍ) : HasSum (fun n ↦ (qjCoeffs n : ℂ) * cexp (2πi z) ^ n) (qj z)`
- **What**: Same convergence with integer coefficients and raw exponentials.
- **How**: rewrite hasSum_qExpansion_qj by qj_coeff_cast_aux and `Periodic.qParam`.
- **Hypotheses**: none
- **Uses from project**: [qjCoeffs, qj, qj_coeff_cast_aux, hasSum_qExpansion_qj]
- **Used by**: infSumQj_summable_aux, qj_eq_tsum_aux
- **Visibility**: private
- **Lines**: 385–388
- **Notes**: —

### `private lemma infSumQj_summable_aux`
- **Type**: `{z : ℍ} : Summable (fun n ↦ (qjCoeffs n) * cexp (2πi z) ^ n)`
- **What**: Summability of the integer q-series of q·j.
- **How**: `.summable` of the HasSum.
- **Hypotheses**: none
- **Uses from project**: [qjCoeffs, qjCoeffs_hasSum_aux]
- **Used by**: qjCoeffs_tsum_div_qParam_aux
- **Visibility**: private
- **Lines**: 390–392
- **Notes**: stale name (`infSumQj` does not exist).

### `private lemma qj_eq_tsum_aux`
- **Type**: `(z : ℍ) : qj z = ∑' n, (qjCoeffs n) * cexp (2πi z) ^ n`
- **What**: q·j as its integer q-series.
- **How**: `HasSum.tsum_eq`.
- **Hypotheses**: none
- **Uses from project**: [qj, qjCoeffs, qjCoeffs_hasSum_aux]
- **Used by**: j_eq_qjCoeffs_tsum
- **Visibility**: private
- **Lines**: 394–396
- **Notes**: —

### `private lemma qj_div_qParam_eq_j_aux`
- **Type**: `(z : ℍ) : qj z / cexp (2πi z) = j z`
- **What**: Dividing q·j by q gives j.
- **How**: `simp [qj]` (cexp ≠ 0).
- **Hypotheses**: none
- **Uses from project**: [qj, j]
- **Used by**: j_eq_qjCoeffs_tsum
- **Visibility**: private
- **Lines**: 398–400
- **Notes**: —

### `private lemma qjCoeffs_tsum_div_qParam_aux`
- **Type**: `(z : ℍ) : (∑' n, qjCoeffs n * q^n) / q = qjCoeffs 0 / q + ∑' n, qjCoeffs (n+1) * q^n` (q = cexp(2πiz))
- **What**: Peel off the constant term and divide by q.
- **How**: `Summable.tsum_eq_zero_add`, `add_div`, `tsum_div_const`, `pow_succ`.
- **Hypotheses**: none
- **Uses from project**: [qjCoeffs, infSumQj_summable_aux]
- **Used by**: j_eq_qjCoeffs_tsum
- **Visibility**: private
- **Lines**: 402–407, body 2 lines
- **Notes**: —

### `theorem j_eq_qjCoeffs_tsum`
- **Type**: `(z : ℍ) : j z = qjCoeffs 0 / cexp (2πi z) + ∑' n, qjCoeffs (n + 1) * cexp (2πi z) ^ n`
- **What**: The convergent Fourier expansion j = c₋₁/q + Σ cₙ qⁿ with integer coefficients.
- **How**: chain the three previous aux lemmas.
- **Hypotheses**: none
- **Uses from project**: [j, qjCoeffs, qj_div_qParam_eq_j_aux, qj_eq_tsum_aux, qjCoeffs_tsum_div_qParam_aux]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 410–413
- **Notes**: used only by qexp_coeffs.lean:132. `qjCoeffs 0 = 1` is not substituted here (that is `qjCoeffs_zero`, qexp_coeffs.lean:55 — derivable here from qj_qExpansion_coeff_zero + qj_coeff_cast_aux).

### `lemma qj_qExpansion_coeff_zero`
- **Type**: `(qExpansion 1 qj).coeff 0 = 1`
- **What**: q·j has constant term 1 (leading coefficient of the pole of j).
- **How**: `qj = E4³·qOverDelta`; `UpperHalfPlane.qExpansion_mul` and `qExpansion_of_pow` (QExpansion.lean:638) make the constant term the product of constant terms: `E_qExpansion_coeff_zero` (EisensteinSeries/QExpansion.lean:348) and cuspFunction_qOverDelta_zero_aux.
- **Hypotheses**: none
- **Uses from project**: [qj, E4, qOverDelta, E4_pow_three_mul_qOverDelta_eq_qj, E4_pow_three_cuspFunction_analyticAt, qOverDelta_cuspFunction_analyticAt, cuspFunction_qOverDelta_zero_aux]
- **Used by**: j_poleOrder
- **Visibility**: public
- **Lines**: 416–430, body 14 lines
- **Notes**: `hE4pow` (417–420) is the 3rd copy of the E4³ q-expansion block. 1 external use (LaurentExpansion.lean:46) + qexp_coeffs.lean:145.

### `private lemma qj_cuspFunction_differentiableOn_aux`
- **Type**: `DifferentiableOn ℂ (cuspFunction 1 qj) (Metric.ball 0 1)`
- **What**: The cusp function of q·j is holomorphic on the unit disc.
- **How**: mathlib `UpperHalfPlane.differentiableOn_cuspFunction_ball` (QExpansion.lean:95).
- **Hypotheses**: none
- **Uses from project**: [qj, qj_periodic, qj_mdifferentiable, qj_isBoundedAtImInfty]
- **Used by**: qj_cuspFunction_analyticAt
- **Visibility**: private
- **Lines**: 432–435
- **Notes**: —

### `lemma qj_cuspFunction_analyticAt`
- **Type**: `AnalyticAt ℂ (cuspFunction 1 qj) 0`
- **What**: q·j has a convergent q-expansion at the cusp.
- **How**: `DifferentiableOn.analyticAt` on the ball.
- **Hypotheses**: none
- **Uses from project**: [qj, qj_cuspFunction_differentiableOn_aux]
- **Used by**: j_cuspFunction_meromorphicAt, j_poleOrder
- **Visibility**: public
- **Lines**: 438–439
- **Notes**: 432–439 equal mathlib `UpperHalfPlane.analyticAt_cuspFunction_zero` (`QExpansion.lean:101`) applied to `one_pos qj_periodic qj_mdifferentiable qj_isBoundedAtImInfty` (one line). Same in jLevelN.lean:140–144.

### `private lemma inv_mul_cuspFunction_qj_eq_j_aux`
- **Type**: `(fun q ↦ q⁻¹ * cuspFunction 1 qj q) =ᶠ[nhdsWithin 0 {0}ᶜ] cuspFunction 1 j`
- **What**: Near the cusp, cusp(j) = q⁻¹·cusp(q·j).
- **How**: on 0<|q|<1 apply project `cuspFunction_qpow_mul_eq` (LaurentQExpansion.lean:330) with n=1 and cancel q.
- **Hypotheses**: none
- **Uses from project**: [qj, j, cuspFunction_qpow_mul_eq]
- **Used by**: j_cuspFunction_meromorphicAt, j_poleOrder
- **Visibility**: private
- **Lines**: 441–452, body 10 lines
- **Notes**: `hnorm` block (444–446) duplicated in jLevelN.lean:177–179.

### `lemma j_cuspFunction_meromorphicAt`
- **Type**: `MeromorphicAt (cuspFunction 1 j) (0 : ℂ)`
- **What**: j is meromorphic at the cusp.
- **How**: `q⁻¹` meromorphic (`MeromorphicAt.id.inv`) times analytic cusp(q·j), `MeromorphicAt.congr` on the punctured nbhd.
- **Hypotheses**: none
- **Uses from project**: [j, qj_cuspFunction_analyticAt, inv_mul_cuspFunction_qj_eq_j_aux]
- **Used by**: j_cuspFunction_not_analyticAt
- **Visibility**: public
- **Lines**: 455–457
- **Notes**: 11 external uses (Cox/ModularFunction.lean, JInvariant.lean, …).

### `lemma j_poleOrder`
- **Type**: `poleOrder 1 j = 1`
- **What**: j has a simple pole at ∞.
- **How**: project `poleOrder_eq_of_meromorphicOrderAt_eq` (LaurentQExpansion.lean:243); meromorphic order of `q⁻¹ · cusp(qj)` is −1 + 0 by mathlib `meromorphicOrderAt_inv` (Analysis/Meromorphic/Order.lean:510) and `meromorphicOrderAt_mul_of_ne_zero` (:863, since cusp(qj)(0) = 1).
- **Hypotheses**: none
- **Uses from project**: [poleOrder (LaurentQExpansion.lean:236), j, qj, poleOrder_eq_of_meromorphicOrderAt_eq, qj_qExpansion_coeff_zero, inv_mul_cuspFunction_qj_eq_j_aux, qj_cuspFunction_analyticAt]
- **Used by**: j_cuspFunction_not_analyticAt, j_poleRemoved, j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one, j_laurentQExpansion_isIntegral
- **Visibility**: public
- **Lines**: 460–470, body 10 lines
- **Notes**: closes with `rfl` on `WithTop ℤ` arithmetic — fragile. 12 external uses.

### `lemma j_cuspFunction_not_analyticAt`
- **Type**: `¬ AnalyticAt ℂ (cuspFunction 1 j) 0`
- **What**: The pole of j is genuine.
- **How**: project `analyticAt_cuspFunction_iff_poleOrder_eq_zero` (LaurentQExpansion.lean:420) + j_poleOrder.
- **Hypotheses**: none
- **Uses from project**: [j, analyticAt_cuspFunction_iff_poleOrder_eq_zero, j_cuspFunction_meromorphicAt, j_poleOrder]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 473–475
- **Notes**: unused anywhere in the project (0 external hits). Junk/documentation candidate.

### `lemma j_poleRemoved`
- **Type**: `poleRemoved 1 j = qj`
- **What**: The pole-removed j is q·j.
- **How**: unfold `UpperHalfPlane.poleRemoved` (LaurentQExpansion.lean:316) with j_poleOrder = 1, `pow_one`.
- **Hypotheses**: none
- **Uses from project**: [poleRemoved, j, qj, j_poleOrder]
- **Used by**: j_to_qExpansion
- **Visibility**: public
- **Lines**: 478–480
- **Notes**: —

### `lemma j_to_qExpansion`
- **Type**: `to_qExpansion 1 j = qExpansion 1 qj`
- **What**: The regular part of the Laurent expansion of j is the q-expansion of q·j.
- **How**: unfold `to_qExpansion` (LaurentQExpansion.lean:321) + j_poleRemoved.
- **Hypotheses**: none
- **Uses from project**: [to_qExpansion, j, qj, j_poleRemoved]
- **Used by**: j_laurentQExpansion_isIntegral
- **Visibility**: public
- **Lines**: 483–484
- **Notes**: 3 external uses (LevelThree.lean:130, LaurentExpansion.lean).

### `theorem j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one`
- **Type**: `{n : ℤ} (hn : n < -1) : (laurentqExpansion 1 j).coeff n = 0`
- **What**: No Laurent coefficients below q⁻¹.
- **How**: project `laurentqExpansion.coeff_eq_zero_of_lt` (LaurentQExpansion.lean:457) with j_poleOrder.
- **Hypotheses**: n < −1.
- **Uses from project**: [laurentqExpansion (LaurentQExpansion.lean:326), j, poleOrder, j_poleOrder, laurentqExpansion.coeff_eq_zero_of_lt]
- **Used by**: j_laurentQExpansion_isIntegral
- **Visibility**: public
- **Lines**: 487–490
- **Notes**: 0 external uses.

### `theorem j_laurentQExpansion_isIntegral`
- **Type**: `{n : ℤ} : ∃ m : ℤ, (laurentqExpansion 1 j).coeff n = m`
- **What**: Every Laurent coefficient of j at ∞ is an integer.
- **How**: n < −1: 0; else project `laurentqExpansion.coeff_of_geq` (LaurentQExpansion.lean:469) + j_to_qExpansion + j_poleOrder reduce to `qjCoeffs (n+1).toNat` via qj_coeff_cast_aux.
- **Hypotheses**: none
- **Uses from project**: [laurentqExpansion, j, qjCoeffs, j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one, poleOrder, j_poleOrder, laurentqExpansion.coeff_of_geq, j_to_qExpansion, qj_coeff_cast_aux]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 493–502, body 9 lines
- **Notes**: An ∃-statement whose witness is `.choose`n downstream as `Cox.jIntCoeff` (LaurentExpansion.lean:31–36) although the explicit witness `if n < -1 then 0 else qjCoeffs (n+1).toNat` is at hand; stating it as a def + spec would make `jIntCoeff (n-1) = qjCoeffs n` definitional. 3 external uses.

## File Summary
- Total declarations: 67 (7 defs: j, deltaOverQ, deltaShiftedQSeries, integralDeltaOverQ, qOverDelta, qj, qjCoeffs; 60 lemmas/theorems; 0 instances; 1 local notation)
- Key API (used by 3+ others in the file): j, qj, deltaOverQ, qOverDelta, qjCoeffs, integralDeltaOverQ, cuspFunction_apply_zero_of_tendsto (4), deltaOverQ_eq_qParam_inv_smul_Delta (3), deltaShiftedQSeries_eq_deltaOverQ (4), E4_pow_three_mul_qOverDelta_eq_qj (3), qOverDelta_cuspFunction_analyticAt (3), j_poleOrder (4)
- Unused declarations (not used by anything in this file): j_modularGroup_smul (7 ext), j_eq_qjCoeffs_tsum (qexp_coeffs only), j_cuspFunction_not_analyticAt (unused anywhere), j_laurentQExpansion_isIntegral (3 ext)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest deltaShiftedQSeries_analyticAt_aux, 28 lines)

## Observations
### Mathlib API candidates
- `qj_cuspFunction_differentiableOn_aux`+`qj_cuspFunction_analyticAt` (432–439) = mathlib `UpperHalfPlane.analyticAt_cuspFunction_zero` (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:101`), one application.
- `Delta_qExpansion_coeff_zero_aux` (108) = mathlib `CuspFormClass.qExpansion_coeff_zero` (`QExpansion.lean:408`).
- `deltaShiftedQSeries_analyticAt_aux` (167–195): lines 174–190 re-derive mathlib's **private** `hasFPowerSeriesOnBall_update` (`QExpansion.lean:239`); ask to make it public (then 143–195 collapse to ~5 lines). Alternative route avoiding deltaShiftedQSeries entirely: `cuspFunction 1 deltaOverQ` is `cusp(Δ)(q)/q` with a simple zero at 0 — mathlib `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` (`Mathlib/Analysis/Analytic/IsolatedZeros.lean:185`) gives the analytic quotient.
- `E4_pow_three_isModularForm_aux` (277): use `E4.pow 3` + `ModularForm.coe_pow` directly.
- `cuspFunction_qOverDelta_eq_inv_aux` (262): mathlib lacks `cuspFunction_inv`/`cuspFunction_div` (has `cuspFunction_mul` `QExpansion.lean:440`, `_smul/_neg/_add/_sub` 448–461) — small upstream candidate.
- `cuspFunction_apply_zero_of_tendsto` (43): not in mathlib (closest `UpperHalfPlane.cuspFunction_apply_zero` `QExpansion.lean:107`); upstream candidate.
- `deltaOverQ_tendsto_atImInfty` (101) is `ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow` (mathlib `Discriminant.lean`, via project `Delta_boundedfactor`).
- No mathlib j-function, no mathlib statement of `j`'s integrality or pole order (searched `jInvariant`, `j-invariant`, `modular invariant`, `ramanujan` under Mathlib/NumberTheory).
### Missing API / repeated patterns
- Cast-coefficient lemma re-proved at 208–211 and 321–323 (see Deltaqexpansions inventory); `qj_coeff_cast_aux` should be the public spec of `qjCoeffs`.
- `qExpansion 1 (E4^3) = (qExpansion 1 E4)^3` block at 417–420 (4th copy project-wide).
- Periodicity-from-vadd case split (337–349) duplicated in jLevelN.lean:103–114; add `UpperHalfPlane.periodic_comp_ofComplex_of_vadd`.
- "cusp function at nonzero q" gadget (152–158) duplicated in jLevelN.lean:151–154 and LaurentQExpansion.lean:330ff.
- `hnorm` (444–446) duplicated jLevelN.lean:177–179: lemma `norm_lt_one_mem_nhdsWithin_ne`.
- Missing companions: `qjCoeffs_zero` lives in qexp_coeffs.lean (should be here, derivable from 416 + 321); `integralDeltaOverQ_coeff`; `qj_apply`/`j_apply` simp lemmas; `qj_mdifferentiable` derived circularly through the pointwise lemma.
### Junk candidates
- `j_cuspFunction_not_analyticAt` (473–475): unused project-wide.
- `deltaOverQ_ne_zero` (96), `deltaOverQ_eq_qParam_inv_mul_Delta` (85): public but only used in-file (fine, but `_mul_` and `_smul_` forms duplicate each other).
- `infSumQj_summable_aux` (390): stale name.
- `cuspFunction_deltaShiftedQSeries_zero_aux` (161) vs `cuspFunction_deltaOverQ_zero_aux` (256) vs `hcoeff0C` (223): three proofs of "value 1 at the cusp".
### Moral duplicates within this batch
- `deltaShiftedQSeries` vs `deltaOverQ` (equal functions, 132): all `_aux` lemmas exist in both flavours (hasSum, zero value, analyticity).
- `qj_differentiableAt_of_im_pos`/`qj_mdifferentiable` ↔ jLevelN `qjN_differentiableAt_aux`/`qjN_mdifferentiable_aux`; `qj_periodic` ↔ `qjN_periodic_aux`; `qj_cuspFunction_analyticAt` ↔ `qjN_cuspFunction_analyticAt_aux`.
- `ModularFunction.j_mdifferentiable` (ModularFunctions/JInvariant.lean:24) is a re-export of `j_mdifferentiable`; `ModularFunction.j_periodic` (JInvariant.lean:28) proves 1-periodicity of `j ∘ ofComplex` by bundling — same skeleton as `qj_periodic`.
### Generalization notes
- `cuspFunction_apply_zero_of_tendsto`: holds for any `h > 0` (only `invQParam_tendsto hh` needs `0 < h`).
- `qOverDelta_isIntegralPowerSeries_aux` (300–306): general fact "image of a unit's inverse under a ring hom is the inverse of the image" — holds for any `R →+* S`; the `IsRIntegralCPowerSeries R` layer exists.
- The whole Δ/q ↔ q/Δ inversion argument only uses: constant term 1 ⇒ unit in ℤ⟦q⟧ ⇒ inverse integral; a general lemma `IsIntegralPowerSeries.inv_of_constantCoeff_eq_one` would package 205–306.
