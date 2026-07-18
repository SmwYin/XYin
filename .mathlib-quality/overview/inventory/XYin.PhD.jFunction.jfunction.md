# Source: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/jFunction/jfunction.lean — project imports: `XYin.PhD.IntegralPowerSeries.HasIntegralQExpansion`, `XYin.PhD.jFunction.Deltaqexpansions`, `XYin.PhD.LaurentQExpansion.LaurentQExpansion`

### `syntax local notation 𝕢`
- **Type**: `local notation "𝕢" => Periodic.qParam`
- **What**: Local shorthand for the q-parameter map q(h, τ) = exp(2πiτ/h).
- **How**: Notation alias for mathlib's `Function.Periodic.qParam`; no proof content.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `deltaShiftedQSeries_hasSum_aux`, `cuspFunction_deltaShiftedQSeries_hasSum_aux`, `hasSum_qExpansion_qj`, `infSumQj_summable_aux`, `infSumQj_eq_qj_aux`, `inv_mul_cuspFunction_qj_eq_j_aux`
- **Visibility**: scoped (local to file)
- **Lines**: 39 (1 line)
- **Notes**: none

### `def j`
- **Type**: `j : ℍ → ℂ` (`:= fun τ ↦ (E4 τ) ^ 3 / Delta τ`)
- **What**: The classical modular j-invariant, defined as E₄³/Δ (with the normalization giving q-expansion q⁻¹ + 744 + …).
- **How**: Pointwise quotient of the project's Eisenstein series E₄ cubed by the discriminant cusp form Δ.
- **Hypotheses**: none.
- **Uses from project**: [`E4` (Deltaqexpansions), `Delta` (Modularforms.Delta)]
- **Used by**: `j_slash_invariant`, `j_modularGroup_smul`, `qj`, `qj_vadd_one_aux`, `qj_differentiableAt_of_im_pos`, `qj_div_qParam_eq_j_aux`, `j_eq_qjCoeffs_tsum`, `j_hasIntegralQExpansion`, `inv_mul_cuspFunction_qj_eq_j_aux`, `j_cuspFunction_meromorphicAt`, `j_cuspFunction_not_analyticAt`, `j_poleOrder`, `j_poleRemoved`, `j_to_qExpansion`, `j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one`, `j_laurentQExpansion_isIntegral`
- **Visibility**: public
- **Lines**: 44 (1 line)
- **Notes**: none

### `lemma j_slash_invariant`
- **Type**: `(γ : SL(2, ℤ)) : j ∣[(0 : ℤ)] γ = j`
- **What**: The j-function is invariant under the weight-0 slash action of SL₂(ℤ), i.e. j is a modular function of level one.
- **How**: Uses the slash transformation laws of E₄ (weight 4) and Δ (weight 12) — `slash_action_eq'` for both, with Δ's coercion handled by the project's `CuspForm_apply` — so the automorphy factors denom(γ,z)¹² cancel in the quotient E₄³/Δ; the cancellation is closed with `Complex.mul_inv_cancel` and `denom_ne_zero`.
- **Hypotheses**: γ ∈ SL₂(ℤ).
- **Uses from project**: [`j`, `E4`, `Delta`, `CuspForm_apply` (Modularforms.Delta)]
- **Used by**: `j_modularGroup_smul`
- **Visibility**: public
- **Lines**: 46–70 (24-line proof)
- **Notes**: none

### `lemma j_modularGroup_smul`
- **Type**: `(γ : SL(2, ℤ)) (z : ℍ) : j (γ • z) = j z`
- **What**: Pointwise SL₂(ℤ)-invariance of j: j(γz) = j(z) for the Möbius action.
- **How**: Specializes `j_slash_invariant` at z and simplifies the weight-0 slash formula (`SL_slash_apply`, the automorphy factor is denom⁰ = 1).
- **Hypotheses**: none.
- **Uses from project**: [`j_slash_invariant`, `j`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 73–75 (2-line proof)
- **Notes**: none

### `def deltaOverQ`
- **Type**: `deltaOverQ : ℍ → ℂ` (`:= fun z ↦ ∏' n, (1 - exp(2πi(n+1)z))^24`)
- **What**: The function Δ(z)/q — the discriminant with its leading factor q removed — expressed directly by its infinite product ∏(1−qⁿ)²⁴.
- **How**: Definition as a tsum-style infinite product; no proof content.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `deltaOverQ_eq_qParam_inv_mul_Delta`, `deltaOverQ_ne_zero`, `deltaShiftedQSeries_eq_deltaOverQ`, `cuspFunction_deltaShiftedQSeries_zero_aux`, `deltaOverQ_isIntegralPowerSeries`, `integralDeltaOverQ`, `coeTo_integralDeltaOverQ`, `integralDeltaOverQ_constantCoeff_isUnit_aux`, `qOverDelta`, `E4_pow_three_mul_qOverDelta_eq_qj`, `deltaOverQ_analyticAt_aux`, `deltaOverQ_tendsto_atImInfty`, `qOverDelta_tendsto_atImInfty`, `cuspFunction_deltaOverQ_zero_aux`, `cuspFunction_qOverDelta_eq_inv_aux`, `deltaOverQ_inv_analyticAt_aux`, `integralDeltaOverQ_mul_qExpansion_qOverDelta`
- **Visibility**: public
- **Lines**: 78–79 (2 lines)
- **Notes**: none

### `lemma deltaOverQ_eq_qParam_inv_mul_Delta`
- **Type**: `deltaOverQ = (fun z ↦ 1 / cexp (2 * π * Complex.I * z) : ℍ → ℂ) * Delta`
- **What**: Identifies the infinite product deltaOverQ with q⁻¹·Δ, justifying the name.
- **How**: Unfolds the project's product definition `Δ` (which is q·∏(1−qⁿ)²⁴) through `Delta_apply` and cancels the exponential factor.
- **Hypotheses**: none.
- **Uses from project**: [`deltaOverQ`, `Delta`, `Delta_apply`, `Δ` (Modularforms.Delta)]
- **Used by**: `deltaShiftedQSeries_eq_deltaOverQ`, `deltaShiftedQSeries_hasSum_aux`, `E4_pow_three_mul_qOverDelta_eq_qj`
- **Visibility**: public
- **Lines**: 81–84 (3-line proof)
- **Notes**: none

### `lemma deltaOverQ_ne_zero`
- **Type**: `(z : ℍ) : deltaOverQ z ≠ 0`
- **What**: Non-vanishing of Δ/q on the upper half-plane (inherited from non-vanishing of Δ, since the removed factor q is a unit).
- **How**: If the product vanished, Δ = q·∏ would vanish, contradicting the project's `Δ_ne_zero`.
- **Hypotheses**: none.
- **Uses from project**: [`deltaOverQ`, `Δ_ne_zero`, `Δ`]
- **Used by**: `integralDeltaOverQ_mul_qExpansion_qOverDelta`
- **Visibility**: public
- **Lines**: 86–91 (5-line proof)
- **Notes**: none

### `def deltaShiftedQSeries`
- **Type**: `deltaShiftedQSeries : ℍ → ℂ` (`:= fun z ↦ ∑' n, (qExpansion 1 Delta).coeff (n+1) * exp(2πiz)^n`)
- **What**: The q-series of Δ with indices shifted down by one (the τ(n+1)qⁿ series) — an analytic avatar of Δ/q.
- **How**: Definition as a tsum of shifted q-expansion coefficients of Δ; no proof content.
- **Hypotheses**: none.
- **Uses from project**: [`Delta`]
- **Used by**: `deltaShiftedQSeries_eq_deltaOverQ`, `deltaShiftedQSeries_hasSum_aux`, `cuspFunction_deltaShiftedQSeries_hasSum_aux`, `cuspFunction_deltaShiftedQSeries_zero_aux`, `deltaShiftedQSeries_analyticAt_aux`, `deltaShiftedQSeries_qExpansion_coeff`, `deltaOverQ_isIntegralPowerSeries`, `deltaOverQ_analyticAt_aux`
- **Visibility**: public
- **Lines**: 94–95 (2 lines)
- **Notes**: none

### `lemma deltaShiftedQSeries_eq_deltaOverQ`
- **Type**: `deltaShiftedQSeries = deltaOverQ`
- **What**: The shifted q-series of Δ converges to Δ/q pointwise on ℍ, i.e. the analytic series and the infinite product define the same function.
- **How**: From mathlib's `UpperHalfPlane.hasSum_qExpansion` for Δ, drops the vanishing constant term (`CuspFormClass.cuspFunction_apply_zero`) via `hasSum_nat_add_iff'`, divides the resulting HasSum by q (`HasSum.mul_left`), and identifies the limit with q⁻¹Δ = deltaOverQ via `deltaOverQ_eq_qParam_inv_mul_Delta`.
- **Hypotheses**: none.
- **Uses from project**: [`deltaShiftedQSeries`, `deltaOverQ`, `Delta`, `Delta_apply`, `Δ`, `deltaOverQ_eq_qParam_inv_mul_Delta`]
- **Used by**: `deltaShiftedQSeries_hasSum_aux`, `cuspFunction_deltaShiftedQSeries_zero_aux`, `deltaOverQ_isIntegralPowerSeries`, `deltaOverQ_analyticAt_aux`
- **Visibility**: public
- **Lines**: 97–123 (26-line proof)
- **Notes**: none

### `lemma deltaShiftedQSeries_hasSum_aux`
- **Type**: `(z : ℍ) : HasSum (fun m ↦ ((qExpansion 1 Delta).coeff (m + 1)) • 𝕢 1 z ^ m) (deltaShiftedQSeries z)`
- **What**: The shifted coefficient series genuinely HasSum-converges to deltaShiftedQSeries at every point of ℍ (in `qParam` form).
- **How**: Repeats the shift-and-divide argument: mathlib's `UpperHalfPlane.hasSum_qExpansion` for Δ, drop the zero constant term with `hasSum_nat_add_iff'`, scale by q⁻¹ with `HasSum.const_smul`, and identify the value via `deltaShiftedQSeries_eq_deltaOverQ` and `deltaOverQ_eq_qParam_inv_mul_Delta`.
- **Hypotheses**: none.
- **Uses from project**: [`deltaShiftedQSeries`, `Delta`, `deltaShiftedQSeries_eq_deltaOverQ`, `deltaOverQ_eq_qParam_inv_mul_Delta`]
- **Used by**: `cuspFunction_deltaShiftedQSeries_hasSum_aux`, `deltaShiftedQSeries_qExpansion_coeff`
- **Visibility**: private
- **Lines**: 125–151 (26-line proof)
- **Notes**: none

### `lemma cuspFunction_deltaShiftedQSeries_hasSum_aux`
- **Type**: `∀ {q : ℂ}, ‖q‖ < 1 → q ≠ 0 → HasSum (fun n ↦ ((qExpansion 1 Delta).coeff (n + 1)) • q ^ n) (cuspFunction 1 deltaShiftedQSeries q)`
- **What**: On the punctured unit q-disc, the shifted Δ-coefficient power series sums to the cusp function of deltaShiftedQSeries.
- **How**: Pulls q back to τ = invQParam(q) ∈ ℍ via `Periodic.im_invQParam_pos_of_norm_lt_one` and `Periodic.qParam_right_inv`, rewrites the cusp function off 0 with `Periodic.cuspFunction_eq_of_nonzero`, and applies `deltaShiftedQSeries_hasSum_aux` at τ.
- **Hypotheses**: ‖q‖ < 1, q ≠ 0.
- **Uses from project**: [`deltaShiftedQSeries_hasSum_aux`, `deltaShiftedQSeries`, `Delta`]
- **Used by**: `deltaShiftedQSeries_analyticAt_aux`
- **Visibility**: private
- **Lines**: 153–169 (16-line proof)
- **Notes**: none

### `lemma cuspFunction_deltaShiftedQSeries_zero_aux`
- **Type**: `cuspFunction 1 deltaShiftedQSeries 0 = 1`
- **What**: The cusp function of the shifted Δ-series takes the value 1 at q = 0 (since Δ/q → 1 as Im τ → ∞).
- **How**: The limit Δ/q → 1 at i∞ is the project's `Delta_boundedfactor`; composing with `Periodic.invQParam_tendsto` and `tendsto_comap_im_ofComplex` computes the `limUnder` defining the cusp function at 0.
- **Hypotheses**: none.
- **Uses from project**: [`deltaShiftedQSeries_eq_deltaOverQ`, `deltaOverQ`, `Delta_boundedfactor` (Modularforms.Delta), `deltaShiftedQSeries`]
- **Used by**: `deltaShiftedQSeries_analyticAt_aux`
- **Visibility**: private
- **Lines**: 171–183 (12-line proof)
- **Notes**: none

### `lemma deltaShiftedQSeries_analyticAt_aux`
- **Type**: `AnalyticAt ℂ (cuspFunction 1 deltaShiftedQSeries) 0`
- **What**: The cusp function of the shifted Δ-series is analytic at q = 0; this makes Δ/q an honest analytic function at the cusp with value 1.
- **How**: Builds a `HasFPowerSeriesOnBall` on the unit ball for the coefficient series `FormalMultilinearSeries.ofScalars`: radius ≥ 1 from summability of the HasSum family via `FormalMultilinearSeries.le_radius_of_summable`, convergence off 0 from `cuspFunction_deltaShiftedQSeries_hasSum_aux`, and the center value matched using `cuspFunction_deltaShiftedQSeries_zero_aux` together with the project's `Delta_q_one_term` (τ(1) = 1), removing the `Function.update` via `update_eq_self_iff`.
- **Hypotheses**: none.
- **Uses from project**: [`cuspFunction_deltaShiftedQSeries_hasSum_aux`, `cuspFunction_deltaShiftedQSeries_zero_aux`, `Delta_q_one_term` (Modularforms.Eisenstein), `deltaShiftedQSeries`, `Delta`]
- **Used by**: `deltaShiftedQSeries_qExpansion_coeff`, `deltaOverQ_analyticAt_aux`
- **Visibility**: private
- **Lines**: 185–213 (28-line proof)
- **Notes**: none

### `lemma deltaShiftedQSeries_qExpansion_coeff`
- **Type**: `(n : ℕ) : (qExpansion 1 deltaShiftedQSeries).coeff n = (qExpansion 1 Delta).coeff (n + 1)`
- **What**: The q-expansion of the shifted series is the shift of the q-expansion of Δ: coefficient n of Δ/q equals coefficient n+1 of Δ.
- **How**: Uniqueness of q-expansion coefficients — mathlib's `UpperHalfPlane.qExpansion_coeff_unique` applied to the analyticity `deltaShiftedQSeries_analyticAt_aux` and the explicit HasSum `deltaShiftedQSeries_hasSum_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`deltaShiftedQSeries_analyticAt_aux`, `deltaShiftedQSeries_hasSum_aux`, `deltaShiftedQSeries`, `Delta`]
- **Used by**: `deltaOverQ_isIntegralPowerSeries`
- **Visibility**: public
- **Lines**: 215–220 (5-line proof)
- **Notes**: none

### `lemma deltaOverQ_isIntegralPowerSeries`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 deltaOverQ)`
- **What**: The q-expansion of Δ/q has integer coefficients — namely the shifted Ramanujan tau values τ(n+1).
- **How**: Via `int_iff` with witness `integralDelta.coeff (n+1)`: identifies qExpansion(Δ/q) with qExpansion(deltaShiftedQSeries) using the project's extensionality `qExpansion_ext` and `deltaShiftedQSeries_eq_deltaOverQ`, then shifts by `deltaShiftedQSeries_qExpansion_coeff` and casts through `coeTo_of_toIntegralPowerSeries Delta_isIntegralPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: [`int_iff`, `integralDelta` (Deltaqexpansions), `qExpansion_ext` (Modularforms.qExpansion_lems), `deltaOverQ`, `deltaShiftedQSeries`, `deltaShiftedQSeries_eq_deltaOverQ`, `deltaShiftedQSeries_qExpansion_coeff`, `coeTo_of_toIntegralPowerSeries`, `Delta_isIntegralPowerSeries` (Deltaqexpansions), `Delta`, `IsIntegralPowerSeries`]
- **Used by**: `integralDeltaOverQ`, `coeTo_integralDeltaOverQ`
- **Visibility**: public
- **Lines**: 222–239 (17-line proof)
- **Notes**: none

### `def integralDeltaOverQ`
- **Type**: `integralDeltaOverQ : PowerSeries ℤ`
- **What**: The integral power series lift of the q-expansion of Δ/q (coefficients τ(n+1), constant term 1).
- **How**: `toIntegralPowerSeries` applied to `deltaOverQ_isIntegralPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: [`toIntegralPowerSeries`, `deltaOverQ_isIntegralPowerSeries`]
- **Used by**: `coeTo_integralDeltaOverQ`, `integralDeltaOverQ_constantCoeff_isUnit_aux`, `integralDeltaOverQ_isUnit_aux`, `integralDeltaOverQ_mul_qExpansion_qOverDelta`, `qOverDelta_isIntegralPowerSeries_aux`
- **Visibility**: public
- **Lines**: 242 (1 line)
- **Notes**: none

### `lemma coeTo_integralDeltaOverQ`
- **Type**: `(coeToComplexPowerSeries.ringHom ℤ) integralDeltaOverQ = qExpansion 1 deltaOverQ`
- **What**: The complexification of the integral lift recovers the q-expansion of Δ/q.
- **How**: Direct application of the project's round-trip lemma `coeTo_of_toIntegralPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: [`coeToComplexPowerSeries.ringHom`, `integralDeltaOverQ`, `deltaOverQ`, `coeTo_of_toIntegralPowerSeries`, `deltaOverQ_isIntegralPowerSeries`]
- **Used by**: `integralDeltaOverQ_constantCoeff_isUnit_aux`, `integralDeltaOverQ_mul_qExpansion_qOverDelta`
- **Visibility**: public
- **Lines**: 244–246 (1-line proof)
- **Notes**: none

### `lemma integralDeltaOverQ_constantCoeff_isUnit_aux`
- **Type**: `IsUnit (constantCoeff integralDeltaOverQ : ℤ)`
- **What**: The constant coefficient of the integral Δ/q series is a unit of ℤ (indeed it equals 1, since Δ/q → 1 at i∞).
- **How**: Computes cuspFunction(Δ/q)(0) = 1 as a `limUnder` from the project's `Delta_boundedfactor` composed with `Periodic.invQParam_tendsto`, hence the complex constant coefficient is 1; casts down to ℤ through `coeTo_integralDeltaOverQ` and the `powerSeriesMapAlgHom` unfolding, concluding the integer is 1.
- **Hypotheses**: none.
- **Uses from project**: [`Delta_boundedfactor`, `deltaOverQ`, `coeTo_integralDeltaOverQ`, `integralDeltaOverQ`, `coeToComplexPowerSeries.ringHom`, `powerSeriesMapAlgHom` (IntegralPowerSeries)]
- **Used by**: `integralDeltaOverQ_isUnit_aux`
- **Visibility**: private
- **Lines**: 248–271 (23-line proof)
- **Notes**: none

### `lemma integralDeltaOverQ_isUnit_aux`
- **Type**: `IsUnit integralDeltaOverQ`
- **What**: The integral Δ/q series is invertible in ℤ⟦q⟧ (constant term ±1 makes a power series a unit).
- **How**: mathlib's `PowerSeries.isUnit_iff_constantCoeff` applied to `integralDeltaOverQ_constantCoeff_isUnit_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`integralDeltaOverQ_constantCoeff_isUnit_aux`, `integralDeltaOverQ`]
- **Used by**: `qOverDelta_isIntegralPowerSeries_aux`
- **Visibility**: private
- **Lines**: 273–275 (2-line proof)
- **Notes**: none

### `def qOverDelta`
- **Type**: `qOverDelta : ℍ → ℂ` (`:= fun z ↦ 1 / deltaOverQ z`)
- **What**: The reciprocal q/Δ of the normalized discriminant factor — the correction that turns E₄³ into q·j.
- **How**: Pointwise reciprocal of `deltaOverQ`; no proof content.
- **Hypotheses**: none.
- **Uses from project**: [`deltaOverQ`]
- **Used by**: `E4_pow_three_mul_qOverDelta_eq_qj`, `qOverDelta_tendsto_atImInfty`, `cuspFunction_qOverDelta_zero_aux`, `cuspFunction_qOverDelta_eq_inv_aux`, `qOverDelta_cuspFunction_analyticAt`, `integralDeltaOverQ_mul_qExpansion_qOverDelta`, `qOverDelta_isIntegralPowerSeries_aux`, `qj_isIntegralPowerSeries_aux`, `qj_isBoundedAtImInfty`, `qj_qExpansion_coeff_zero`
- **Visibility**: public
- **Lines**: 278 (1 line)
- **Notes**: none

### `def qj`
- **Type**: `qj : ℍ → ℂ` (`:= (fun z ↦ cexp (2 * π * Complex.I * z)) * j`)
- **What**: The regularized j-function q·j(z) — holomorphic at the cusp since multiplying by q removes j's simple pole.
- **How**: Pointwise product of the q-parameter with j; no proof content.
- **Hypotheses**: none.
- **Uses from project**: [`j`]
- **Used by**: `E4_pow_three_mul_qOverDelta_eq_qj`, `qj_isIntegralPowerSeries`, `qjCoeffs`, `qj_coeff_cast_aux`, `infSumQj_aux`, `qj_vadd_one_aux`, `qj_periodic`, `qj_differentiableAt_of_im_pos`, `qj_mdifferentiable`, `qj_isBoundedAtImInfty`, `hasSum_qExpansion_qj`, `infSumQj_summable_aux`, `infSumQj_eq_qj_aux`, `qj_eq_tsum_aux`, `qj_div_qParam_eq_series_div_qParam_aux`, `qj_div_qParam_eq_j_aux`, `qj_qExpansion_coeff_zero`, `j_hasIntegralQExpansion`, `qj_cuspFunction_differentiableOn_aux`, `qj_cuspFunction_analyticAt`, `inv_mul_cuspFunction_qj_eq_j_aux`, `j_cuspFunction_not_analyticAt`, `j_poleOrder`, `j_poleRemoved`, `j_to_qExpansion`, `j_laurentQExpansion_isIntegral`
- **Visibility**: public
- **Lines**: 281 (1 line)
- **Notes**: none

### `lemma E4_pow_three_mul_qOverDelta_eq_qj`
- **Type**: `E4 ^ 3 * qOverDelta = qj`
- **What**: The factorization q·j = E₄³ · (q/Δ), reducing integrality of qj to integrality of E₄³ and q/Δ.
- **How**: Pointwise computation: qOverDelta(z) = q/Δ(z) from `deltaOverQ_eq_qParam_inv_mul_Delta` (using Δ ≠ 0 via `Δ_ne_zero` and exp ≠ 0), then E₄³·q/Δ = q·(E₄³/Δ) = q·j by `field_simp`/`ring`.
- **Hypotheses**: none.
- **Uses from project**: [`E4`, `qOverDelta`, `qj`, `j`, `deltaOverQ_eq_qParam_inv_mul_Delta`, `Delta`, `Delta_apply`, `Δ_ne_zero`, `deltaOverQ`]
- **Used by**: `qj_isIntegralPowerSeries`, `qj_isBoundedAtImInfty`, `qj_qExpansion_coeff_zero`
- **Visibility**: public
- **Lines**: 283–295 (12-line proof)
- **Notes**: none

### `lemma deltaOverQ_analyticAt_aux`
- **Type**: `AnalyticAt ℂ (cuspFunction 1 deltaOverQ) 0`
- **What**: The cusp function of Δ/q is analytic at q = 0.
- **How**: Transfers `deltaShiftedQSeries_analyticAt_aux` along the function equality `deltaShiftedQSeries_eq_deltaOverQ`.
- **Hypotheses**: none.
- **Uses from project**: [`deltaShiftedQSeries_eq_deltaOverQ`, `deltaShiftedQSeries_analyticAt_aux`, `deltaOverQ`]
- **Used by**: `deltaOverQ_inv_analyticAt_aux`, `integralDeltaOverQ_mul_qExpansion_qOverDelta`
- **Visibility**: private
- **Lines**: 297–298 (1-line proof)
- **Notes**: none

### `lemma deltaOverQ_tendsto_atImInfty`
- **Type**: `Tendsto deltaOverQ atImInfty (nhds (1 : ℂ))`
- **What**: Δ/q tends to 1 as Im z → ∞ (the infinite product ∏(1−qⁿ)²⁴ → 1 as q → 0).
- **How**: Direct restatement of the project's `Delta_boundedfactor`.
- **Hypotheses**: none.
- **Uses from project**: [`deltaOverQ`, `Delta_boundedfactor`]
- **Used by**: `qOverDelta_tendsto_atImInfty`, `cuspFunction_deltaOverQ_zero_aux`
- **Visibility**: public
- **Lines**: 300–301 (1-line proof)
- **Notes**: none

### `lemma qOverDelta_tendsto_atImInfty`
- **Type**: `Tendsto qOverDelta atImInfty (nhds (1 : ℂ))`
- **What**: q/Δ tends to 1 as Im z → ∞.
- **How**: Inverts the limit of `deltaOverQ_tendsto_atImInfty` with `Tendsto.inv₀` (the limit 1 is nonzero).
- **Hypotheses**: none.
- **Uses from project**: [`qOverDelta`, `deltaOverQ_tendsto_atImInfty`, `deltaOverQ`]
- **Used by**: `cuspFunction_qOverDelta_zero_aux`, `qj_isBoundedAtImInfty`
- **Visibility**: public
- **Lines**: 303–307 (4-line proof)
- **Notes**: none

### `lemma cuspFunction_deltaOverQ_zero_aux`
- **Type**: `cuspFunction 1 deltaOverQ 0 = 1`
- **What**: The cusp-function value of Δ/q at q = 0 is 1.
- **How**: Computes the defining `limUnder` by composing `deltaOverQ_tendsto_atImInfty` with mathlib's `Periodic.invQParam_tendsto` and `tendsto_comap_im_ofComplex`, then `Tendsto.limUnder_eq`.
- **Hypotheses**: none.
- **Uses from project**: [`deltaOverQ_tendsto_atImInfty`, `deltaOverQ`]
- **Used by**: `cuspFunction_qOverDelta_eq_inv_aux`, `deltaOverQ_inv_analyticAt_aux`
- **Visibility**: private
- **Lines**: 309–314 (5-line proof)
- **Notes**: none

### `lemma cuspFunction_qOverDelta_zero_aux`
- **Type**: `cuspFunction 1 qOverDelta 0 = 1`
- **What**: The cusp-function value of q/Δ at q = 0 is 1.
- **How**: Same `limUnder` computation from `qOverDelta_tendsto_atImInfty` composed with `Periodic.invQParam_tendsto`.
- **Hypotheses**: none.
- **Uses from project**: [`qOverDelta_tendsto_atImInfty`, `qOverDelta`]
- **Used by**: `cuspFunction_qOverDelta_eq_inv_aux`, `qj_qExpansion_coeff_zero`
- **Visibility**: private
- **Lines**: 316–321 (5-line proof)
- **Notes**: none

### `lemma cuspFunction_qOverDelta_eq_inv_aux`
- **Type**: `cuspFunction 1 qOverDelta = fun q ↦ (cuspFunction 1 deltaOverQ q)⁻¹`
- **What**: The cusp function of the reciprocal is the reciprocal of the cusp function, globally on the q-disc.
- **How**: Off q = 0 both sides agree by the definitional formula of `Periodic.cuspFunction`; at q = 0 both equal 1 by `cuspFunction_deltaOverQ_zero_aux` and `cuspFunction_qOverDelta_zero_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`cuspFunction_deltaOverQ_zero_aux`, `cuspFunction_qOverDelta_zero_aux`, `qOverDelta`, `deltaOverQ`]
- **Used by**: `qOverDelta_cuspFunction_analyticAt`
- **Visibility**: private
- **Lines**: 323–328 (5-line proof)
- **Notes**: none

### `lemma deltaOverQ_inv_analyticAt_aux`
- **Type**: `AnalyticAt ℂ (fun q ↦ (cuspFunction 1 deltaOverQ q)⁻¹) 0`
- **What**: The reciprocal of the cusp function of Δ/q is analytic at 0 (permissible since the value there is 1 ≠ 0).
- **How**: mathlib's `AnalyticAt.inv` applied to `deltaOverQ_analyticAt_aux` with non-vanishing from `cuspFunction_deltaOverQ_zero_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`deltaOverQ_analyticAt_aux`, `cuspFunction_deltaOverQ_zero_aux`, `deltaOverQ`]
- **Used by**: `qOverDelta_cuspFunction_analyticAt`
- **Visibility**: private
- **Lines**: 330–332 (2-line proof)
- **Notes**: none

### `lemma qOverDelta_cuspFunction_analyticAt`
- **Type**: `AnalyticAt ℂ (cuspFunction 1 qOverDelta) 0`
- **What**: The cusp function of q/Δ is analytic at q = 0.
- **How**: Transfers `deltaOverQ_inv_analyticAt_aux` along the function identity `cuspFunction_qOverDelta_eq_inv_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`cuspFunction_qOverDelta_eq_inv_aux`, `deltaOverQ_inv_analyticAt_aux`, `qOverDelta`]
- **Used by**: `integralDeltaOverQ_mul_qExpansion_qOverDelta`, `qj_isIntegralPowerSeries_aux`, `qj_qExpansion_coeff_zero`
- **Visibility**: public
- **Lines**: 334–335 (1-line proof)
- **Notes**: none

### `lemma E4_pow_three_isModularForm_aux`
- **Type**: `∃ f : ModularForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) 12, (f : ℍ → ℂ) = E4 ^ 3`
- **What**: E₄³ (as a function) is realized by an actual weight-12 modular form, namely the triple product E₄·(E₄·E₄).
- **How**: Witness `E4.mul (E4.mul E4)` with coercion computed by mathlib's `ModularForm.coe_mul` and `pow_three`.
- **Hypotheses**: none.
- **Uses from project**: [`E4`]
- **Used by**: `E4_pow_three_cuspFunction_analyticAt`
- **Visibility**: private
- **Lines**: 337–342 (5-line proof)
- **Notes**: none

### `lemma E4_pow_three_cuspFunction_analyticAt`
- **Type**: `AnalyticAt ℂ (cuspFunction 1 (E4 ^ 3)) 0`
- **What**: The cusp function of E₄³ is analytic at q = 0 (it is a modular form, hence bounded and analytic at the cusp).
- **How**: mathlib's `ModularFormClass.analyticAt_cuspFunction_zero` applied to the modular-form witness from `E4_pow_three_isModularForm_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`E4_pow_three_isModularForm_aux`, `E4`]
- **Used by**: `qj_isIntegralPowerSeries_aux`, `qj_qExpansion_coeff_zero`
- **Visibility**: public
- **Lines**: 344–347 (3-line proof)
- **Notes**: none

### `lemma integralDeltaOverQ_mul_qExpansion_qOverDelta`
- **Type**: `(coeToComplexPowerSeries.ringHom ℤ) integralDeltaOverQ * qExpansion 1 qOverDelta = 1`
- **What**: The q-expansions of Δ/q and q/Δ are multiplicative inverses in ℂ⟦q⟧.
- **How**: Converts the product of q-expansions into the q-expansion of the pointwise product via mathlib's `qExpansion_mul` (with both analyticity facts), notes (Δ/q)·(q/Δ) = 1 pointwise from `deltaOverQ_ne_zero`, and finishes with `qExpansion_one`.
- **Hypotheses**: none.
- **Uses from project**: [`coeTo_integralDeltaOverQ`, `deltaOverQ_analyticAt_aux`, `qOverDelta_cuspFunction_analyticAt`, `deltaOverQ_ne_zero`, `qOverDelta`, `deltaOverQ`, `integralDeltaOverQ`, `coeToComplexPowerSeries.ringHom`]
- **Used by**: `qOverDelta_isIntegralPowerSeries_aux`
- **Visibility**: public
- **Lines**: 349–356 (7-line proof)
- **Notes**: none

### `lemma qOverDelta_isIntegralPowerSeries_aux`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 qOverDelta)`
- **What**: The q-expansion of q/Δ has integer coefficients — it is the inverse of an integral series with unit constant term.
- **How**: Takes the ℤ⟦q⟧-inverse u⁻¹ from `integralDeltaOverQ_isUnit_aux` as witness; its complexification times the complexification of integralDeltaOverQ is 1, and cancelling against `integralDeltaOverQ_mul_qExpansion_qOverDelta` identifies it with qExpansion(q/Δ).
- **Hypotheses**: none.
- **Uses from project**: [`IsIntegralPowerSeries`, `integralDeltaOverQ_isUnit_aux`, `coeToComplexPowerSeries.ringHom`, `integralDeltaOverQ`, `integralDeltaOverQ_mul_qExpansion_qOverDelta`, `qOverDelta`]
- **Used by**: `qj_isIntegralPowerSeries_aux`
- **Visibility**: private
- **Lines**: 358–382 (24-line proof)
- **Notes**: none

### `lemma qj_isIntegralPowerSeries_aux`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 (E4 ^ 3 * qOverDelta))`
- **What**: The q-expansion of E₄³·(q/Δ) has integer coefficients.
- **How**: Splits the q-expansion of the product with mathlib's `qExpansion_mul` and multiplies integralities with the project's `hasCoeffsIn_mul`, using `E4_pow_three_isIntegralPowerSeries` (from Deltaqexpansions) and `qOverDelta_isIntegralPowerSeries_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`E4_pow_three_cuspFunction_analyticAt`, `qOverDelta_cuspFunction_analyticAt`, `hasCoeffsIn_mul` (IntegralPowerSeries), `E4_pow_three_isIntegralPowerSeries` (Deltaqexpansions), `qOverDelta_isIntegralPowerSeries_aux`, `E4`, `qOverDelta`, `IsIntegralPowerSeries`]
- **Used by**: `qj_isIntegralPowerSeries`
- **Visibility**: private
- **Lines**: 384–387 (3-line proof)
- **Notes**: none

### `theorem qj_isIntegralPowerSeries`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 qj)`
- **What**: Main integrality theorem: the q-expansion of q·j has integer coefficients (so j has an integral q-expansion with a simple pole: j = q⁻¹ + 744 + 196884q + …).
- **How**: Rewrites qj as E₄³·(q/Δ) via `E4_pow_three_mul_qOverDelta_eq_qj` and applies `qj_isIntegralPowerSeries_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`E4_pow_three_mul_qOverDelta_eq_qj`, `qj_isIntegralPowerSeries_aux`, `qj`, `IsIntegralPowerSeries`]
- **Used by**: `qjCoeffs`, `qj_coeff_cast_aux`, `j_hasIntegralQExpansion`, `j_laurentQExpansion_isIntegral`
- **Visibility**: public
- **Lines**: 389–390 (1-line proof)
- **Notes**: none

### `def qjCoeffs`
- **Type**: `qjCoeffs : ℕ → ℤ` (`:= fun n ↦ (toIntegralPowerSeries qj_isIntegralPowerSeries).coeff n`)
- **What**: The integer coefficients c(n) of the q-expansion of q·j (so c(0) = 1, c(1) = 744, c(2) = 196884, …).
- **How**: Coefficient extraction from the integral lift of qExpansion(qj).
- **Hypotheses**: none.
- **Uses from project**: [`toIntegralPowerSeries`, `qj_isIntegralPowerSeries`, `qj`]
- **Used by**: `qj_coeff_cast_aux`, `infSumQj_summable_aux`, `infSumQj_eq_qj_aux`, `qj_eq_tsum_aux`, `qj_div_qParam_eq_series_div_qParam_aux`, `qjCoeffs_tsum_div_qParam_aux`, `j_eq_qjCoeffs_tsum`, `j_laurentQExpansion_isIntegral`
- **Visibility**: public
- **Lines**: 393 (1 line)
- **Notes**: none

### `lemma qj_coeff_cast_aux`
- **Type**: `(n : ℕ) : ((qjCoeffs n : ℤ) : ℂ) = (qExpansion 1 qj).coeff n`
- **What**: The complex q-expansion coefficient of qj is the cast of the integer coefficient qjCoeffs n.
- **How**: Coefficient-wise instance of the round-trip identity `coeTo_of_toIntegralPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: [`qjCoeffs`, `coeTo_of_toIntegralPowerSeries`, `qj_isIntegralPowerSeries`, `qj`]
- **Used by**: `infSumQj_summable_aux`, `infSumQj_eq_qj_aux`, `qj_eq_tsum_aux`
- **Visibility**: private
- **Lines**: 395–397 (term-mode, 1-line proof)
- **Notes**: none

### `def infSumQj_aux`
- **Type**: `infSumQj_aux : ℍ → ℂ` (`:= fun z ↦ ∑' n, (qExpansion 1 qj).coeff n * exp(2πiz)^n`)
- **What**: The tsum of the q-expansion of qj, as a function on ℍ (an intermediate object shown equal to qj).
- **How**: Definition as a tsum; no proof content.
- **Hypotheses**: none.
- **Uses from project**: [`qj`]
- **Used by**: `infSumQj_eq_qj_aux`, `qj_eq_tsum_aux`
- **Visibility**: private
- **Lines**: 399–400 (2 lines)
- **Notes**: none

### `lemma qj_vadd_one_aux`
- **Type**: `(τ : ℍ) : qj ((1 : ℝ) +ᵥ τ) = qj τ`
- **What**: qj is invariant under the translation τ ↦ τ + 1 (both j and the exponential factor e^{2πiτ} are 1-periodic).
- **How**: Periodicity of E₄ and Δ from mathlib's `SlashInvariantForm.vAdd_apply_of_mem_strictPeriods` gives j(τ+1) = j(τ); the exponential factor is handled by `Complex.exp_add` and `Complex.exp_two_pi_mul_I` (e^{2πi} = 1).
- **Hypotheses**: none.
- **Uses from project**: [`qj`, `E4`, `Delta`, `j`]
- **Used by**: `qj_periodic`
- **Visibility**: private
- **Lines**: 402–424 (22-line proof)
- **Notes**: none

### `lemma qj_periodic`
- **Type**: `Periodic (qj ∘ UpperHalfPlane.ofComplex) 1`
- **What**: The extension of qj to ℂ through `ofComplex` is 1-periodic — the hypothesis needed for q-expansion machinery.
- **How**: For Im w > 0 reduces to `qj_vadd_one_aux` via `UpperHalfPlane.ofComplex_apply_of_im_pos`; for Im w ≤ 0 both sides use the junk value at `ofComplex` (`ofComplex_apply_of_im_nonpos`).
- **Hypotheses**: none.
- **Uses from project**: [`qj_vadd_one_aux`, `qj`]
- **Used by**: `hasSum_qExpansion_qj`, `qj_cuspFunction_differentiableOn_aux`
- **Visibility**: public
- **Lines**: 426–443 (17-line proof)
- **Notes**: none

### `lemma qj_differentiableAt_of_im_pos`
- **Type**: `∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (qj ∘ UpperHalfPlane.ofComplex) z`
- **What**: The complex extension of qj is holomorphic at every point of the open upper half-plane.
- **How**: The exponential factor is entire; E₄ and Δ are MDifferentiable (`ModularFormClass.holo`) hence differentiable through `UpperHalfPlane.mdifferentiableAt_iff`; the quotient j = E₄³/Δ is differentiable since Δ ≠ 0 (`Δ_ne_zero`); local agreement of the composite with the entire exponential handled by `Filter.EventuallyEq` congruence on the open set Im > 0.
- **Hypotheses**: 0 < Im z.
- **Uses from project**: [`qj`, `j`, `E4`, `Delta`, `Δ_ne_zero`, `Delta_apply`]
- **Used by**: `qj_mdifferentiable`
- **Visibility**: public
- **Lines**: 445–470 (25-line proof)
- **Notes**: none

### `lemma qj_mdifferentiable`
- **Type**: `MDiff qj`
- **What**: qj is MDifferentiable as a function on the upper half-plane manifold.
- **How**: mathlib's `UpperHalfPlane.mdifferentiable_iff` reduces to differentiability on {Im > 0}, supplied by `qj_differentiableAt_of_im_pos`.
- **Hypotheses**: none.
- **Uses from project**: [`qj_differentiableAt_of_im_pos`, `qj`]
- **Used by**: `hasSum_qExpansion_qj`, `qj_cuspFunction_differentiableOn_aux`
- **Visibility**: public
- **Lines**: 472–475 (3-line proof)
- **Notes**: none

### `lemma e4_isBoundedAtImInfty_aux`
- **Type**: `IsBoundedAtImInfty E4`
- **What**: E₄ is bounded at i∞ (as any modular form is).
- **How**: mathlib's `ModularFormClass.bdd_at_infty` by simp.
- **Hypotheses**: none.
- **Uses from project**: [`E4`]
- **Used by**: `E4_pow_three_isBoundedAtImInfty_aux`
- **Visibility**: private
- **Lines**: 477–478 (1-line proof)
- **Notes**: none

### `lemma E4_pow_three_isBoundedAtImInfty_aux`
- **Type**: `IsBoundedAtImInfty (fun z : ℍ ↦ E4 z ^ 3)`
- **What**: E₄³ is bounded at i∞.
- **How**: Two applications of `BoundedAtFilter.mul` to `e4_isBoundedAtImInfty_aux`, rewriting the cube as an iterated product.
- **Hypotheses**: none.
- **Uses from project**: [`e4_isBoundedAtImInfty_aux`, `E4`]
- **Used by**: `qj_isBoundedAtImInfty`
- **Visibility**: private
- **Lines**: 480–488 (8-line proof)
- **Notes**: none

### `lemma qj_isBoundedAtImInfty`
- **Type**: `IsBoundedAtImInfty qj`
- **What**: qj is bounded at i∞ (its cusp value is 1, matching the removal of j's pole).
- **How**: q/Δ → 1 (`qOverDelta_tendsto_atImInfty`) so q/Δ = (q/Δ − 1) + 1 is bounded via `ZeroAtFilter.boundedAtFilter` and `const_boundedAtFilter`; multiplied by the bounded E₄³ (`E4_pow_three_isBoundedAtImInfty_aux`) and identified with qj via `E4_pow_three_mul_qOverDelta_eq_qj`.
- **Hypotheses**: none.
- **Uses from project**: [`qOverDelta_tendsto_atImInfty`, `E4_pow_three_isBoundedAtImInfty_aux`, `E4_pow_three_mul_qOverDelta_eq_qj`, `qj`, `qOverDelta`, `E4`]
- **Used by**: `hasSum_qExpansion_qj`, `qj_cuspFunction_differentiableOn_aux`
- **Visibility**: public
- **Lines**: 490–507 (17-line proof)
- **Notes**: none

### `lemma hasSum_qExpansion_qj`
- **Type**: `{τ : ℍ} : HasSum (fun m ↦ (qExpansion 1 qj).coeff m • 𝕢 1 τ ^ m) (qj τ)`
- **What**: The q-expansion of qj converges to qj at every point of ℍ.
- **How**: mathlib's `UpperHalfPlane.hasSum_qExpansion` with the three hypotheses `qj_periodic`, `qj_mdifferentiable`, `qj_isBoundedAtImInfty`.
- **Hypotheses**: none.
- **Uses from project**: [`qj_periodic`, `qj_mdifferentiable`, `qj_isBoundedAtImInfty`, `qj`]
- **Used by**: `infSumQj_summable_aux`, `infSumQj_eq_qj_aux`
- **Visibility**: public
- **Lines**: 509–512 (2-line proof)
- **Notes**: none

### `lemma infSumQj_summable_aux`
- **Type**: `{z : ℍ} : Summable (fun n ↦ (qjCoeffs n) * cexp (2 * π * Complex.I * z) ^ n)`
- **What**: The integer-coefficient q-series of qj is summable at each z ∈ ℍ.
- **How**: Summability of the complex-coefficient series from `hasSum_qExpansion_qj`, transported term-by-term along the cast identity `qj_coeff_cast_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`hasSum_qExpansion_qj`, `qj_coeff_cast_aux`, `qjCoeffs`, `qj`]
- **Used by**: `qjCoeffs_tsum_div_qParam_aux`
- **Visibility**: private
- **Lines**: 514–530 (16-line proof)
- **Notes**: none

### `lemma infSumQj_eq_qj_aux`
- **Type**: `infSumQj_aux = qj`
- **What**: The tsum of the q-expansion of qj equals qj as a function on ℍ.
- **How**: `HasSum.tsum_eq` on `hasSum_qExpansion_qj`, with coefficients recast to integers by `qj_coeff_cast_aux` and `tsum_congr`.
- **Hypotheses**: none.
- **Uses from project**: [`infSumQj_aux`, `hasSum_qExpansion_qj`, `qj_coeff_cast_aux`, `qjCoeffs`, `qj`]
- **Used by**: `qj_eq_tsum_aux`
- **Visibility**: private
- **Lines**: 532–555 (23-line proof)
- **Notes**: none

### `lemma qj_eq_tsum_aux`
- **Type**: `∀ z : ℍ, qj z = ∑' n, (qjCoeffs n) * cexp (2 * π * Complex.I * z) ^ n`
- **What**: Pointwise q-series representation of qj with integer coefficients.
- **How**: Chains `infSumQj_eq_qj_aux` with the `tsum_congr` recasting via `qj_coeff_cast_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`infSumQj_eq_qj_aux`, `infSumQj_aux`, `qj_coeff_cast_aux`, `qjCoeffs`, `qj`]
- **Used by**: `qj_div_qParam_eq_series_div_qParam_aux`
- **Visibility**: private
- **Lines**: 557–567 (10-line proof)
- **Notes**: none

### `lemma qj_div_qParam_eq_series_div_qParam_aux`
- **Type**: `(z : ℍ) : qj z / cexp (2πiz) = (∑' n, (qjCoeffs n) * cexp (2πiz) ^ n) / cexp (2πiz)`
- **What**: Divides both sides of the qj series representation by the q-parameter.
- **How**: `congrArg` of division applied to `qj_eq_tsum_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`qj_eq_tsum_aux`, `qjCoeffs`, `qj`]
- **Used by**: `j_eq_qjCoeffs_tsum`
- **Visibility**: private
- **Lines**: 569–573 (1-line proof)
- **Notes**: none

### `lemma qj_div_qParam_eq_j_aux`
- **Type**: `(z : ℍ) : qj z / cexp (2 * π * Complex.I * z) = j z`
- **What**: Dividing qj by q recovers j.
- **How**: Unfolds `qj` = q·j and cancels the nonzero exponential by simp.
- **Hypotheses**: none.
- **Uses from project**: [`qj`, `j`]
- **Used by**: `j_eq_qjCoeffs_tsum`
- **Visibility**: private
- **Lines**: 575–577 (1-line proof)
- **Notes**: none

### `lemma qjCoeffs_tsum_div_qParam_aux`
- **Type**: `(z : ℍ) : (∑' n, (qjCoeffs n) * q ^ n) / q = qjCoeffs 0 / q + ∑' n, (qjCoeffs (n+1)) * q ^ n` where `q = cexp (2πiz)`
- **What**: Splitting the divided q-series into the polar part c(0)/q plus the regular tail Σc(n+1)qⁿ.
- **How**: Peels the 0-th term with `Summable.tsum_eq_zero_add` (from `infSumQj_summable_aux`), distributes division with `add_div` and `tsum_div_const`, and cancels one power of q per term with `pow_succ`/`field_simp`.
- **Hypotheses**: none.
- **Uses from project**: [`infSumQj_summable_aux`, `qjCoeffs`]
- **Used by**: `j_eq_qjCoeffs_tsum`
- **Visibility**: private
- **Lines**: 579–603 (24-line proof)
- **Notes**: none

### `theorem j_eq_qjCoeffs_tsum`
- **Type**: `(z : ℍ) : j z = qjCoeffs 0 / cexp (2πiz) + ∑' n, qjCoeffs (n + 1) * cexp (2πiz) ^ n`
- **What**: The convergent Laurent-type q-series representation of the j-function: j = c(0)q⁻¹ + Σ c(n+1)qⁿ with integer coefficients.
- **How**: Combines `qj_div_qParam_eq_j_aux` (qj/q = j), `qj_div_qParam_eq_series_div_qParam_aux`, and the series splitting `qjCoeffs_tsum_div_qParam_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`qj_div_qParam_eq_j_aux`, `qjCoeffs_tsum_div_qParam_aux`, `qj_div_qParam_eq_series_div_qParam_aux`, `j`, `qjCoeffs`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 606–610 (3-line proof)
- **Notes**: none

### `lemma qj_qExpansion_coeff_zero`
- **Type**: `(qExpansion 1 qj).coeff 0 = 1`
- **What**: The constant term of the q-expansion of qj is 1 — equivalently j's Laurent expansion starts with exactly q⁻¹.
- **How**: Factors qExpansion(qj) = qExpansion(E₄³)·qExpansion(q/Δ) via `qExpansion_mul` and `E4_pow_three_mul_qOverDelta_eq_qj`; the constant term of qExpansion(E₄)³ is 1 by mathlib's `EisensteinSeries.E_qExpansion_coeff_zero` and `qExpansion_of_pow`, and that of q/Δ is 1 by `cuspFunction_qOverDelta_zero_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`qj`, `E4_pow_three_mul_qOverDelta_eq_qj`, `E4_pow_three_cuspFunction_analyticAt`, `qOverDelta_cuspFunction_analyticAt`, `cuspFunction_qOverDelta_zero_aux`, `E4`, `qOverDelta`]
- **Used by**: `j_cuspFunction_not_analyticAt`, `j_poleOrder`
- **Visibility**: public
- **Lines**: 613–637 (24-line proof)
- **Notes**: none

### `theorem Delta_hasIntegralQExpansion`
- **Type**: `HasIntegralQExpansion 1 Delta`
- **What**: Δ satisfies the project's `HasIntegralQExpansion` predicate (some q-power multiple has an integral power-series expansion; here with shift 0).
- **How**: Direct application of the project bridge `HasIntegralQExpansion_ofPowerSeries` to `Delta_isIntegralPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: [`HasIntegralQExpansion`, `HasIntegralQExpansion_ofPowerSeries` (IntegralPowerSeries.HasIntegralQExpansion), `Delta_isIntegralPowerSeries` (Deltaqexpansions), `Delta`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 639–640 (term-mode, 1 line)
- **Notes**: none

### `theorem E4_hasIntegralQExpansion`
- **Type**: `HasIntegralQExpansion 1 E4`
- **What**: E₄ has an integral q-expansion in the project's sense.
- **How**: `HasIntegralQExpansion_ofPowerSeries` applied to `E4_isIntegralPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: [`HasIntegralQExpansion_ofPowerSeries`, `E4_isIntegralPowerSeries` (Deltaqexpansions), `E4`, `HasIntegralQExpansion`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 642–643 (term-mode, 1 line)
- **Notes**: none

### `theorem E6_hasIntegralQExpansion`
- **Type**: `HasIntegralQExpansion 1 E6`
- **What**: E₆ has an integral q-expansion in the project's sense.
- **How**: `HasIntegralQExpansion_ofPowerSeries` applied to `E6_isIntegralPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: [`HasIntegralQExpansion_ofPowerSeries`, `E6_isIntegralPowerSeries` (Deltaqexpansions), `E6`, `HasIntegralQExpansion`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 645–646 (term-mode, 1 line)
- **Notes**: none

### `theorem j_hasIntegralQExpansion`
- **Type**: `HasIntegralQExpansion 1 j`
- **What**: The j-function has an integral q-expansion after multiplication by q¹ — the existential form of qj's integrality.
- **How**: Witness n = 1 in the `HasIntegralQExpansion` existential; q¹·j = qj, whose expansion is integral by `qj_isIntegralPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: [`HasIntegralQExpansion`, `qj`, `qj_isIntegralPowerSeries`, `j`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 648–650 (2-line proof)
- **Notes**: none

### `lemma qj_cuspFunction_differentiableOn_aux`
- **Type**: `DifferentiableOn ℂ (cuspFunction 1 qj) (Metric.ball 0 1)`
- **What**: The cusp function of qj is holomorphic on the open unit q-disc.
- **How**: mathlib's `UpperHalfPlane.differentiableOn_cuspFunction_ball` with `qj_periodic`, `qj_mdifferentiable`, `qj_isBoundedAtImInfty`.
- **Hypotheses**: none.
- **Uses from project**: [`qj_periodic`, `qj_mdifferentiable`, `qj_isBoundedAtImInfty`, `qj`]
- **Used by**: `qj_cuspFunction_analyticAt`
- **Visibility**: private
- **Lines**: 654–657 (term-mode, 2 lines)
- **Notes**: declared after the `end` of the noncomputable section (lines 654+ sit outside it)

### `lemma qj_cuspFunction_analyticAt`
- **Type**: `AnalyticAt ℂ (cuspFunction 1 qj) 0`
- **What**: The cusp function of qj is analytic at q = 0.
- **How**: mathlib's `DifferentiableOn.analyticAt` on the unit-ball differentiability `qj_cuspFunction_differentiableOn_aux` with the ball as a neighborhood of 0.
- **Hypotheses**: none.
- **Uses from project**: [`qj_cuspFunction_differentiableOn_aux`, `qj`]
- **Used by**: `j_cuspFunction_meromorphicAt`, `j_cuspFunction_not_analyticAt`, `j_poleOrder`
- **Visibility**: public
- **Lines**: 659–662 (term-mode, 3 lines)
- **Notes**: none

### `lemma inv_mul_cuspFunction_qj_eq_j_aux`
- **Type**: `(fun q : ℂ ↦ q⁻¹ * cuspFunction 1 qj q) =ᶠ[nhdsWithin 0 {0}ᶜ] cuspFunction 1 j`
- **What**: On a punctured neighborhood of q = 0, the cusp function of j equals q⁻¹ times the cusp function of qj — the analytic statement that j has at worst a simple pole with residue series qj.
- **How**: For each q ≠ 0 in the unit disc, sets τ = invQParam(q) (`Periodic.im_invQParam_pos_of_norm_lt_one`), evaluates both cusp functions off 0 with `Periodic.cuspFunction_eq_of_nonzero`, and cancels q⁻¹·(q·j(τ)) = j(τ) using `Periodic.qParam_right_inv`.
- **Hypotheses**: none.
- **Uses from project**: [`qj`, `j`]
- **Used by**: `j_cuspFunction_meromorphicAt`, `j_poleOrder`
- **Visibility**: private
- **Lines**: 664–692 (28-line proof)
- **Notes**: none

### `lemma j_cuspFunction_meromorphicAt`
- **Type**: `MeromorphicAt (cuspFunction 1 j) (0 : ℂ)`
- **What**: The cusp function of j is meromorphic at q = 0.
- **How**: q⁻¹ is meromorphic (`MeromorphicAt.id.inv`), qj's cusp function is analytic hence meromorphic (`qj_cuspFunction_analyticAt`), and their product agrees with cuspFunction j near 0 by `inv_mul_cuspFunction_qj_eq_j_aux`, transferred with `MeromorphicAt.congr`.
- **Hypotheses**: none.
- **Uses from project**: [`qj_cuspFunction_analyticAt`, `inv_mul_cuspFunction_qj_eq_j_aux`, `j`, `qj`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 694–696 (2-line proof)
- **Notes**: none

### `lemma j_cuspFunction_not_analyticAt`
- **Type**: `¬ AnalyticAt ℂ (cuspFunction 1 j) 0`
- **What**: The cusp function of j is genuinely singular at q = 0 (j really has a pole at i∞, it is not a removable singularity).
- **How**: If it were analytic, q·cuspFunction(j) would tend to 0 as q → 0; but q·cuspFunction(j) agrees with cuspFunction(qj) on the punctured disc by the project's `cuspFunction_qpow_mul_eq` (LaurentQExpansion), which tends to 1 by `qj_qExpansion_coeff_zero` and continuity from `qj_cuspFunction_analyticAt` — contradiction via `tendsto_nhds_unique`.
- **Hypotheses**: none.
- **Uses from project**: [`qj_qExpansion_coeff_zero`, `qj_cuspFunction_analyticAt`, `cuspFunction_qpow_mul_eq` (LaurentQExpansion), `qj`, `j`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 698–726 (28-line proof)
- **Notes**: none

### `lemma j_poleOrder`
- **Type**: `poleOrder 1 j = 1`
- **What**: The j-function has a pole of order exactly 1 at the cusp i∞ (in the project's `poleOrder` framework on the q-disc).
- **How**: Computes the meromorphic order of cuspFunction j at 0 as −1: it factors as F·q⁻¹ with F = cuspFunction qj analytic and F(0) = 1 ≠ 0 (`qj_qExpansion_coeff_zero`), so by mathlib's `meromorphicOrderAt_mul_of_ne_zero` and `meromorphicOrderAt_inv` the order is 0 + (−1); the transfer along `inv_mul_cuspFunction_qj_eq_j_aux` uses `meromorphicOrderAt_congr`, and `poleOrder` unfolds to the negated order.
- **Hypotheses**: none.
- **Uses from project**: [`poleOrder` (LaurentQExpansion), `qj_qExpansion_coeff_zero`, `inv_mul_cuspFunction_qj_eq_j_aux`, `qj_cuspFunction_analyticAt`, `qj`, `j`]
- **Used by**: `j_poleRemoved`, `j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one`, `j_laurentQExpansion_isIntegral`
- **Visibility**: public
- **Lines**: 728–756 (28-line proof)
- **Notes**: none

### `lemma j_poleRemoved`
- **Type**: `poleRemoved 1 j = qj`
- **What**: The project's canonical pole-removal q^{poleOrder}·j of j is exactly qj.
- **How**: Unfolds `UpperHalfPlane.poleRemoved` and substitutes `j_poleOrder` = 1, so q¹·j = qj definitionally (via `Periodic.qParam` and `pow_one`).
- **Hypotheses**: none.
- **Uses from project**: [`poleRemoved` (LaurentQExpansion), `qj`, `j`, `j_poleOrder`]
- **Used by**: `j_to_qExpansion`
- **Visibility**: public
- **Lines**: 758–760 (2-line proof)
- **Notes**: none

### `lemma j_to_qExpansion`
- **Type**: `to_qExpansion 1 j = qExpansion 1 qj`
- **What**: The project's regularized q-expansion of j (expansion of its pole-removal) is the q-expansion of qj.
- **How**: Unfolds `UpperHalfPlane.to_qExpansion` and rewrites with `j_poleRemoved`.
- **Hypotheses**: none.
- **Uses from project**: [`to_qExpansion` (LaurentQExpansion), `j_poleRemoved`, `j`, `qj`]
- **Used by**: `j_laurentQExpansion_isIntegral`
- **Visibility**: public
- **Lines**: 762–763 (1-line proof)
- **Notes**: none

### `theorem j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one`
- **Type**: `{n : ℤ} (hn : n < -1) : (laurentqExpansion 1 j).coeff n = 0`
- **What**: The Laurent q-expansion of j has no coefficients below degree −1 (the pole is simple).
- **How**: Since poleOrder = 1 (`j_poleOrder`), n < −1 means n < −poleOrder, and the project's `laurentqExpansion.coeff_eq_zero_of_lt` kills the coefficient.
- **Hypotheses**: n < −1.
- **Uses from project**: [`laurentqExpansion` (LaurentQExpansion), `j_poleOrder`, `laurentqExpansion.coeff_eq_zero_of_lt`, `poleOrder`, `j`]
- **Used by**: `j_laurentQExpansion_isIntegral`
- **Visibility**: public
- **Lines**: 765–768 (3-line proof)
- **Notes**: none

### `theorem j_laurentQExpansion_isIntegral`
- **Type**: `{n : ℤ} : ∃ m : ℤ, (laurentqExpansion 1 j).coeff n = m`
- **What**: Every Laurent q-expansion coefficient of j is an integer: 0 below degree −1, and qjCoeffs(n+1) in degrees ≥ −1.
- **How**: Case split on n < −1 (zero by `j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one`) versus n ≥ −1, where the project's `laurentqExpansion.coeff_of_geq` expresses the coefficient through `to_qExpansion`, rewritten to qExpansion(qj) by `j_to_qExpansion`, whose coefficients are the integers qjCoeffs via `coeTo_of_toIntegralPowerSeries qj_isIntegralPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: [`j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one`, `qjCoeffs`, `j_poleOrder`, `laurentqExpansion.coeff_of_geq` (LaurentQExpansion), `j_to_qExpansion`, `coeTo_of_toIntegralPowerSeries`, `qj_isIntegralPowerSeries`, `to_qExpansion`, `laurentqExpansion`, `poleOrder`, `qj`, `j`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 770–787 (17-line proof)
- **Notes**: none

### File Summary
- Total declarations: 69 (8 defs [j, deltaOverQ, deltaShiftedQSeries, integralDeltaOverQ, qOverDelta, qj, qjCoeffs, private infSumQj_aux], 60 lemmas/theorems, 0 instances, 1 tactic/meta decl [local notation 𝕢])
- Key API (used by 3+ others): [`j`, `qj`, `deltaOverQ`, `qOverDelta`, `deltaShiftedQSeries`, `qjCoeffs`, `qj_isIntegralPowerSeries`, `qj_coeff_cast_aux`, `deltaOverQ_eq_qParam_inv_mul_Delta`, `deltaShiftedQSeries_eq_deltaOverQ`, `E4_pow_three_mul_qOverDelta_eq_qj`, `qOverDelta_cuspFunction_analyticAt`, `qj_cuspFunction_analyticAt`, `qj_qExpansion_coeff_zero` (2 direct + statement reuse), `j_poleOrder`, `integralDeltaOverQ` (5 users)]
- Unused declarations (not used by anything in this file): [`j_modularGroup_smul`, `j_eq_qjCoeffs_tsum`, `Delta_hasIntegralQExpansion`, `E4_hasIntegralQExpansion`, `E6_hasIntegralQExpansion`, `j_hasIntegralQExpansion`, `j_cuspFunction_meromorphicAt`, `j_cuspFunction_not_analyticAt`, `j_laurentQExpansion_isIntegral`] — all are public API endpoints consumed by downstream files (e.g. jLevelN.lean, jInvariantLink.lean, Cox/*)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [] (largest: `deltaShiftedQSeries_analyticAt_aux` 28 lines, `inv_mul_cuspFunction_qj_eq_j_aux` 28 lines, `j_cuspFunction_not_analyticAt` 28 lines, `j_poleOrder` 28 lines)
