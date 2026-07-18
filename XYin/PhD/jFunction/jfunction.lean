/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion

import XYin.PhD.IntegralPowerSeries.IntegralPowerSeries
import XYin.PhD.jFunction.Deltaqexpansions
import XYin.PhD.LaurentQExpansion.LaurentQExpansion

/-!
# The modular `j`-function and its Laurent q-expansion

This file defines the classical modular function `j = E4 ^ 3 / Delta`. It constructs the
holomorphic regularization `qj`, proves that its q-expansion has integral coefficients and
constant coefficient one, and deduces the pole order and integrality of the Laurent q-expansion
of `j` at infinity.

## Main definitions

* `j`: the classical modular function.
* `qj`: the regularized function obtained by multiplying `j` by the q-parameter.
* `qjCoeffs`: the integral coefficients of the q-expansion of `qj`.

## Main results

* `qj_isIntegralPowerSeries`: the q-expansion of `qj` has integral coefficients.
* `j_eq_qjCoeffs_tsum`: the convergent q-series reconstruction of `j`.
* `j_poleOrder`: the function `j` has a simple pole at infinity.
* `j_laurentQExpansion_isIntegral`: every Laurent q-expansion coefficient of `j` is integral.
-/

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups PowerSeries
  SlashInvariantFormClass Real Function IntegralPowerSeries
open scoped Manifold

local notation "𝕢" => Periodic.qParam

noncomputable section

private lemma cuspFunction_apply_zero_of_tendsto {f : ℍ → ℂ} {a : ℂ}
    (hf : Tendsto f atImInfty (nhds a)) : cuspFunction 1 f 0 = a := by
  have hcomp : Tendsto ((f ∘ UpperHalfPlane.ofComplex) ∘ Periodic.invQParam (1 : ℝ))
      (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds a) :=
    hf.comp (tendsto_comap_im_ofComplex.comp (Periodic.invQParam_tendsto (by norm_num)))
  simpa [cuspFunction, Periodic.cuspFunction, comp_def] using hcomp.limUnder_eq

/-- The classical modular invariant `j = E4 ^ 3 / Delta`. -/
def j : ℍ → ℂ := fun τ ↦ (E4 τ) ^ 3 / Delta τ

/-- The modular invariant `j` is invariant under the weight-zero slash action of `SL₂(ℤ)`. -/
lemma j_slash_invariant (γ : SL(2, ℤ)) : j ∣[(0 : ℤ)] γ = j := by
  ext z
  rw [slash_action_eq'_iff, j, j]
  have h1 := congrFun (E4.slash_action_eq' γ (by refine
      (Subgroup.mem_map_iff_mem (Matrix.SpecialLinearGroup.mapGL_injective)).mpr (by apply
      CongruenceSubgroup.mem_Gamma_one))) z
  have h2 := congrFun (Delta.slash_action_eq' γ (by refine
      (Subgroup.mem_map_iff_mem (Matrix.SpecialLinearGroup.mapGL_injective)).mpr (by apply
      CongruenceSubgroup.mem_Gamma_one))) z
  rw [← ModularForm.SL_slash] at h1 h2
  simp only [ModularForm.slash_action_eq'_iff, SlashInvariantForm.toFun_eq_coe,
    toSlashInvariantForm_coe, Fin.isValue] at h1
  rw [ModularForm.slash_action_eq'_iff, CuspForm_apply, CuspForm_apply] at h2
  rw [h1, h2]
  ring_nf
  have h3 := pow_ne_zero 12 (denom_ne_zero γ z)
  rw [ModularGroup.denom_apply] at h3
  rw [← zpow_natCast, ← zpow_mul]
  ring_nf
  nth_rw 2 [mul_comm]
  rw [← mul_assoc]
  nth_rw 3 [mul_comm]
  rw [Complex.mul_inv_cancel]
  · simp
  · exact h3

/-- The modular invariant `j` is unchanged by the action of `SL₂(ℤ)`. -/
lemma j_modularGroup_smul (γ : SL(2, ℤ)) (z : ℍ) : j (γ • z) = j z := by
  have h := congrFun (j_slash_invariant γ) z
  simpa only [SL_slash_apply, neg_zero, zpow_zero, mul_one] using h

/-- The discriminant divided by the q-parameter, expressed as its infinite product. -/
def deltaOverQ : ℍ → ℂ :=
  fun z ↦ ∏' (n : ℕ), (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24

/-- The infinite product `deltaOverQ` is the discriminant divided by the q-parameter. -/
lemma deltaOverQ_eq_qParam_inv_mul_Delta :
    deltaOverQ = (fun z ↦ 1 / cexp (2 * π * Complex.I * z) : ℍ → ℂ) * Delta := by
  ext z
  simp [deltaOverQ, Delta_apply, Δ, Pi.mul_apply, mul_assoc]

private lemma deltaOverQ_eq_qParam_inv_smul_Delta (z : ℍ) :
    deltaOverQ z = (𝕢 1 (z : ℂ))⁻¹ • Delta z := by
  simpa [Periodic.qParam, one_div, Pi.mul_apply, smul_eq_mul] using
    congrFun deltaOverQ_eq_qParam_inv_mul_Delta z

/-- The function `deltaOverQ` does not vanish on the upper half-plane. -/
lemma deltaOverQ_ne_zero (z : ℍ) : deltaOverQ z ≠ 0 := by
  intro h
  have hprod : ∏' (n : ℕ), (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24 = 0 := by
    simpa [deltaOverQ] using h
  apply Δ_ne_zero z
  simp [Δ, hprod]

/-- The function `deltaOverQ` tends to `1` at infinity. -/
lemma deltaOverQ_tendsto_atImInfty : Tendsto deltaOverQ atImInfty (nhds (1 : ℂ)) := by
  simpa [deltaOverQ] using Delta_boundedfactor

/-- The q-expansion of `Delta` with its vanishing constant coefficient removed. -/
def deltaShiftedQSeries : ℍ → ℂ :=
  fun z ↦ ∑' n : ℕ, (qExpansion 1 Delta).coeff (n + 1) * cexp (2 * π * Complex.I * z) ^ n

private lemma Delta_qExpansion_coeff_zero_aux : (qExpansion 1 Delta).coeff 0 = 0 := by
  simpa [qExpansion_coeff] using
    CuspFormClass.cuspFunction_apply_zero Delta (by norm_num) (by simp)

private lemma Delta_hasSum_aux (z : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion 1 Delta).coeff m • 𝕢 1 (z : ℂ) ^ m) (Delta z) :=
  UpperHalfPlane.hasSum_qExpansion (by norm_num)
    (SlashInvariantFormClass.periodic_comp_ofComplex Delta (by simp))
    (ModularFormClass.holo Delta) (ModularFormClass.bdd_at_infty Delta) z

private lemma Delta_shift_hasSum_aux (z : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion 1 Delta).coeff (m + 1) • 𝕢 1 (z : ℂ) ^ m)
      ((𝕢 1 (z : ℂ))⁻¹ • Delta z) := by
  have hq : 𝕢 1 (z : ℂ) ≠ 0 := by simp [Periodic.qParam]
  have hs_shift :
      HasSum (fun m : ℕ ↦ (qExpansion 1 Delta).coeff (m + 1) • 𝕢 1 (z : ℂ) ^ (m + 1))
        (Delta z) := by
    have hs' := (hasSum_nat_add_iff' 1).2 (Delta_hasSum_aux z)
    simpa only [Finset.sum_range_one, Delta_qExpansion_coeff_zero_aux, zero_smul, sub_zero]
      using hs'
  have hs_mul := hs_shift.const_smul (𝕢 1 (z : ℂ))⁻¹
  simpa [smul_smul, pow_succ, hq, mul_assoc, mul_comm, mul_left_comm] using hs_mul

/-- The shifted q-series of `Delta` converges to `deltaOverQ` on the upper half-plane. -/
lemma deltaShiftedQSeries_eq_deltaOverQ : deltaShiftedQSeries = deltaOverQ := by
  ext z
  rw [deltaOverQ_eq_qParam_inv_smul_Delta, ← (Delta_shift_hasSum_aux z).tsum_eq]
  simp [deltaShiftedQSeries, Periodic.qParam, smul_eq_mul]

private lemma deltaShiftedQSeries_hasSum_aux (z : ℍ) :
    HasSum (fun m ↦ ((qExpansion 1 Delta).coeff (m + 1)) • 𝕢 1 (z : ℂ) ^ m)
      (deltaShiftedQSeries z) := by
  rw [deltaShiftedQSeries_eq_deltaOverQ, deltaOverQ_eq_qParam_inv_smul_Delta]
  exact Delta_shift_hasSum_aux z

private lemma cuspFunction_deltaShiftedQSeries_hasSum_aux :
    ∀ {q : ℂ}, ‖q‖ < 1 → q ≠ 0 →
    HasSum (fun n ↦ ((qExpansion 1 Delta).coeff (n + 1)) • q ^ n)
      (cuspFunction 1 deltaShiftedQSeries q) := by
  intro q hq hq0
  let τ : ℍ := ⟨Periodic.invQParam 1 q,
    Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num : 0 < (1 : ℝ)) hq hq0⟩
  have hqparam : 𝕢 1 (τ : ℂ) = q := by
    simpa [τ] using Periodic.qParam_right_inv (by norm_num : (1 : ℝ) ≠ 0) hq0
  have hcusp : cuspFunction 1 deltaShiftedQSeries q = deltaShiftedQSeries τ := by
    have him : 0 < Complex.im (Periodic.invQParam 1 q) :=
      Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num : 0 < (1 : ℝ)) hq hq0
    change Periodic.cuspFunction 1 (deltaShiftedQSeries ∘ UpperHalfPlane.ofComplex) q =
      deltaShiftedQSeries τ
    rw [Periodic.cuspFunction_eq_of_nonzero 1 _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  simpa [hqparam, hcusp] using deltaShiftedQSeries_hasSum_aux τ

private lemma cuspFunction_deltaShiftedQSeries_zero_aux :
    cuspFunction 1 deltaShiftedQSeries 0 = 1 := by
  refine cuspFunction_apply_zero_of_tendsto ?_
  rw [deltaShiftedQSeries_eq_deltaOverQ]
  simpa [deltaOverQ] using Delta_boundedfactor

private lemma deltaShiftedQSeries_analyticAt_aux :
    AnalyticAt ℂ (cuspFunction 1 deltaShiftedQSeries) 0 := by
  let cshift : ℕ → ℂ := fun m ↦ (qExpansion 1 Delta).coeff (m + 1)
  have hs_cusp : ∀ {q : ℂ}, ‖q‖ < 1 → q ≠ 0 →
      HasSum (fun n ↦ cshift n • q ^ n) (cuspFunction 1 deltaShiftedQSeries q) := by
    simp only [cshift]
    exact cuspFunction_deltaShiftedQSeries_hasSum_aux
  have Hupd : HasFPowerSeriesOnBall (update (cuspFunction 1 deltaShiftedQSeries) 0 (cshift 0))
      (.ofScalars ℂ cshift) 0 1 := by
    constructor
    · refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
      rcases eq_or_ne r 0 with rfl | hr'
      · simp
      · lift r to NNReal using hr.ne_top
        apply FormalMultilinearSeries.le_radius_of_summable
        simpa [norm_smul] using
          (hs_cusp (q := r) (by simpa using hr) (mod_cast hr')).summable.norm
    · simp
    · intro y hy
      rw [zero_add]
      rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hy
      rcases eq_or_ne y 0 with rfl | hy'
      · simpa +contextual [zero_pow_eq] using hasSum_ite_eq 0 (cshift 0)
      · simpa [update_of_ne hy', mul_comm] using hs_cusp (q := y) hy hy'
  have h0 : cshift 0 = cuspFunction 1 deltaShiftedQSeries 0 := by
    rw [cuspFunction_deltaShiftedQSeries_zero_aux]
    simpa [cshift] using Delta_q_one_term
  rw [update_eq_self_iff.mpr h0] at Hupd
  exact Hupd.hasFPowerSeriesAt.analyticAt

/-- The q-expansion of `deltaShiftedQSeries` is the shift of the q-expansion of `Delta`. -/
lemma deltaShiftedQSeries_qExpansion_coeff (n : ℕ) :
    (qExpansion 1 deltaShiftedQSeries).coeff n = (qExpansion 1 Delta).coeff (n + 1) :=
  (UpperHalfPlane.qExpansion_coeff_unique (f := deltaShiftedQSeries) (h := 1) (by norm_num)
    deltaShiftedQSeries_analyticAt_aux deltaShiftedQSeries_hasSum_aux n).symm

/-- The q-expansion of `deltaOverQ` has integral coefficients (the shifted Ramanujan tau
values). -/
lemma deltaOverQ_isIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 deltaOverQ) := by
  rw [int_iff]
  intro n
  refine ⟨integralDelta.coeff (n + 1), ?_⟩
  rw [← deltaShiftedQSeries_eq_deltaOverQ, deltaShiftedQSeries_qExpansion_coeff n]
  simpa using (congrArg (PowerSeries.coeff (n + 1))
    (coeTo_of_toIntegralPowerSeries Delta_isIntegralPowerSeries)).symm

/-- The integral power series whose complexification is the q-expansion of `deltaOverQ`. -/
def integralDeltaOverQ : PowerSeries ℤ := toIntegralPowerSeries deltaOverQ_isIntegralPowerSeries

/-- The complexification of `integralDeltaOverQ` recovers the q-expansion of `deltaOverQ`. -/
lemma coeTo_integralDeltaOverQ :
    (coeToComplexPowerSeries.ringHom ℤ) integralDeltaOverQ = qExpansion 1 deltaOverQ :=
  coeTo_of_toIntegralPowerSeries deltaOverQ_isIntegralPowerSeries

private lemma integralDeltaOverQ_constantCoeff_isUnit_aux :
    IsUnit (constantCoeff integralDeltaOverQ : ℤ) := by
  have hcoeff0C : (qExpansion 1 deltaOverQ).coeff 0 = 1 := by
    simp [qExpansion_coeff, cuspFunction_apply_zero_of_tendsto deltaOverQ_tendsto_atImInfty]
  have hZ : (constantCoeff integralDeltaOverQ : ℤ) = 1 := by
    have h0 := congrArg (PowerSeries.coeff 0) coeTo_integralDeltaOverQ
    simpa [coeToComplexPowerSeries.ringHom, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hcoeff0C] using h0
  simp [hZ]

private lemma integralDeltaOverQ_isUnit_aux : IsUnit integralDeltaOverQ :=
  PowerSeries.isUnit_iff_constantCoeff (φ := integralDeltaOverQ).mpr
    integralDeltaOverQ_constantCoeff_isUnit_aux

/-- The reciprocal of `deltaOverQ`, equivalently the q-parameter divided by `Delta`. -/
def qOverDelta : ℍ → ℂ := fun z ↦ 1 / deltaOverQ z

/-- The holomorphic regularization of `j` obtained by multiplying it by the q-parameter. -/
def qj : ℍ → ℂ := (fun z ↦ cexp (2 * π * Complex.I * z) : ℍ → ℂ) * j

/-- The factorization `qj = E4 ^ 3 * (q / Delta)` of the regularized modular invariant. -/
lemma E4_pow_three_mul_qOverDelta_eq_qj : E4 ^ 3 * qOverDelta = qj := by
  ext z
  change (E4 z) ^ 3 * qOverDelta z = cexp (2 * π * Complex.I * z) * ((E4 z) ^ 3 / Delta z)
  have hDq : deltaOverQ z = (1 / cexp (2 * π * Complex.I * z)) * Delta z := by
    simpa [Pi.mul_apply] using congrFun deltaOverQ_eq_qParam_inv_mul_Delta z
  have hDnz : Delta z ≠ 0 := by simpa [Delta_apply] using (Δ_ne_zero z)
  have hExpNz : cexp (2 * π * Complex.I * z) ≠ 0 := Complex.exp_ne_zero _
  have hqoz : qOverDelta z = cexp (2 * π * Complex.I * z) / Delta z := by
    rw [qOverDelta, hDq]
    field_simp [hDnz, hExpNz]
  calc
  _ = (E4 z) ^ 3 * (cexp (2 * π * Complex.I * z) / Delta z) := by rw [hqoz]
  _ = _ := by ring

private lemma deltaOverQ_analyticAt_aux : AnalyticAt ℂ (cuspFunction 1 deltaOverQ) 0 := by
  simpa [deltaShiftedQSeries_eq_deltaOverQ] using deltaShiftedQSeries_analyticAt_aux

/-- The function `qOverDelta` tends to `1` at infinity. -/
lemma qOverDelta_tendsto_atImInfty : Tendsto qOverDelta atImInfty (nhds (1 : ℂ)) := by
  change Tendsto (fun τ : ℍ ↦ 1 / deltaOverQ τ) atImInfty (nhds (1 : ℂ))
  simpa [one_div] using deltaOverQ_tendsto_atImInfty.inv₀ one_ne_zero

private lemma cuspFunction_deltaOverQ_zero_aux : cuspFunction 1 deltaOverQ 0 = 1 :=
  cuspFunction_apply_zero_of_tendsto deltaOverQ_tendsto_atImInfty

private lemma cuspFunction_qOverDelta_zero_aux : cuspFunction 1 qOverDelta 0 = 1 :=
  cuspFunction_apply_zero_of_tendsto qOverDelta_tendsto_atImInfty

private lemma cuspFunction_qOverDelta_eq_inv_aux :
    cuspFunction 1 qOverDelta = fun q ↦ (cuspFunction 1 deltaOverQ q)⁻¹ := by
  funext q
  by_cases hq : q = 0
  · simp [hq, cuspFunction_deltaOverQ_zero_aux, cuspFunction_qOverDelta_zero_aux]
  · simp [cuspFunction, Periodic.cuspFunction, hq, qOverDelta]

private lemma deltaOverQ_inv_analyticAt_aux :
    AnalyticAt ℂ (fun q ↦ (cuspFunction 1 deltaOverQ q)⁻¹) 0 := by
  exact deltaOverQ_analyticAt_aux.inv (by simp [cuspFunction_deltaOverQ_zero_aux])

/-- The cusp function of `qOverDelta` is analytic at `q = 0`. -/
lemma qOverDelta_cuspFunction_analyticAt : AnalyticAt ℂ (cuspFunction 1 qOverDelta) 0 := by
  simpa [cuspFunction_qOverDelta_eq_inv_aux] using deltaOverQ_inv_analyticAt_aux

private lemma E4_pow_three_isModularForm_aux :
    ∃ f : ModularForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma 1)) 12, (f : ℍ → ℂ) = E4 ^ 3 := by
  refine ⟨E4.mul (E4.mul E4), ?_⟩
  funext z
  simpa [pow_three] using congrFun (ModularForm.coe_mul E4 (E4.mul E4)) z

/-- The cusp function of `E4 ^ 3` is analytic at `q = 0`. -/
lemma E4_pow_three_cuspFunction_analyticAt : AnalyticAt ℂ (cuspFunction 1 (E4 ^ 3)) 0 := by
  rcases E4_pow_three_isModularForm_aux with ⟨f, hf⟩
  simpa [hf] using
    (ModularFormClass.analyticAt_cuspFunction_zero f (by norm_num) (by simp))

/-- The q-expansions of `deltaOverQ` and `qOverDelta` are multiplicative inverses. -/
lemma integralDeltaOverQ_mul_qExpansion_qOverDelta :
    (coeToComplexPowerSeries.ringHom ℤ) integralDeltaOverQ * qExpansion 1 qOverDelta = 1 := by
  rw [coeTo_integralDeltaOverQ,
    ← qExpansion_mul deltaOverQ_analyticAt_aux qOverDelta_cuspFunction_analyticAt]
  have h : deltaOverQ * qOverDelta = 1 := by
    ext z
    simp [qOverDelta, deltaOverQ_ne_zero]
  rw [h, qExpansion_one]

private lemma qOverDelta_isIntegralPowerSeries_aux :
    IsIntegralPowerSeries (qExpansion 1 qOverDelta) := by
  obtain ⟨u, hu⟩ := integralDeltaOverQ_isUnit_aux
  refine ⟨(↑(u⁻¹) : PowerSeries ℤ), ?_⟩
  calc
    (coeToComplexPowerSeries.ringHom ℤ) (↑(u⁻¹) : PowerSeries ℤ)
        = (coeToComplexPowerSeries.ringHom ℤ) (↑(u⁻¹) : PowerSeries ℤ) *
          ((coeToComplexPowerSeries.ringHom ℤ) integralDeltaOverQ *
            qExpansion 1 qOverDelta) := by
          rw [integralDeltaOverQ_mul_qExpansion_qOverDelta, mul_one]
    _ = (coeToComplexPowerSeries.ringHom ℤ) ((↑(u⁻¹) : PowerSeries ℤ) * ↑u) *
          qExpansion 1 qOverDelta := by rw [hu, ← mul_assoc, ← map_mul]
    _ = qExpansion 1 qOverDelta := by simp

private lemma qj_isIntegralPowerSeries_aux :
    IsIntegralPowerSeries (qExpansion 1 (E4 ^ 3 * qOverDelta)) := by
  rw [qExpansion_mul E4_pow_three_cuspFunction_analyticAt qOverDelta_cuspFunction_analyticAt]
  exact hasCoeffsIn_mul ℤ ℂ E4_pow_three_isIntegralPowerSeries
    qOverDelta_isIntegralPowerSeries_aux

/-- The q-expansion of the regularized modular invariant `qj` has integral coefficients. -/
theorem qj_isIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 qj) := by
  simpa using E4_pow_three_mul_qOverDelta_eq_qj ▸ qj_isIntegralPowerSeries_aux

/-- The integral coefficients of the q-expansion of `qj`. -/
def qjCoeffs : ℕ → ℤ := fun n ↦ (toIntegralPowerSeries qj_isIntegralPowerSeries).coeff n

private lemma qj_coeff_cast_aux (n : ℕ) :
    ((qjCoeffs n : ℤ) : ℂ) = (qExpansion 1 qj).coeff n :=
  congrArg (PowerSeries.coeff n) (coeTo_of_toIntegralPowerSeries qj_isIntegralPowerSeries)

private lemma qj_vadd_one_aux (τ : ℍ) : qj ((1 : ℝ) +ᵥ τ) = qj τ := by
  have hE4 : E4 ((1 : ℝ) +ᵥ τ) = E4 τ := by
    simpa using
      (SlashInvariantForm.vAdd_apply_of_mem_strictPeriods (f := E4) (τ := τ) (hH := by simp))
  have hDelta : Delta ((1 : ℝ) +ᵥ τ) = Delta τ := by
    simpa using
      (SlashInvariantForm.vAdd_apply_of_mem_strictPeriods
        (f := Delta) (τ := τ) (hH := by simp))
  have hj : j ((1 : ℝ) +ᵥ τ) = j τ := by
    simp [j, hE4, hDelta]
  have hexp :
      cexp (2 * π * Complex.I * (((1 : ℝ) +ᵥ τ : ℍ) : ℂ)) =
        cexp (2 * π * Complex.I * (τ : ℂ)) := by
    calc
    _ = cexp (2 * π * Complex.I * ((1 : ℂ) + (τ : ℂ))) := by
      simp [UpperHalfPlane.coe_vadd]
    _ = cexp (2 * π * Complex.I * (τ : ℂ) + 2 * π * Complex.I) := by ring_nf
    _ = cexp (2 * π * Complex.I * (τ : ℂ)) * cexp (2 * π * Complex.I) := by
      rw [Complex.exp_add]
    _ = _ := by simp [Complex.exp_two_pi_mul_I]
  change cexp (2 * π * Complex.I * (((1 : ℝ) +ᵥ τ : ℍ) : ℂ)) * j ((1 : ℝ) +ᵥ τ) =
    cexp (2 * π * Complex.I * (τ : ℂ)) * j τ
  rw [hj, hexp]

/-- The complex extension of `qj` is one-periodic. -/
lemma qj_periodic : Periodic (qj ∘ UpperHalfPlane.ofComplex) 1 := by
  intro w
  by_cases hw : 0 < Complex.im w
  · have hw1 : 0 < Complex.im (w + 1) := by simpa using hw
    let τ : ℍ := ⟨w, hw⟩
    have hτ1 : ((1 : ℝ) +ᵥ τ : ℍ) = UpperHalfPlane.ofComplex (w + 1) := by
      apply UpperHalfPlane.ext
      simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos hw1, UpperHalfPlane.coe_vadd, add_comm]
    have hq : qj (UpperHalfPlane.ofComplex (w + 1)) = qj (UpperHalfPlane.ofComplex w) := by
      calc
      _ = qj ((1 : ℝ) +ᵥ τ) := by rw [← hτ1]
      _ = qj τ := qj_vadd_one_aux τ
      _ = _ := by simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    simpa [comp] using hq
  · have hw0 : Complex.im w ≤ 0 := le_of_not_gt hw
    have hw1 : Complex.im (w + 1) ≤ 0 := by simpa using hw0
    simp [comp, UpperHalfPlane.ofComplex_apply_of_im_nonpos hw1,
        UpperHalfPlane.ofComplex_apply_of_im_nonpos hw0]

/-- The complex extension of `qj` is holomorphic on the open upper half-plane. -/
lemma qj_differentiableAt_of_im_pos : ∀ z : ℂ, 0 < Complex.im z →
    DifferentiableAt ℂ (qj ∘ UpperHalfPlane.ofComplex) z := by
  intro z hz
  have hexp := (Complex.differentiableAt_exp.comp z ((differentiableAt_id :
      DifferentiableAt ℂ (fun w : ℂ ↦ w) z).const_mul (2 * π * Complex.I)))
  have hEqExp :
      (((fun τ : ℍ ↦ cexp (2 * π * Complex.I * (τ : ℂ))) ∘
        UpperHalfPlane.ofComplex)
      =ᶠ[nhds z] (fun w : ℂ ↦ cexp (2 * π * Complex.I * w))) := by
    filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im) hz] with w hw
    simp [comp, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  have hexpH :
      DifferentiableAt ℂ
        (((fun τ : ℍ ↦ cexp (2 * π * Complex.I * (τ : ℂ))) ∘
          UpperHalfPlane.ofComplex)) z := by
    exact hexp.congr_of_eventuallyEq hEqExp
  have hE4 : DifferentiableAt ℂ (E4 ∘ UpperHalfPlane.ofComplex) z :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo E4 ⟨z, hz⟩)
  have hDelta : DifferentiableAt ℂ (Delta ∘ UpperHalfPlane.ofComplex) z :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo Delta ⟨z, hz⟩)
  have hDelta0 : (Delta ∘ UpperHalfPlane.ofComplex) z ≠ 0 := by
    simpa [comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz, Delta_apply] using
      (Δ_ne_zero (UpperHalfPlane.ofComplex z))
  have hj : DifferentiableAt ℂ (j ∘ UpperHalfPlane.ofComplex) z := by
    simpa [j, comp] using (hE4.pow 3).div hDelta hDelta0
  simpa [qj, comp, Pi.mul_apply] using hexpH.mul hj

/-- The regularized modular invariant `qj` is differentiable on the upper half-plane. -/
lemma qj_mdifferentiable : MDiff qj := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  exact (qj_differentiableAt_of_im_pos z hz).differentiableWithinAt

private lemma E4_pow_three_isBoundedAtImInfty_aux :
    IsBoundedAtImInfty (fun z : ℍ ↦ E4 z ^ 3) := by
  have h : IsBoundedAtImInfty E4 := by simp [ModularFormClass.bdd_at_infty]
  simpa [pow_three, mul_assoc] using h.mul (h.mul h)

/-- The regularized modular invariant `qj` is bounded at infinity. -/
lemma qj_isBoundedAtImInfty : IsBoundedAtImInfty qj := by
  have hqoverDelta : IsBoundedAtImInfty qOverDelta := by
    simpa [IsBoundedAtImInfty, BoundedAtFilter, Pi.one_def] using
      qOverDelta_tendsto_atImInfty.isBigO_one ℂ
  have hqjEq : ((fun z : ℍ ↦ (E4 z) ^ 3) * qOverDelta) = qj := by
    ext z
    simpa [qj] using congrFun E4_pow_three_mul_qOverDelta_eq_qj z
  simpa [hqjEq] using E4_pow_three_isBoundedAtImInfty_aux.mul hqoverDelta

/-- The q-expansion of `qj` converges to `qj` at every point of the upper half-plane. -/
lemma hasSum_qExpansion_qj {τ : ℍ} :
    HasSum (fun m : ℕ ↦ (qExpansion 1 qj).coeff m • 𝕢 1 τ ^ m) (qj τ) :=
  UpperHalfPlane.hasSum_qExpansion (h := 1) (f := qj) (by positivity) qj_periodic
    qj_mdifferentiable qj_isBoundedAtImInfty τ

private lemma qjCoeffs_hasSum_aux (z : ℍ) :
    HasSum (fun n : ℕ ↦ (qjCoeffs n : ℂ) * cexp (2 * π * Complex.I * z) ^ n) (qj z) := by
  simpa [smul_eq_mul, Periodic.qParam, ← qj_coeff_cast_aux] using
    hasSum_qExpansion_qj (τ := z)

private lemma infSumQj_summable_aux {z : ℍ} :
    Summable (fun n : ℕ ↦ (qjCoeffs n) * cexp (2 * π * Complex.I * z) ^ n) :=
  (qjCoeffs_hasSum_aux z).summable

private lemma qj_eq_tsum_aux (z : ℍ) :
    qj z = ∑' n, (qjCoeffs n) * cexp (2 * π * Complex.I * z) ^ n :=
  (qjCoeffs_hasSum_aux z).tsum_eq.symm

private lemma qj_div_qParam_eq_j_aux (z : ℍ) :
    qj z / cexp (2 * π * Complex.I * z) = j z := by
  simp [qj]

private lemma qjCoeffs_tsum_div_qParam_aux (z : ℍ) :
    (∑' n, (qjCoeffs n) * cexp (2 * π * Complex.I * z) ^ n) / cexp (2 * π * Complex.I * z)
    = (qjCoeffs 0 / cexp (2 * π * Complex.I * z)) +
    ∑' n, (qjCoeffs (n + 1)) * cexp (2 * π * Complex.I * z) ^ n := by
  let q : ℂ := cexp (2 * π * Complex.I * z)
  have hq : q ≠ 0 := by simp [q]
  have hsplit : (∑' n, (qjCoeffs n) * q ^ n)
        = (qjCoeffs 0) * q ^ 0 + ∑' n, (qjCoeffs (n + 1)) * q ^ (n + 1) := by
    simpa [q] using infSumQj_summable_aux.tsum_eq_zero_add
  calc
  _ = ((qjCoeffs 0) * q ^ 0) / q + (∑' n, (qjCoeffs (n + 1)) * q ^ (n + 1)) / q := by
    rw [hsplit, add_div]
  _ = (qjCoeffs 0 / q) + ∑' n, ((qjCoeffs (n + 1)) * q ^ (n + 1)) / q := by
    rw [tsum_div_const]
    simp
  _ = (qjCoeffs 0 / q) + ∑' n, (qjCoeffs (n + 1)) * q ^ n := by
    congr 1
    refine tsum_congr ?_
    intro n
    rw [pow_succ]
    field_simp [hq, mul_assoc]
  _ = _ := by simp [q]

/-- The convergent q-series reconstruction of the modular invariant `j`. -/
theorem j_eq_qjCoeffs_tsum (z : ℍ) :
    j z = qjCoeffs 0 / cexp (2 * π * Complex.I * z) +
      ∑' n, qjCoeffs (n + 1) * cexp (2 * π * Complex.I * z) ^ n := by
  rw [← qj_div_qParam_eq_j_aux, qj_eq_tsum_aux z, qjCoeffs_tsum_div_qParam_aux]

/-- The regularized modular invariant `qj` has constant coefficient one. -/
lemma qj_qExpansion_coeff_zero : (qExpansion 1 qj).coeff 0 = 1 := by
  have hqj : qExpansion 1 qj = qExpansion 1 (E4 ^ 3 * qOverDelta) := by
    simpa [qj] using congrArg (qExpansion 1) E4_pow_three_mul_qOverDelta_eq_qj.symm
  have hmul :
      qExpansion 1 (E4 ^ 3 * qOverDelta) = qExpansion 1 (E4 ^ 3) * qExpansion 1 qOverDelta := by
    exact qExpansion_mul E4_pow_three_cuspFunction_analyticAt qOverDelta_cuspFunction_analyticAt
  have hE4pow : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using
      qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
        (k := (4 : ℤ)) (hh := by norm_num) (hΓ := by simp) E4 3
  have hE4coeff0 : (qExpansion 1 E4).coeff 0 = 1 := by
    simpa [UpperHalfPlane.qExpansion_coeff, E4] using
      EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4) ⟨2, rfl⟩
  have hE4pow0 : (qExpansion 1 (E4 ^ 3)).coeff 0 = 1 := by
    rw [hE4pow]
    have hE4const : PowerSeries.constantCoeff (qExpansion 1 E4) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE4coeff0
    simp [PowerSeries.coeff_zero_eq_constantCoeff, hE4const]
  have hqover0 : (qExpansion 1 qOverDelta).coeff 0 = 1 := by
    simp [qExpansion_coeff, cuspFunction_qOverDelta_zero_aux]
  calc
  _ = (qExpansion 1 (E4 ^ 3 * qOverDelta)).coeff 0 := by rw [hqj]
  _ = (qExpansion 1 (E4 ^ 3) * qExpansion 1 qOverDelta).coeff 0 := by rw [hmul]
  _ = (qExpansion 1 (E4 ^ 3)).coeff 0 * (qExpansion 1 qOverDelta).coeff 0 := by simp
  _ = _ := by simp [hE4pow0, hqover0]

private lemma qj_cuspFunction_differentiableOn_aux :
    DifferentiableOn ℂ (cuspFunction 1 qj) (Metric.ball 0 1) :=
  UpperHalfPlane.differentiableOn_cuspFunction_ball (h := 1) (f := qj) (by norm_num)
    qj_periodic qj_mdifferentiable qj_isBoundedAtImInfty

/-- The cusp function of `qj` is analytic at `q = 0`. -/
lemma qj_cuspFunction_analyticAt : AnalyticAt ℂ (cuspFunction 1 qj) 0 :=
  qj_cuspFunction_differentiableOn_aux.analyticAt (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

private lemma inv_mul_cuspFunction_qj_eq_j_aux :
    (fun q : ℂ ↦ q⁻¹ * cuspFunction 1 qj q) =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
      cuspFunction 1 j := by
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) := by
    refine nhdsWithin_le_nhds ?_
    simpa [Metric.ball, dist_eq_norm] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one
  filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hq
  have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
  have hqj : cuspFunction 1 qj q = q * cuspFunction 1 j q := by
    simpa [qj, Periodic.qParam, pow_one, Pi.mul_apply] using
      cuspFunction_qpow_mul_eq (h := 1) (hh := by norm_num) (f := j) (n := 1) hq0 hqnorm
  rw [hqj, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul]

/-- The cusp function of `j` is meromorphic at `q = 0`. -/
lemma j_cuspFunction_meromorphicAt : MeromorphicAt (cuspFunction 1 j) (0 : ℂ) :=
  (((MeromorphicAt.id (0 : ℂ)).inv).mul
    qj_cuspFunction_analyticAt.meromorphicAt).congr inv_mul_cuspFunction_qj_eq_j_aux

/-- The modular invariant `j` has a simple pole at infinity. -/
lemma j_poleOrder : poleOrder 1 j = 1 := by
  refine poleOrder_eq_of_meromorphicOrderAt_eq (r := 1) ?_
  have hqj0 : cuspFunction 1 qj 0 = 1 := by
    simpa [qExpansion_coeff] using qj_qExpansion_coeff_zero
  have hqinvord : meromorphicOrderAt (fun q : ℂ ↦ q⁻¹) (0 : ℂ) = (-1 : WithTop ℤ) := by
    calc
      meromorphicOrderAt (fun q : ℂ ↦ q⁻¹) (0 : ℂ)
          = -meromorphicOrderAt (fun q : ℂ ↦ q) (0 : ℂ) := by
              simpa using (meromorphicOrderAt_inv (f := fun q : ℂ ↦ q) (x := (0 : ℂ)))
      _ = (-1 : WithTop ℤ) := by
            change -meromorphicOrderAt (𝕜 := ℂ) id 0 = (-1 : WithTop ℤ)
            simp
  rw [meromorphicOrderAt_congr inv_mul_cuspFunction_qj_eq_j_aux.symm]
  change meromorphicOrderAt (((fun q : ℂ ↦ q⁻¹) * cuspFunction 1 qj)) (0 : ℂ) = _
  rw [show (fun q : ℂ ↦ q⁻¹) * cuspFunction 1 qj = cuspFunction 1 qj * fun q : ℂ ↦ q⁻¹
    by ext; simp [mul_comm]]
  rw [meromorphicOrderAt_mul_of_ne_zero qj_cuspFunction_analyticAt (by simp [hqj0]), hqinvord]
  rfl

/-- The pole of `j` at infinity is not a removable singularity. -/
lemma j_cuspFunction_not_analyticAt : ¬ AnalyticAt ℂ (cuspFunction 1 j) 0 := by
  simp [analyticAt_cuspFunction_iff_poleOrder_eq_zero j_cuspFunction_meromorphicAt,
    j_poleOrder]

/-- Removing the pole of `j` at infinity yields the regularized modular invariant `qj`. -/
lemma j_poleRemoved : poleRemoved 1 j = qj := by
  ext τ
  simp [UpperHalfPlane.poleRemoved, qj, j_poleOrder, Periodic.qParam, pow_one]

/-- The regularized q-expansion of `j` is the q-expansion of `qj`. -/
lemma j_to_qExpansion : to_qExpansion 1 j = qExpansion 1 qj := by
  simp [UpperHalfPlane.to_qExpansion, j_poleRemoved]

/-- The Laurent q-expansion of `j` has no coefficients below degree `-1`. -/
theorem j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one {n : ℤ} (hn : n < -1) :
    (laurentqExpansion 1 j).coeff n = 0 := by
  have hlt : n < -(poleOrder 1 j : ℤ) := by simpa [j_poleOrder] using hn
  exact laurentqExpansion.coeff_eq_zero_of_lt hlt

/-- Every Laurent q-expansion coefficient of the modular invariant `j` is an integer. -/
theorem j_laurentQExpansion_isIntegral {n : ℤ} :
    ∃ m : ℤ, (laurentqExpansion 1 j).coeff n = m := by
  by_cases hn : n < -1
  · refine ⟨0, ?_⟩
    simp [j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one hn]
  · refine ⟨qjCoeffs (Int.toNat (n + 1)), ?_⟩
    have hge : -(poleOrder 1 j : ℤ) ≤ n := by
      simpa [j_poleOrder] using le_of_not_gt hn
    calc
    _ = (to_qExpansion 1 j).coeff (Int.toNat (n + poleOrder 1 j)) := by
            simpa using (laurentqExpansion.coeff_of_geq hge)
    _ = (qExpansion 1 qj).coeff (Int.toNat (n + poleOrder 1 j)) := by rw [j_to_qExpansion]
    _ = (qExpansion 1 qj).coeff (Int.toNat (n + 1)) := by simp [j_poleOrder]
    _ = _ := by simpa using (qj_coeff_cast_aux (Int.toNat (n + 1))).symm

end
