/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion

import XYin.PhD.IntegralPowerSeries.IntegralPowerSeries
import XYin.PhD.jFunction.Deltaqexpansions
import XYin.PhD.LaurentQExpansion.Algebra

/-!
# The modular `j`-function and its Laurent q-expansion

This file defines the classical modular function `j = E4 ^ 3 / Delta`. It constructs the
holomorphic regularization `qj`, proves that its q-expansion has integral coefficients and
constant coefficient one, and deduces the pole order and integrality of the Laurent q-expansion
of `j` at infinity.

## Main definitions

* `j`: the classical modular function.
* `deltaOverQ`, `qOverDelta`: the unit `Δ / q = ∏ (1 - qⁿ)²⁴` and its inverse.
* `qj`: the regularized function obtained by multiplying `j` by the q-parameter.
* `qjCoeffs`: the integral coefficients of the q-expansion of `qj`.

## Main results

* `qExpansion_Delta_eq_X_mul`: the q-expansion of `Δ` is `X` times the q-expansion of `Δ / q`.
* `qj_isIntegralPowerSeries`: the q-expansion of `qj` has integral coefficients.
* `j_eq_qjCoeffs_tsum`: the convergent q-series reconstruction of `j`.
* `j_poleOrder`: the function `j` has a simple pole at infinity.
* `j_laurentQExpansion_coeff`: the Laurent q-expansion coefficients of `j` with explicit integer
  witnesses; `j_laurentQExpansion_isIntegral` is its existential form.
-/

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups PowerSeries
  SlashInvariantFormClass Real Function IntegralPowerSeries
open scoped Manifold Topology

local notation "𝕢" => Periodic.qParam

noncomputable section

/-- If `f` tends to `a` at `i∞`, then its cusp function takes the value `a` at `q = 0`. -/
lemma cuspFunction_apply_zero_of_tendsto {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} {a : ℂ}
    (hf : Tendsto f atImInfty (𝓝 a)) : cuspFunction h f 0 = a := by
  have hcomp : Tendsto ((f ∘ UpperHalfPlane.ofComplex) ∘ Periodic.invQParam h) (𝓝[≠] 0) (𝓝 a) :=
    hf.comp (tendsto_comap_im_ofComplex.comp (Periodic.invQParam_tendsto hh))
  simpa [cuspFunction, Periodic.cuspFunction, comp_def] using hcomp.limUnder_eq

/-- A function with a limit at `i∞` is bounded at `i∞`. -/
lemma isBoundedAtImInfty_of_tendsto {f : ℍ → ℂ} {a : ℂ} (hf : Tendsto f atImInfty (𝓝 a)) :
    IsBoundedAtImInfty f := by
  simpa [IsBoundedAtImInfty, BoundedAtFilter, Pi.one_def] using hf.isBigO_one ℝ

private lemma mdifferentiable_cexp_aux : MDiff (fun τ : ℍ ↦ cexp (2 * π * Complex.I * τ)) :=
  Complex.differentiable_exp.mdifferentiable.comp
    (mdifferentiable_const.mul UpperHalfPlane.mdifferentiable_coe)

private lemma cexp_vadd_one_aux (τ : ℍ) :
    cexp (2 * π * Complex.I * ↑((1 : ℝ) +ᵥ τ)) = cexp (2 * π * Complex.I * τ) := by
  simp [UpperHalfPlane.coe_vadd, mul_add, Complex.exp_add]

private lemma E4_vadd_one_aux (τ : ℍ) : E4 ((1 : ℝ) +ᵥ τ) = E4 τ :=
  SlashInvariantForm.vAdd_apply_of_mem_strictPeriods E4 τ (by simp)

private lemma Delta_vadd_one_aux (τ : ℍ) : Delta ((1 : ℝ) +ᵥ τ) = Delta τ :=
  SlashInvariantForm.vAdd_apply_of_mem_strictPeriods Delta τ (by simp)

/-- The classical modular invariant `j = E4 ^ 3 / Delta`. -/
def j : ℍ → ℂ := fun τ ↦ (E4 τ) ^ 3 / Delta τ

/-- The modular invariant is holomorphic on the upper half-plane. -/
lemma j_mdifferentiable : MDiff j := by
  simpa only [j, Function.comp_def] using
    ((ModularFormClass.holo E4).pow 3).div (ModularFormClass.holo Delta)
      (fun τ ↦ Δ_ne_zero τ)

/-- The modular invariant `j` is invariant under the weight-zero slash action of `SL₂(ℤ)`. -/
lemma j_slash_invariant (γ : SL(2, ℤ)) : j ∣[(0 : ℤ)] γ = j := by
  let f := E4.mul (E4.mul E4)
  have hj : j = (f : ℍ → ℂ) / Delta := by
    simp only [f, ModularForm.coe_mul]
    ext z
    simp [j, pow_three]
  have hγ : (γ : GL (Fin 2) ℝ) ∈
      Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1) :=
    (Subgroup.mem_map_iff_mem Matrix.SpecialLinearGroup.mapGL_injective).mpr
      (CongruenceSubgroup.mem_Gamma_one γ)
  rw [hj]
  change ((f : ℍ → ℂ) / Delta) ∣[(12 - 12 : ℤ)] γ = _
  rw [div_slash_SL2, SL_slash, SL_slash]
  exact congrArg₂ (· / ·) (f.slash_action_eq' γ hγ) (Delta.slash_action_eq' γ hγ)

/-- The modular invariant `j` is unchanged by the action of `SL₂(ℤ)`. -/
lemma j_modularGroup_smul (γ : SL(2, ℤ)) (z : ℍ) : j (γ • z) = j z := by
  have h := congrFun (j_slash_invariant γ) z
  simpa only [SL_slash_apply, neg_zero, zpow_zero, mul_one] using h

/-! ### The unit `Δ / q` -/

/-- The discriminant divided by the q-parameter, expressed as its infinite product. -/
def deltaOverQ : ℍ → ℂ :=
  fun z ↦ ∏' (n : ℕ), (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24

/-- The infinite product `deltaOverQ` is the discriminant divided by the q-parameter. -/
lemma deltaOverQ_eq_qParam_inv_mul_Delta :
    deltaOverQ = (fun z ↦ 1 / cexp (2 * π * Complex.I * z) : ℍ → ℂ) * Delta := by
  ext z
  simp [deltaOverQ, Delta_apply, Δ, Pi.mul_apply, mul_assoc]

/-- The function `deltaOverQ` does not vanish on the upper half-plane. -/
lemma deltaOverQ_ne_zero (z : ℍ) : deltaOverQ z ≠ 0 := by
  rw [deltaOverQ_eq_qParam_inv_mul_Delta, Pi.mul_apply]
  exact mul_ne_zero (one_div_ne_zero (Complex.exp_ne_zero _)) (Δ_ne_zero z)

/-- The function `deltaOverQ` tends to `1` at infinity. -/
lemma deltaOverQ_tendsto_atImInfty : Tendsto deltaOverQ atImInfty (𝓝 (1 : ℂ)) := by
  simpa [deltaOverQ] using Delta_boundedfactor

private lemma deltaOverQ_vadd_one_aux (τ : ℍ) : deltaOverQ ((1 : ℝ) +ᵥ τ) = deltaOverQ τ := by
  simp only [deltaOverQ_eq_qParam_inv_mul_Delta, Pi.mul_apply, cexp_vadd_one_aux,
    Delta_vadd_one_aux]

private lemma deltaOverQ_periodic_aux : Periodic (deltaOverQ ∘ UpperHalfPlane.ofComplex) 1 :=
  periodic_comp_ofComplex_of_vadd deltaOverQ_vadd_one_aux

private lemma deltaOverQ_mdifferentiable_aux : MDiff deltaOverQ := by
  rw [deltaOverQ_eq_qParam_inv_mul_Delta]
  exact (mdifferentiable_const.div mdifferentiable_cexp_aux fun _ ↦ Complex.exp_ne_zero _).mul
    (ModularFormClass.holo Delta)

/-- The cusp function of `deltaOverQ` is analytic at `q = 0`. -/
lemma deltaOverQ_cuspFunction_analyticAt : AnalyticAt ℂ (cuspFunction 1 deltaOverQ) 0 :=
  analyticAt_cuspFunction_zero one_pos deltaOverQ_periodic_aux deltaOverQ_mdifferentiable_aux
    (isBoundedAtImInfty_of_tendsto deltaOverQ_tendsto_atImInfty)

/-- The q-expansion of `Delta` is `X` times the q-expansion of `deltaOverQ = Δ / q`. -/
lemma qExpansion_Delta_eq_X_mul : qExpansion 1 Delta = X * qExpansion 1 deltaOverQ := by
  have h : ⇑Delta = fun τ : ℍ ↦ 𝕢 1 τ ^ 1 * deltaOverQ τ := by
    ext τ
    simp [deltaOverQ_eq_qParam_inv_mul_Delta, Periodic.qParam]
  rw [h, qExpansion_qpow_mul one_pos deltaOverQ_cuspFunction_analyticAt 1, pow_one]

/-- The q-expansion coefficients of `deltaOverQ` are the shifted coefficients of `Delta`. -/
lemma deltaOverQ_qExpansion_coeff (n : ℕ) :
    (qExpansion 1 deltaOverQ).coeff n = (qExpansion 1 Delta).coeff (n + 1) := by
  rw [qExpansion_Delta_eq_X_mul, coeff_succ_X_mul]

/-- The q-expansion of `Delta` with its vanishing constant coefficient removed. -/
def deltaShiftedQSeries : ℍ → ℂ :=
  fun z ↦ ∑' n : ℕ, (qExpansion 1 Delta).coeff (n + 1) * cexp (2 * π * Complex.I * z) ^ n

/-- The shifted q-series of `Delta` converges to `deltaOverQ` on the upper half-plane. -/
lemma deltaShiftedQSeries_eq_deltaOverQ : deltaShiftedQSeries = deltaOverQ := by
  ext z
  rw [← (hasSum_qExpansion one_pos deltaOverQ_periodic_aux deltaOverQ_mdifferentiable_aux
    (isBoundedAtImInfty_of_tendsto deltaOverQ_tendsto_atImInfty) z).tsum_eq]
  simp [deltaShiftedQSeries, deltaOverQ_qExpansion_coeff, Periodic.qParam]

/-- The q-expansion of `deltaOverQ` has integral coefficients (the shifted Ramanujan tau
values). -/
lemma deltaOverQ_isIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 deltaOverQ) :=
  (int_iff _).2 fun n ↦ ⟨integralDelta.coeff (n + 1), (deltaOverQ_qExpansion_coeff n).trans
    (coeff_toIntegralPowerSeries_cast Delta_isIntegralPowerSeries (n + 1)).symm⟩

/-- The integral power series whose complexification is the q-expansion of `deltaOverQ`. -/
def integralDeltaOverQ : PowerSeries ℤ := toIntegralPowerSeries deltaOverQ_isIntegralPowerSeries

/-- The complexification of `integralDeltaOverQ` recovers the q-expansion of `deltaOverQ`. -/
lemma coeTo_integralDeltaOverQ :
    (coeToComplexPowerSeries.ringHom ℤ) integralDeltaOverQ = qExpansion 1 deltaOverQ :=
  coeTo_of_toIntegralPowerSeries deltaOverQ_isIntegralPowerSeries

private lemma integralDeltaOverQ_isUnit_aux : IsUnit integralDeltaOverQ := by
  have h : (qExpansion 1 deltaOverQ).coeff 0 = 1 := by
    simp [qExpansion_coeff, cuspFunction_apply_zero_of_tendsto one_pos
      deltaOverQ_tendsto_atImInfty]
  have hZ : integralDeltaOverQ.coeff 0 = 1 := by
    exact_mod_cast (coeff_toIntegralPowerSeries_cast deltaOverQ_isIntegralPowerSeries 0).trans h
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, hZ]
  exact isUnit_one

/-! ### The regularization `qj = q · j` -/

/-- The reciprocal of `deltaOverQ`, equivalently the q-parameter divided by `Delta`. -/
def qOverDelta : ℍ → ℂ := fun z ↦ 1 / deltaOverQ z

/-- The holomorphic regularization of `j` obtained by multiplying it by the q-parameter. -/
def qj : ℍ → ℂ := (fun z ↦ cexp (2 * π * Complex.I * z) : ℍ → ℂ) * j

/-- `qj τ = q · j τ`, with `q = 𝕢 1 τ = exp (2πiτ)` the q-parameter. -/
lemma qj_apply (τ : ℍ) : qj τ = 𝕢 1 τ * j τ := by
  simp [qj, Periodic.qParam]

/-- The factorization `qj = E4 ^ 3 * (q / Delta)` of the regularized modular invariant. -/
lemma E4_pow_three_mul_qOverDelta_eq_qj : E4 ^ 3 * qOverDelta = qj := by
  ext z
  simp only [qOverDelta, deltaOverQ_eq_qParam_inv_mul_Delta, Pi.mul_apply,
    mul_inv_rev, inv_inv, qj, j, Pi.pow_apply, div_eq_mul_inv]
  ring

/-- The function `qOverDelta` tends to `1` at infinity. -/
lemma qOverDelta_tendsto_atImInfty : Tendsto qOverDelta atImInfty (𝓝 (1 : ℂ)) := by
  change Tendsto (fun τ ↦ 1 / deltaOverQ τ) atImInfty (𝓝 (1 : ℂ))
  simpa [one_div] using deltaOverQ_tendsto_atImInfty.inv₀ one_ne_zero

/-- The cusp function of `qOverDelta` is analytic at `q = 0`. -/
lemma qOverDelta_cuspFunction_analyticAt : AnalyticAt ℂ (cuspFunction 1 qOverDelta) 0 :=
  analyticAt_cuspFunction_zero one_pos
    (periodic_comp_ofComplex_of_vadd fun τ ↦ by simp only [qOverDelta, deltaOverQ_vadd_one_aux])
    (mdifferentiable_const.div deltaOverQ_mdifferentiable_aux deltaOverQ_ne_zero)
    (isBoundedAtImInfty_of_tendsto qOverDelta_tendsto_atImInfty)

/-- The cusp function of `E4 ^ 3` is analytic at `q = 0`. -/
lemma E4_pow_three_cuspFunction_analyticAt : AnalyticAt ℂ (cuspFunction 1 (E4 ^ 3)) 0 := by
  simpa [ModularForm.coe_pow] using
    ModularFormClass.analyticAt_cuspFunction_zero (E4.pow 3) one_pos (by simp)

/-- The q-expansions of `deltaOverQ` and `qOverDelta` are multiplicative inverses. -/
lemma integralDeltaOverQ_mul_qExpansion_qOverDelta :
    (coeToComplexPowerSeries.ringHom ℤ) integralDeltaOverQ * qExpansion 1 qOverDelta = 1 := by
  rw [coeTo_integralDeltaOverQ,
    ← qExpansion_mul deltaOverQ_cuspFunction_analyticAt qOverDelta_cuspFunction_analyticAt]
  have h : deltaOverQ * qOverDelta = 1 := by
    ext z
    simp [qOverDelta, deltaOverQ_ne_zero]
  rw [h, qExpansion_one]

private lemma qOverDelta_isIntegralPowerSeries_aux :
    IsIntegralPowerSeries (qExpansion 1 qOverDelta) := by
  obtain ⟨u, hu⟩ := integralDeltaOverQ_isUnit_aux
  refine ⟨(↑(u⁻¹) : PowerSeries ℤ), ?_⟩
  exact (Units.map (coeToComplexPowerSeries.ringHom ℤ).toMonoidHom u).inv_eq_of_mul_eq_one_right
    (by simpa only [Units.coe_map, MonoidHom.coe_coe, hu] using
      integralDeltaOverQ_mul_qExpansion_qOverDelta)

/-- The q-expansion of the regularized modular invariant `qj` has integral coefficients. -/
theorem qj_isIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 qj) := by
  rw [← E4_pow_three_mul_qOverDelta_eq_qj,
    qExpansion_mul E4_pow_three_cuspFunction_analyticAt qOverDelta_cuspFunction_analyticAt]
  exact hasCoeffsIn_mul ℤ ℂ E4_pow_three_isIntegralPowerSeries
    qOverDelta_isIntegralPowerSeries_aux

/-- The integral coefficients of the q-expansion of `qj`. -/
def qjCoeffs : ℕ → ℤ := fun n ↦ (toIntegralPowerSeries qj_isIntegralPowerSeries).coeff n

/-- The integers `qjCoeffs n` are the q-expansion coefficients of `qj`. -/
lemma qjCoeffs_cast (n : ℕ) : ((qjCoeffs n : ℤ) : ℂ) = (qExpansion 1 qj).coeff n :=
  coeff_toIntegralPowerSeries_cast qj_isIntegralPowerSeries n

private lemma qj_vadd_one_aux (τ : ℍ) : qj ((1 : ℝ) +ᵥ τ) = qj τ := by
  simp only [qj, j, Pi.mul_apply, cexp_vadd_one_aux, E4_vadd_one_aux, Delta_vadd_one_aux]

/-- The complex extension of `qj` is one-periodic. -/
lemma qj_periodic : Periodic (qj ∘ UpperHalfPlane.ofComplex) 1 :=
  periodic_comp_ofComplex_of_vadd qj_vadd_one_aux

/-- The regularized modular invariant `qj` is differentiable on the upper half-plane. -/
lemma qj_mdifferentiable : MDiff qj :=
  mdifferentiable_cexp_aux.mul j_mdifferentiable

/-- The complex extension of `qj` is holomorphic on the open upper half-plane. -/
lemma qj_differentiableAt_of_im_pos : ∀ z : ℂ, 0 < Complex.im z →
    DifferentiableAt ℂ (qj ∘ UpperHalfPlane.ofComplex) z := fun z hz ↦
  UpperHalfPlane.mdifferentiableAt_iff.mp (qj_mdifferentiable ⟨z, hz⟩)

/-- The regularized modular invariant `qj` is bounded at infinity. -/
lemma qj_isBoundedAtImInfty : IsBoundedAtImInfty qj := by
  rw [← E4_pow_three_mul_qOverDelta_eq_qj]
  exact (by simpa [ModularForm.coe_pow] using bdd_at_infty (E4.pow 3) :
    IsBoundedAtImInfty (⇑E4 ^ 3)).mul (isBoundedAtImInfty_of_tendsto qOverDelta_tendsto_atImInfty)

/-- The q-expansion of `qj` converges to `qj` at every point of the upper half-plane. -/
lemma hasSum_qExpansion_qj {τ : ℍ} :
    HasSum (fun m : ℕ ↦ (qExpansion 1 qj).coeff m • 𝕢 1 τ ^ m) (qj τ) :=
  UpperHalfPlane.hasSum_qExpansion (h := 1) (f := qj) (by positivity) qj_periodic
    qj_mdifferentiable qj_isBoundedAtImInfty τ

/-- The convergent q-series reconstruction of the modular invariant `j`. -/
theorem j_eq_qjCoeffs_tsum (z : ℍ) :
    j z = qjCoeffs 0 / cexp (2 * π * Complex.I * z) +
      ∑' n, qjCoeffs (n + 1) * cexp (2 * π * Complex.I * z) ^ n := by
  have hs : HasSum (fun n : ℕ ↦ (qjCoeffs n : ℂ) * cexp (2 * π * Complex.I * z) ^ n) (qj z) := by
    simpa [smul_eq_mul, Periodic.qParam, qjCoeffs_cast] using hasSum_qExpansion_qj (τ := z)
  rw [show j z = qj z / cexp (2 * π * Complex.I * z) by simp [qj], ← hs.tsum_eq,
    hs.summable.tsum_eq_zero_add, add_div, ← tsum_div_const]
  simp [pow_succ, ← mul_assoc]

/-- The regularized modular invariant `qj` has constant coefficient one. -/
lemma qj_qExpansion_coeff_zero : (qExpansion 1 qj).coeff 0 = 1 := by
  have hE4 : constantCoeff (qExpansion 1 E4) = 1 := by
    simpa using congr_fun E4_q_exp 0
  have hqOverDelta : constantCoeff (qExpansion 1 qOverDelta) = 1 := by
    simp [← coeff_zero_eq_constantCoeff, qExpansion_coeff,
      cuspFunction_apply_zero_of_tendsto one_pos qOverDelta_tendsto_atImInfty]
  rw [← E4_pow_three_mul_qOverDelta_eq_qj,
    qExpansion_mul E4_pow_three_cuspFunction_analyticAt qOverDelta_cuspFunction_analyticAt,
    E4_pow_three_qExpansion]
  simp [hE4, hqOverDelta]

/-- The regularized `j`-function `qj` has constant coefficient `1`: at the cusp, `j` has a
simple pole with leading coefficient `1`. -/
lemma qjCoeffs_zero : qjCoeffs 0 = 1 := by
  exact_mod_cast (qjCoeffs_cast 0).trans qj_qExpansion_coeff_zero

/-- The cusp function of `qj` is analytic at `q = 0`. -/
lemma qj_cuspFunction_analyticAt : AnalyticAt ℂ (cuspFunction 1 qj) 0 :=
  analyticAt_cuspFunction_zero one_pos qj_periodic qj_mdifferentiable qj_isBoundedAtImInfty

/-! ### The pole of `j` at infinity -/

private lemma inv_mul_cuspFunction_qj_eq_j_aux :
    (fun q : ℂ ↦ q⁻¹ * cuspFunction 1 qj q) =ᶠ[𝓝[≠] (0 : ℂ)] cuspFunction 1 j := by
  have hqj : qj = fun τ : ℍ ↦ 𝕢 1 τ ^ 1 * j τ := funext fun τ ↦ by rw [qj_apply, pow_one]
  have h := cuspFunction_qpow_mul_eventuallyEq one_pos j 1
  rw [← hqj] at h
  filter_upwards [h, self_mem_nhdsWithin] with q hq (hq0 : q ≠ 0)
  rw [hq, pow_one, inv_mul_cancel_left₀ hq0]

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
    simpa using (meromorphicOrderAt_inv (f := id) (x := (0 : ℂ)))
  rw [meromorphicOrderAt_congr inv_mul_cuspFunction_qj_eq_j_aux.symm]
  change meromorphicOrderAt (((fun q : ℂ ↦ q⁻¹) * cuspFunction 1 qj)) (0 : ℂ) = _
  rw [mul_comm, meromorphicOrderAt_mul_of_ne_zero qj_cuspFunction_analyticAt (by simp [hqj0]),
    hqinvord]
  rfl

/-- The pole of `j` at infinity is not a removable singularity. -/
lemma j_cuspFunction_not_analyticAt : ¬ AnalyticAt ℂ (cuspFunction 1 j) 0 := by
  simp [analyticAt_cuspFunction_iff_poleOrder_eq_zero j_cuspFunction_meromorphicAt,
    j_poleOrder]

/-- Removing the pole of `j` at infinity yields the regularized modular invariant `qj`. -/
lemma j_poleRemoved : poleRemoved 1 j = qj := by
  ext τ
  rw [poleRemoved_apply, j_poleOrder, pow_one, qj_apply]

/-- The regularized q-expansion of `j` is the q-expansion of `qj`. -/
lemma j_to_qExpansion : to_qExpansion 1 j = qExpansion 1 qj := by
  rw [UpperHalfPlane.to_qExpansion, j_poleRemoved]

/-! ### The Laurent q-expansion of `j` -/

/-- The Laurent q-expansion of `j` has no coefficients below degree `-1`. -/
theorem j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one {n : ℤ} (hn : n < -1) :
    (laurentqExpansion 1 j).coeff n = 0 :=
  laurentqExpansion.coeff_eq_zero_of_lt' j_poleOrder hn

/-- From degree `-1` on, the Laurent q-expansion coefficients of `j` are the q-expansion
coefficients of `qj`, shifted by the order `1` of the pole of `j` at infinity. -/
theorem j_laurentQExpansion_coeff_of_neg_one_le {n : ℤ} (hn : -1 ≤ n) :
    (laurentqExpansion 1 j).coeff n = (qExpansion 1 qj).coeff (n + 1).toNat := by
  rw [laurentqExpansion.coeff_of_geq' j_poleOrder hn, j_to_qExpansion, Nat.cast_one]

/-- The Laurent q-expansion coefficient of `j` at `n - 1` is the `n`-th q-expansion coefficient
of `qj`. -/
theorem j_laurentQExpansion_coeff_sub_one (n : ℕ) :
    (laurentqExpansion 1 j).coeff ((n : ℤ) - 1) = (qExpansion 1 qj).coeff n := by
  rw [j_laurentQExpansion_coeff_of_neg_one_le (by omega), sub_add_cancel, Int.toNat_natCast]

/-- The Laurent q-expansion coefficients of `j`, with explicit integer witnesses: they vanish
below the simple pole at `-1`, and from there on they are the coefficients `qjCoeffs` of the
regularization `qj`, shifted by one. -/
theorem j_laurentQExpansion_coeff (n : ℤ) :
    (laurentqExpansion 1 j).coeff n =
      ((if n < -1 then 0 else qjCoeffs (n + 1).toNat : ℤ) : ℂ) := by
  split_ifs with hn
  · simpa using j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one hn
  · rw [j_laurentQExpansion_coeff_of_neg_one_le (not_lt.1 hn), qjCoeffs_cast]

/-- Every Laurent q-expansion coefficient of the modular invariant `j` is an integer. -/
theorem j_laurentQExpansion_isIntegral {n : ℤ} :
    ∃ m : ℤ, (laurentqExpansion 1 j).coeff n = m :=
  ⟨_, j_laurentQExpansion_coeff n⟩

end
