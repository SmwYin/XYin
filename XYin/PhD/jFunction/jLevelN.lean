/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.jFunction.jfunction

/-!
# Level-N transforms of the analytic j-invariant

This file studies the function obtained by evaluating the analytic modular invariant at `N · τ`.

## Main definitions

* `jN`: the function `τ ↦ j (N · τ)`.

## Main results

* `jN_slash_invariant`: `jN N` is invariant under `Γ₀(N)`.
* `jN_cuspFunction_meromorphicAt`: the cusp function of `jN N` is meromorphic at zero.
* `jN_differentiableAt`: `jN N` is differentiable on the upper half-plane.
-/

open Complex Filter Function MatrixGroups ModularForm ModularFormClass Real SlashInvariantFormClass
  UpperHalfPlane
open scoped Manifold

local notation "ℍₒ" => upperHalfPlaneSet

noncomputable section

private lemma natCast_mul_im_pos_aux (N : ℕ) [NeZero N] {z : ℂ} (hz : 0 < z.im) :
    0 < ((N : ℂ) * z).im := by
  simpa [Complex.mul_im] using mul_pos (Nat.cast_pos.mpr (NeZero.pos N)) hz

/-- The level-`N` transform `τ ↦ j (N · τ)` of the analytic modular invariant. -/
def jN (N : ℕ) [NeZero N] : ℍ → ℂ :=
  fun z ↦ j ⟨(N : ℂ) * (z : ℂ), natCast_mul_im_pos_aux N z.2⟩

private def gamma0Conjugate (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : SL(2, ℤ) :=
  let a := γ 0 0
  let b := γ 0 1
  let c := γ 1 0
  let d := γ 1 1
  ⟨!![a, ↑N * b; c / ↑N, d], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have hdvd : (N : ℤ) ∣ c :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
    have hdet : a * d - b * c = 1 := by
      have h := γ.prop
      rwa [Matrix.det_fin_two] at h
    rw [show ↑N * b * (c / ↑N) = b * (↑N * (c / ↑N)) from by ring,
      Int.mul_ediv_cancel' hdvd]
    linarith⟩

private lemma natCast_smul_gamma0_comm_aux (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    (⟨(N : ℂ) * ((γ • z : ℍ) : ℂ), natCast_mul_im_pos_aux N (γ • z).2⟩ : ℍ) =
      gamma0Conjugate N γ hγ •
        (⟨(N : ℂ) * (z : ℂ), natCast_mul_im_pos_aux N z.2⟩ : ℍ) := by
  ext
  simp only [coe_specialLinearGroup_apply, gamma0Conjugate, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  have hdvd : (N : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have hcN : (N : ℤ) * (γ 1 0 / ↑N) = γ 1 0 := Int.mul_ediv_cancel' hdvd
  have hR : (algebraMap ℤ ℝ) (γ 1 0 / ↑N) * (N : ℝ) =
      (algebraMap ℤ ℝ) (γ 1 0) := by
    rw [show (N : ℝ) = (algebraMap ℤ ℝ) (N : ℤ) from by simp [algebraMap_int_eq],
      ← map_mul, mul_comm, hcN]
  have hC : (↑((algebraMap ℤ ℝ) (γ 1 0 / ↑N)) : ℂ) * ((N : ℂ) * ↑z) =
      (↑((algebraMap ℤ ℝ) (γ 1 0)) : ℂ) * ↑z := by
    rw [← mul_assoc, show (↑((algebraMap ℤ ℝ) (γ 1 0 / ↑N)) : ℂ) * ↑N =
      ↑((algebraMap ℤ ℝ) (γ 1 0)) from by exact_mod_cast hR]
  rw [hC, map_mul,
    show (algebraMap ℤ ℝ) (N : ℤ) = (N : ℝ) from by simp [algebraMap_int_eq]]
  push_cast
  rw [← mul_div_assoc]
  congr 1
  ring

/-- The level-`N` transform `jN N` is invariant under `Γ₀(N)`. -/
lemma jN_slash_invariant (N : ℕ) [NeZero N] (γ : CongruenceSubgroup.Gamma0 N) :
    jN N ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = jN N := by
  ext z
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one, jN]
  rw [natCast_smul_gamma0_comm_aux N γ γ.prop z]
  exact j_modularGroup_smul _ _

private def qjN (N : ℕ) [NeZero N] : ℍ → ℂ :=
  fun z ↦ qj ⟨(N : ℂ) * (z : ℂ), natCast_mul_im_pos_aux N z.2⟩

private lemma natCast_mul_ofComplex_coe_aux (N : ℕ) [NeZero N] {w : ℂ} (hw : 0 < w.im) :
    (⟨(N : ℂ) * (UpperHalfPlane.ofComplex w : ℂ),
        natCast_mul_im_pos_aux N (UpperHalfPlane.ofComplex w).2⟩ : ℍ) =
      UpperHalfPlane.ofComplex ((N : ℂ) * w) :=
  UpperHalfPlane.ext <| by
    rw [UpperHalfPlane.coe_mk, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos (natCast_mul_im_pos_aux N hw)]

private lemma qjN_periodic_aux (N : ℕ) [NeZero N] :
    Periodic (qjN N ∘ UpperHalfPlane.ofComplex) N := by
  have hqNN : Periodic (qj ∘ UpperHalfPlane.ofComplex) ((N : ℂ) * ↑N) := by
    simpa [Nat.cast_mul] using qj_periodic.nat_mul (N * N)
  intro w
  simp only [Function.comp, qjN]
  by_cases hw : 0 < Complex.im w
  · rw [natCast_mul_ofComplex_coe_aux N (by simpa using hw), natCast_mul_ofComplex_coe_aux N hw]
    simpa [Function.comp, mul_add] using hqNN ((N : ℂ) * w)
  · have hwN : Complex.im (w + ↑N) ≤ 0 := by simpa using le_of_not_gt hw
    simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos (le_of_not_gt hw),
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hwN]

private lemma qjN_differentiableAt_aux (N : ℕ) [NeZero N] {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (qjN N ∘ UpperHalfPlane.ofComplex) z := by
  have hNz : 0 < Complex.im ((N : ℂ) * z) := natCast_mul_im_pos_aux N hz
  have hqj := qj_differentiableAt_of_im_pos _ hNz
  have hN : DifferentiableAt ℂ (fun w ↦ (N : ℂ) * w) z :=
    (differentiableAt_const _).mul differentiableAt_id
  refine (hqj.comp z hN).congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im) hz] with w hw
  simp only [Function.comp, qjN]
  rw [natCast_mul_ofComplex_coe_aux N hw]

private lemma qjN_mdifferentiable_aux (N : ℕ) [NeZero N] : MDiff (qjN N) :=
  UpperHalfPlane.mdifferentiable_iff.mpr fun _ hz ↦
    (qjN_differentiableAt_aux N hz).differentiableWithinAt

private lemma qjN_isBoundedAtImInfty_aux (N : ℕ) [NeZero N] : IsBoundedAtImInfty (qjN N) := by
  apply qj_isBoundedAtImInfty.comp_tendsto
  rw [show atImInfty = Filter.comap UpperHalfPlane.im Filter.atTop from rfl,
    Filter.tendsto_comap_iff]
  have him_eq : UpperHalfPlane.im ∘
      (fun x : ℍ ↦ (⟨(N : ℂ) * (x : ℂ), natCast_mul_im_pos_aux N x.2⟩ : ℍ)) =
        (fun x : ℝ ↦ (N : ℝ) * x) ∘ UpperHalfPlane.im := by
    ext τ
    simp only [Function.comp, UpperHalfPlane.im, Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, zero_mul, add_zero]
  rw [him_eq]
  exact (Filter.Tendsto.const_mul_atTop (Nat.cast_pos.mpr (NeZero.pos N))
    Filter.tendsto_id).comp Filter.tendsto_comap

private lemma qjN_cuspFunction_analyticAt_aux (N : ℕ) [NeZero N] :
    AnalyticAt ℂ (cuspFunction N (qjN N)) 0 :=
  (UpperHalfPlane.differentiableOn_cuspFunction_ball (Nat.cast_pos.mpr (NeZero.pos N))
    (qjN_periodic_aux N) (qjN_mdifferentiable_aux N) (qjN_isBoundedAtImInfty_aux N)).analyticAt
    (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

private lemma jN_cuspFunction_eq_aux (N : ℕ) [NeZero N] {q : ℂ} (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) : cuspFunction N (jN N) q = q⁻¹ ^ (N * N) * cuspFunction N (qjN N) q := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have him := Periodic.im_invQParam_pos_of_norm_lt_one hN hq hq0
  let τ : ℍ := ⟨Periodic.invQParam N q, him⟩
  have key : ∀ f : ℍ → ℂ, cuspFunction N f q = f τ := fun f ↦ by
    change Periodic.cuspFunction N _ q = _
    rw [Periodic.cuspFunction_eq_of_nonzero N _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hcexp : cexp (2 * ↑π * Complex.I *
        (↑(⟨(N : ℂ) * (τ : ℂ), natCast_mul_im_pos_aux N τ.2⟩ : ℍ) : ℂ)) =
      q ^ (N * N) := by
    rw [UpperHalfPlane.coe_mk]
    rw [show 2 * ↑π * Complex.I * ((N : ℂ) * (τ : ℂ)) = ↑(N * N) *
      (2 * ↑π * Complex.I * (τ : ℂ) / ↑N) by
        field_simp [Nat.cast_ne_zero.mpr (NeZero.ne N)]
        push_cast
        ring,
      Complex.exp_nat_mul]
    congr 1
    simpa [τ, Periodic.qParam] using Periodic.qParam_right_inv (ne_of_gt hN) hq0
  rw [key, key]
  simp only [jN, qjN, qj, Pi.mul_apply]
  rw [hcexp, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq0), one_mul]

/-- The cusp function of `jN N` is meromorphic at the origin. -/
lemma jN_cuspFunction_meromorphicAt (N : ℕ) [NeZero N] :
    MeromorphicAt (cuspFunction N (jN N)) (0 : ℂ) := by
  have hpow : MeromorphicAt (fun q : ℂ ↦ q⁻¹ ^ (N * N)) (0 : ℂ) :=
    ((MeromorphicAt.id (0 : ℂ)).inv).pow _
  refine (hpow.mul (qjN_cuspFunction_analyticAt_aux N).meromorphicAt).congr ?_
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds (by simpa [Metric.ball, dist_eq_norm]
      using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  filter_upwards [hnorm, self_mem_nhdsWithin] with q hq hq'
  exact (jN_cuspFunction_eq_aux N (by simpa using hq') hq).symm

/-- The level-`N` transform `jN N` is differentiable on the upper half-plane. -/
lemma jN_differentiableAt (N : ℕ) [NeZero N] {z : ℍₒ} :
    DifferentiableAt ℂ (jN N ∘ UpperHalfPlane.ofComplex) z := by
  obtain ⟨z, hz⟩ := z
  have hz' : 0 < z.im := hz
  have hNz : 0 < Complex.im ((N : ℂ) * z) := natCast_mul_im_pos_aux N hz'
  have hE4 := UpperHalfPlane.mdifferentiableAt_iff.mp
    (ModularFormClass.holo E4 ⟨↑N * z, hNz⟩)
  have hΔ := UpperHalfPlane.mdifferentiableAt_iff.mp
    (ModularFormClass.holo Delta ⟨↑N * z, hNz⟩)
  have hΔ0 : (Delta ∘ UpperHalfPlane.ofComplex) (↑N * z) ≠ 0 := by
    simp only [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hNz, Delta_apply]
    exact Δ_ne_zero _
  have hj : DifferentiableAt ℂ (j ∘ UpperHalfPlane.ofComplex) (↑N * z) := by
    simpa [j, Function.comp] using (hE4.pow 3).div hΔ hΔ0
  have hcomp :
      DifferentiableAt ℂ ((j ∘ UpperHalfPlane.ofComplex) ∘ fun w ↦ (N : ℂ) * w) z :=
    hj.comp z ((differentiableAt_const _).mul differentiableAt_id)
  have hEq : (jN N ∘ UpperHalfPlane.ofComplex)
      =ᶠ[nhds z] ((j ∘ UpperHalfPlane.ofComplex) ∘ fun w ↦ (N : ℂ) * w) := by
    filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im) hz']
      with w hw
    simp only [Function.comp, jN, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos (natCast_mul_im_pos_aux N hw)]
  exact hcomp.congr_of_eventuallyEq hEq
