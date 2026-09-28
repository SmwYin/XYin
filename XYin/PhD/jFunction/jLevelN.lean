/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.jFunction.jfunction

/-!
# Level-N transforms of the analytic j-invariant

This file studies the function `levelJ N : τ ↦ j (N · τ)` obtained by evaluating the analytic
modular invariant at `N · τ`. Its meromorphy at the cusps is proved in
`XYin.PhD.Cox.ModularFunction.LevelJ` (`Cox.levelJ_cuspData`).

## Main definitions

* `UpperHalfPlane.natScale`: the scaling `τ ↦ N · τ` of the upper half-plane, an instance of
  mathlib's action `UpperHalfPlane.posRealAction` of the positive reals.
* `levelJ`: the function `τ ↦ j (N · τ)`.

## Main results

* `levelJ_slash_invariant`: `levelJ N` is invariant under `Γ₀(N)`.
* `levelJ_differentiableAt`: `levelJ N` is differentiable on the upper half-plane.
-/

open Complex Filter Function MatrixGroups ModularForm ModularFormClass Real SlashInvariantFormClass
  UpperHalfPlane
open scoped Manifold

local notation "ℍₒ" => upperHalfPlaneSet

noncomputable section

/-- The scaling `τ ↦ N · τ` of the upper half-plane by a nonzero natural number, via mathlib's
action of the positive reals. -/
def UpperHalfPlane.natScale (N : ℕ) [NeZero N] (τ : ℍ) : ℍ :=
  (⟨(N : ℝ), Nat.cast_pos.mpr (NeZero.pos N)⟩ : {x : ℝ // 0 < x}) • τ

@[simp]
lemma UpperHalfPlane.coe_natScale (N : ℕ) [NeZero N] (τ : ℍ) :
    (natScale N τ : ℂ) = N * τ := by
  simp [natScale, Complex.real_smul]

/-- The level-`N` transform `τ ↦ j (N · τ)` of the analytic modular invariant. -/
def levelJ (N : ℕ) [NeZero N] : ℍ → ℂ :=
  fun z ↦ j (natScale N z)

/-- `levelJ N τ = j (N · τ)`, with `N · τ` the scaling `UpperHalfPlane.natScale`. -/
lemma levelJ_apply (N : ℕ) [NeZero N] (τ : ℍ) : levelJ N τ = j (natScale N τ) :=
  rfl

private lemma natCast_dvd_of_mem_Gamma0_aux {N : ℕ} {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : (N : ℤ) ∣ γ 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)

/-- The conjugate `diag(N, 1) γ diag(N, 1)⁻¹` of `γ ∈ Γ₀(N)`, an element of `SL₂(ℤ)`. -/
private def gamma0Conjugate (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : SL(2, ℤ) :=
  ⟨!![γ 0 0, N * γ 0 1; γ 1 0 / N, γ 1 1], by
    obtain ⟨c, hc⟩ := natCast_dvd_of_mem_Gamma0_aux hγ
    have hdet := γ.prop
    rw [Matrix.det_fin_two, hc] at hdet
    rw [Matrix.det_fin_two_of, hc, Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
    linear_combination hdet⟩

private lemma natScale_smul_gamma0_comm_aux (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    natScale N (γ • z) = gamma0Conjugate N γ hγ • natScale N z := by
  obtain ⟨c, hc⟩ := natCast_dvd_of_mem_Gamma0_aux hγ
  ext
  simp only [coe_natScale, coe_specialLinearGroup_apply, gamma0Conjugate, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, hc,
    Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  push_cast
  ring

/-- The level-`N` transform `levelJ N` is invariant under `Γ₀(N)`. -/
lemma levelJ_slash_invariant (N : ℕ) [NeZero N] (γ : CongruenceSubgroup.Gamma0 N) :
    levelJ N ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = levelJ N := by
  ext z
  rw [SL_slash_apply, zpow_neg, zpow_zero, inv_one, mul_one, levelJ_apply, levelJ_apply,
    natScale_smul_gamma0_comm_aux N γ γ.prop z]
  exact j_modularGroup_smul _ _

private lemma natCast_mul_im_pos_aux (N : ℕ) [NeZero N] {w : ℂ} (hw : 0 < w.im) :
    0 < ((N : ℂ) * w).im := by
  simpa using mul_pos (Nat.cast_pos.mpr (NeZero.pos N)) hw

private lemma natScale_ofComplex_aux (N : ℕ) [NeZero N] {w : ℂ} (hw : 0 < w.im) :
    natScale N (UpperHalfPlane.ofComplex w) = UpperHalfPlane.ofComplex ((N : ℂ) * w) := by
  ext
  rw [coe_natScale, ofComplex_apply_of_im_pos hw,
    ofComplex_apply_of_im_pos (natCast_mul_im_pos_aux N hw), coe_mk]

/-- The level-`N` transform `levelJ N` is differentiable on the upper half-plane. -/
lemma levelJ_differentiableAt (N : ℕ) [NeZero N] {z : ℍₒ} :
    DifferentiableAt ℂ (levelJ N ∘ UpperHalfPlane.ofComplex) z := by
  obtain ⟨z, hz⟩ := z
  refine ((UpperHalfPlane.mdifferentiableAt_iff.mp
    (j_mdifferentiable ⟨↑N * z, natCast_mul_im_pos_aux N hz⟩)).comp z
    (differentiableAt_id.const_mul (N : ℂ))).congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im) hz] with w hw
  simp only [Function.comp, levelJ]
  rw [natScale_ofComplex_aux N hw]
  rfl
