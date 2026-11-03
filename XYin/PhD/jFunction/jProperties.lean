/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.jFunction.jfunction

/-!
# Zeros and special values of the modular invariant

This file relates the zeros of `j` and `j - 1728` to the Eisenstein series, proves the
special values `j(i) = 1728` and `j(ρ) = 0`, and describes its simple pole at infinity.
-/

open Complex CongruenceSubgroup Filter Function ModularForm UpperHalfPlane ModularGroup
  SlashInvariantForm
open scoped MatrixGroups Topology

noncomputable section

/-- The zeros of `j` are exactly the zeros of the weight-four Eisenstein series. -/
lemma j_eq_zero_iff (τ : ℍ) : j τ = 0 ↔ E₄ τ = 0 := by
  simp [j, discriminant_ne_zero]

/-- Subtracting `1728` from `j` gives the quotient `E₆² / Δ`. -/
lemma j_sub_1728_eq (τ : ℍ) : j τ - 1728 = E₆ τ ^ 2 / discriminant τ := by
  have hrel : E₄ τ ^ 3 - E₆ τ ^ 2 = 1728 * discriminant τ := by
    rw [discriminant_eq_E₄_cube_sub_E₆_sq τ]
    ring
  rw [j, eq_div_iff (discriminant_ne_zero τ), sub_mul,
    div_mul_cancel₀ _ (discriminant_ne_zero τ)]
  linear_combination hrel

/-- The points where `j = 1728` are exactly the zeros of the weight-six Eisenstein series. -/
lemma j_eq_1728_iff (τ : ℍ) : j τ = 1728 ↔ E₆ τ = 0 := by
  rw [← sub_eq_zero, j_sub_1728_eq]
  simp [discriminant_ne_zero]

/-- The weight-six Eisenstein series vanishes at the elliptic point `i`. -/
lemma E₆_apply_I : E₆ UpperHalfPlane.I = 0 := by
  have : SlashInvariantFormClass (ModularForm 𝒮ℒ 6) Γ(1) 6 :=
    Gamma_one_coe_eq_SL ▸ inferInstance
  have h := slash_action_eqn_SL'' E₆ (mem_Gamma_one S) UpperHalfPlane.I
  have hfix : S • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [modular_S_smul, UpperHalfPlane.ext_iff]
    simp
  rw [hfix, show denom (S : SL(2, ℤ)) (UpperHalfPlane.I : ℂ) = Complex.I from
    denom_S UpperHalfPlane.I] at h
  norm_num at h
  linear_combination h / 2

/-- The classical modular invariant takes the value `1728` at `i`. -/
lemma j_apply_I : j UpperHalfPlane.I = 1728 :=
  (j_eq_1728_iff UpperHalfPlane.I).2 E₆_apply_I

/-- The weight-four Eisenstein series vanishes at the cubic elliptic point `ρ`. -/
lemma E₄_apply_rho : E₄ ρ = 0 := by
  have : SlashInvariantFormClass (ModularForm 𝒮ℒ 4) Γ(1) 4 :=
    Gamma_one_coe_eq_SL ▸ inferInstance
  have hfix : (S * T) • ρ = ρ := stabilizer_ρ.mpr (by simp)
  have h := slash_action_eqn_SL'' E₄ (mem_Gamma_one (S * T)) ρ
  have hden : denom (S * T : SL(2, ℤ)) (ρ : ℂ) = (ρ : ℂ) + 1 := by
    norm_num [denom, Matrix.SpecialLinearGroup.coe_mul, coe_S, coe_T, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.map_apply]
  rw [hfix, hden] at h
  norm_num only [zpow_ofNat] at h
  have hpower : ((ρ : ℂ) + 1) ^ 4 = (ρ : ℂ) ^ 2 := by
    linear_combination ((ρ : ℂ) ^ 2 + 3 * ρ + 1) * ρ_sq
  rw [hpower] at h
  by_contra hn
  have hscalar : (ρ : ℂ) ^ 2 = 1 := mul_right_cancel₀ hn (by simpa using h.symm)
  rw [ρ_sq] at hscalar
  have him := congrArg Complex.im hscalar
  simp at him
  linarith [ρ.im_pos]

/-- The classical modular invariant vanishes at `ρ = (-1 + i√3) / 2`. -/
lemma j_apply_rho : j ρ = 0 := (j_eq_zero_iff ρ).2 E₄_apply_rho

/-- The modular invariant takes the value `1728` on the modular orbit of `i`. -/
lemma j_apply_smul_I (γ : SL(2, ℤ)) : j (γ • UpperHalfPlane.I) = 1728 := by
  rw [j_modularGroup_smul, j_apply_I]

/-- The modular invariant vanishes on the modular orbit of `ρ`. -/
lemma j_apply_smul_rho (γ : SL(2, ℤ)) : j (γ • ρ) = 0 := by
  rw [j_modularGroup_smul, j_apply_rho]

/-- The modular invariant is complex analytic at every point of the upper half-plane. -/
lemma j_analyticAt (τ : ℍ) : AnalyticAt ℂ (j ∘ ofComplex) (τ : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp j_mdifferentiable).analyticOnNhd
    isOpen_upperHalfPlaneSet _ τ.im_pos

/-- The modular invariant has no poles inside the upper half-plane. -/
lemma j_meromorphicOrderAt_nonneg (τ : ℍ) :
    0 ≤ meromorphicOrderAt (j ∘ ofComplex) (τ : ℂ) :=
  (j_analyticAt τ).meromorphicOrderAt_nonneg

/-- The signed meromorphic order of `j` at the cusp is `-1`. -/
lemma j_cuspFunction_order : meromorphicOrderAt (cuspFunction 1 j) 0 = (-1 : WithTop ℤ) := by
  have h0 : poleOrder 1 j ≠ 0 := by simp [j_poleOrder]
  simpa [j_poleOrder] using meromorphicOrderAt_cuspFunction_eq_neg_poleOrder h0

/-- The cusp function of `j` tends to infinity at its simple pole. -/
lemma j_cuspFunction_tendsto_cobounded :
    Tendsto (cuspFunction 1 j) (𝓝[≠] 0) (Bornology.cobounded ℂ) :=
  tendsto_cobounded_of_meromorphicOrderAt_neg (by
    rw [j_cuspFunction_order]
    change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
    exact WithTop.coe_lt_coe.mpr (by norm_num))

/-- The modular invariant tends to infinity as the imaginary part tends to infinity. -/
lemma j_tendsto_cobounded_atImInfty : Tendsto j atImInfty (Bornology.cobounded ℂ) := by
  have hq := (Periodic.qParam_tendsto (h := 1) one_pos).comp tendsto_coe_atImInfty
  have hj := j_cuspFunction_tendsto_cobounded.comp hq
  exact hj.congr fun τ ↦ UpperHalfPlane.eq_cuspFunction τ one_ne_zero j_periodic

/-- The absolute value of `j` tends to infinity at the cusp. -/
lemma tendsto_norm_j_atImInfty : Tendsto (fun τ : ℍ ↦ ‖j τ‖) atImInfty atTop :=
  tendsto_norm_atTop_iff_cobounded.mpr j_tendsto_cobounded_atImInfty
