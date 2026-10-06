/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.ModularFunctions.CuspGrowth
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

/-!
# Exponential growth at arbitrary cusps

The definition follows `OnePoint.IsBoundedAt`, replacing boundedness with at most exponential
growth. Checking one scaling matrix suffices, so the condition is independent of that choice.
-/

open Complex Filter UpperHalfPlane Matrix.SpecialLinearGroup Asymptotics
open scoped Topology MatrixGroups ModularForm

noncomputable section

namespace UpperHalfPlane

/-- Changing coordinates by an upper triangular matrix preserves finite exponential growth, in
every weight. -/
lemma IsOfExponentialGrowth.slash {f : ℍ → ℂ} {g : GL (Fin 2) ℝ} {k : ℤ}
    (hf : IsOfExponentialGrowth f) (hg : g 1 0 = 0) :
    IsOfExponentialGrowth (f ∣[k] g) := by
  obtain ⟨ρ, -, hb⟩ := isOfExponentialGrowth_iff_isBigO.1 hf
  have him (τ : ℍ) : (g • τ).im = |g 0 0 / g 1 1| * τ.im := by
    simp [im_smul, num, denom, hg, abs_div, abs_mul, abs_of_pos τ.im_pos, mul_div_right_comm]
  refine IsOfExponentialGrowth.of_isBigO_exp (ρ := ρ * |g 0 0 / g 1 1|) ?_
  rw [← isBigO_norm_left]
  suffices (fun τ ↦ (‖g.det.val ^ (k - 1)‖ * ‖g 1 1 ^ (-k)‖) * ‖f (g • τ)‖) =O[atImInfty]
      fun τ ↦ Real.exp (ρ * |g 0 0 / g 1 1| * τ.im) by
    simpa [ModularForm.slash_def, denom, hg, mul_assoc, mul_comm ‖f _‖]
  apply IsBigO.const_mul_left
  simpa [Function.comp_def, him, mul_assoc] using
    (hb.comp_tendsto (tendsto_smul_atImInfty hg)).norm_left

end UpperHalfPlane

namespace OnePoint

/-- A weight-`k` function has at most exponential growth at a cusp if every scaling
transform taking infinity to that cusp has at most exponential growth at infinity. -/
def IsExpBoundedAt (c : OnePoint ℝ) (f : ℍ → ℂ) (k : ℤ) : Prop :=
  ∀ g : GL (Fin 2) ℝ, g • ∞ = c → IsOfExponentialGrowth (f ∣[k] g)

/-- A weight-zero function has at most exponential growth at a cusp if each scaling transform
has at most exponential growth at infinity, uniformly in the real part. -/
def IsOfExponentialGrowthAt (c : OnePoint ℝ) (f : ℍ → ℂ) : Prop :=
  ∀ g : GL (Fin 2) ℝ, g • ∞ = c → IsOfExponentialGrowth (f ∣[(0 : ℤ)] g)

variable {c : OnePoint ℝ} {f f' : ℍ → ℂ} {k k' : ℤ} {g : GL (Fin 2) ℝ}

/-- The existing weight-zero condition is the specialization of the weighted condition. -/
lemma IsExpBoundedAt.iff_at_zero :
    IsExpBoundedAt c f 0 ↔ IsOfExponentialGrowthAt c f := Iff.rfl

/-- The existing weight-zero condition is the specialization of the weighted condition. -/
lemma isExpBoundedAt_zero_iff :
    IsExpBoundedAt c f 0 ↔ IsOfExponentialGrowthAt c f := IsExpBoundedAt.iff_at_zero

/-- Moving the cusp is equivalent to applying the same slash transform to the function. -/
lemma IsExpBoundedAt.smul_iff :
    IsExpBoundedAt (g • c) f k ↔ IsExpBoundedAt c (f ∣[k] g) k := by
  rw [IsExpBoundedAt, IsExpBoundedAt, (Equiv.mulLeft g⁻¹).forall_congr_left]
  simp [mul_smul, ← SlashAction.slash_mul]

/-- The intrinsic cusp condition at infinity is the ordinary growth condition. -/
lemma isExpBoundedAt_infty_iff : IsExpBoundedAt ∞ f k ↔ IsOfExponentialGrowth f :=
  ⟨fun h ↦ by simpa using h 1 (by simp),
    fun h _ hg ↦ h.slash (smul_infty_eq_self_iff.mp hg)⟩

/-- One scaling matrix is enough to test exponential growth at a cusp, in every weight. -/
lemma isExpBoundedAt_iff (hg : g • ∞ = c) :
    IsExpBoundedAt c f k ↔ IsOfExponentialGrowth (f ∣[k] g) :=
  ⟨fun hc ↦ hc g hg,
    by simp [← hg, IsExpBoundedAt.smul_iff, isExpBoundedAt_infty_iff]⟩

/-- Boundedness at a cusp implies at most exponential growth there. -/
lemma IsBoundedAt.isExpBoundedAt (h : IsBoundedAt c f k) : IsExpBoundedAt c f k :=
  fun g hg ↦ IsOfExponentialGrowth.of_isBoundedAtImInfty (h g hg)

lemma IsExpBoundedAt.add (hf : IsExpBoundedAt c f k) (hf' : IsExpBoundedAt c f' k) :
    IsExpBoundedAt c (f + f') k :=
  fun g hg ↦ by simpa only [SlashAction.add_slash] using (hf g hg).add (hf' g hg)

lemma IsExpBoundedAt.neg (hf : IsExpBoundedAt c f k) : IsExpBoundedAt c (-f) k :=
  fun g hg ↦ by simpa only [SlashAction.neg_slash] using (hf g hg).neg

/-- Multiplication adds the two weights and preserves the exponential cusp condition. -/
lemma IsExpBoundedAt.mul (hf : IsExpBoundedAt c f k) (hf' : IsExpBoundedAt c f' k') :
    IsExpBoundedAt c (f * f') (k + k') := fun g hg ↦ by
  rw [ModularForm.mul_slash]
  exact ((hf g hg).mul (hf' g hg)).smul _

lemma IsOfExponentialGrowthAt.smul_iff :
    IsOfExponentialGrowthAt (g • c) f ↔
      IsOfExponentialGrowthAt c (f ∣[(0 : ℤ)] g) := by
  rw [IsOfExponentialGrowthAt, IsOfExponentialGrowthAt,
    (Equiv.mulLeft g⁻¹).forall_congr_left]
  simp [mul_smul, ← SlashAction.slash_mul]

lemma isOfExponentialGrowthAt_infty_iff :
    IsOfExponentialGrowthAt ∞ f ↔ IsOfExponentialGrowth f :=
  ⟨fun h ↦ by simpa using h 1 (by simp),
    fun h _ hg ↦ h.slash (smul_infty_eq_self_iff.mp hg)⟩

/-- One scaling matrix is enough to test exponential growth at a cusp. -/
lemma isOfExponentialGrowthAt_iff (hg : g • ∞ = c) :
    IsOfExponentialGrowthAt c f ↔ IsOfExponentialGrowth (f ∣[(0 : ℤ)] g) :=
  ⟨fun hc ↦ hc g hg,
    by simp [← hg, IsOfExponentialGrowthAt.smul_iff, isOfExponentialGrowthAt_infty_iff]⟩

namespace IsOfExponentialGrowthAt

variable {f' : ℍ → ℂ}

lemma add (hf : IsOfExponentialGrowthAt c f) (hf' : IsOfExponentialGrowthAt c f') :
    IsOfExponentialGrowthAt c (f + f') :=
  fun g hg ↦ by simpa only [SlashAction.add_slash] using (hf g hg).add (hf' g hg)

lemma neg (hf : IsOfExponentialGrowthAt c f) : IsOfExponentialGrowthAt c (-f) :=
  fun g hg ↦ by simpa only [SlashAction.neg_slash] using (hf g hg).neg

lemma sub (hf : IsOfExponentialGrowthAt c f) (hf' : IsOfExponentialGrowthAt c f') :
    IsOfExponentialGrowthAt c (f - f') := by
  simpa only [sub_eq_add_neg] using hf.add hf'.neg

lemma mul (hf : IsOfExponentialGrowthAt c f) (hf' : IsOfExponentialGrowthAt c f') :
    IsOfExponentialGrowthAt c (f * f') := fun g hg ↦ by
  have h := ModularForm.mul_slash 0 0 g f f'
  rw [zero_add] at h
  rw [h]
  exact ((hf g hg).mul (hf' g hg)).smul _

lemma const_smul (a : ℂ) (hf : IsOfExponentialGrowthAt c f) :
    IsOfExponentialGrowthAt c (a • f) :=
  fun g hg ↦ by simpa only [ModularForm.smul_slash] using (hf g hg).smul _

lemma const (a : ℂ) : IsOfExponentialGrowthAt c fun _ ↦ a := fun g _ ↦ by
  convert IsOfExponentialGrowth.const (σ g a * ((|g.det.val| : ℝ) : ℂ) ^ (-1 : ℤ)) using 1
  funext τ
  simp [ModularForm.slash_apply]

end IsOfExponentialGrowthAt

/-- Constant functions have at most exponential growth at every cusp in weight zero. -/
lemma isExpBoundedAt_const (a : ℂ) : IsExpBoundedAt c (fun _ ↦ a) 0 :=
  IsOfExponentialGrowthAt.const a

section SL2Z

/-- At a cusp of `SL₂(ℤ)`, exponential growth can be tested with one integral scaling matrix. -/
lemma isOfExponentialGrowthAt_iff_exists_SL2Z (hc : IsCusp c 𝒮ℒ) :
    IsOfExponentialGrowthAt c f ↔
      ∃ γ : SL(2, ℤ), mapGL ℝ γ • ∞ = c ∧ IsOfExponentialGrowth (f ∣[(0 : ℤ)] γ) := by
  refine ⟨fun h ↦ ?_, fun ⟨γ, hγ, h⟩ ↦ (isOfExponentialGrowthAt_iff hγ).2 h⟩
  obtain ⟨γ, hγ⟩ := isCusp_SL2Z_iff'.mp hc
  exact ⟨γ, hγ.symm, h _ hγ.symm⟩

/-- At a cusp of `SL₂(ℤ)`, exponential growth holds iff it holds after every integral scaling
matrix. -/
lemma isOfExponentialGrowthAt_iff_forall_SL2Z (hc : IsCusp c 𝒮ℒ) :
    IsOfExponentialGrowthAt c f ↔
      ∀ γ : SL(2, ℤ), mapGL ℝ γ • ∞ = c → IsOfExponentialGrowth (f ∣[(0 : ℤ)] γ) := by
  refine ⟨fun h γ hγ ↦ h _ hγ, fun h ↦ ?_⟩
  obtain ⟨γ, hγ⟩ := isCusp_SL2Z_iff'.mp hc
  exact (isOfExponentialGrowthAt_iff hγ.symm).2 (h γ hγ.symm)

/-- A function all of whose integral transforms have exponential growth at infinity has
exponential growth at every cusp of `SL₂(ℤ)`. -/
lemma isOfExponentialGrowthAt_of_forall_SL2Z
    (h : ∀ γ : SL(2, ℤ), IsOfExponentialGrowth (f ∣[(0 : ℤ)] γ)) (hc : IsCusp c 𝒮ℒ) :
    IsOfExponentialGrowthAt c f :=
  (isOfExponentialGrowthAt_iff_forall_SL2Z hc).2 fun γ _ ↦ h γ

end SL2Z

end OnePoint
