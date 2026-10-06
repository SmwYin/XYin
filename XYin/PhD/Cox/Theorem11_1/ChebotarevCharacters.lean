/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite character orthogonality

Source: AINTLIB, `ForMathlib/CharacterOrthogonality.lean`, revision
`953409d221e42e247e32db31def5444fe60f3f87`. These generic algebraic inputs precede the number-field
character-sum adapters.
-/

noncomputable section

namespace Cox.Chebotarev

/-- Source: AINTLIB CharacterOrthogonality.lean, lines 40–45, the translation identity. -/
theorem sum_eq_zero_of_mulLeft_mul_const {H : Type*} [Group H] [Fintype H]
    {R : Type*} [Semiring R] [IsRightCancelMulZero R]
    (f : H → R) (h₀ : H) {c : R} (hc : c ≠ 1)
    (hf : ∀ h, f (h₀ * h) = c * f h) : ∑ h : H, f h = 0 := by
  refine eq_zero_of_mul_eq_self_left hc ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_bijective (h₀ * ·) (Group.mulLeft_bijective h₀) _ _ fun h ↦ (hf h).symm

/-- Source: AINTLIB CharacterOrthogonality.lean, lines 50–55, column orthogonality. -/
theorem sum_char_apply_eq_zero_of_ne_one {G : Type*} [CommGroup G] [Finite G]
    {R : Type*} [CommSemiring R] [IsRightCancelMulZero R]
    [HasEnoughRootsOfUnity R (Monoid.exponent G)]
    [Fintype (G →* Rˣ)] {g : G} (hg : g ≠ 1) :
    ∑ χ : G →* Rˣ, ((χ g : Rˣ) : R) = 0 := by
  obtain ⟨χ₀, hχ₀⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G R hg
  exact sum_eq_zero_of_mulLeft_mul_const _ χ₀ (fun h ↦ hχ₀ (Units.ext h))
    fun χ ↦ by rw [MonoidHom.mul_apply, Units.val_mul]

/-- Source: AINTLIB CharacterOrthogonality.lean, lines 59–64, row orthogonality. -/
theorem sum_char_self_eq_zero_of_ne_one {G : Type*} [Group G] [Fintype G]
    {R : Type*} [Semiring R] [IsRightCancelMulZero R] {χ : G →* Rˣ} (hχ : χ ≠ 1) :
    ∑ g : G, ((χ g : Rˣ) : R) = 0 := by
  obtain ⟨g₀, hg₀⟩ := DFunLike.ne_iff.mp hχ
  rw [MonoidHom.one_apply] at hg₀
  exact sum_eq_zero_of_mulLeft_mul_const _ g₀ (fun h ↦ hg₀ (Units.ext h))
    fun g ↦ by rw [map_mul, Units.val_mul]

/-- Source: AINTLIB CharacterOrthogonality.lean:77–83, the translated orthogonality identity. -/
theorem sum_char_translate_eq_card_or_zero {G : Type*} [CommGroup G] [Finite G] [DecidableEq G]
    {R : Type*} [CommSemiring R] [IsRightCancelMulZero R]
    [HasEnoughRootsOfUnity R (Monoid.exponent G)] [Fintype (G →* Rˣ)] (u s : G) :
    (∑ χ : G →* Rˣ, ((χ (u⁻¹ * s) : Rˣ) : R)) =
      if s = u then (Fintype.card (G →* Rˣ) : R) else 0 := by
  by_cases hs : s = u
  · subst hs; simp
  · rw [if_neg hs]
    exact sum_char_apply_eq_zero_of_ne_one fun h ↦ hs (inv_mul_eq_one.mp h).symm

/-- Source: AINTLIB CharacterOrthogonality.lean:71–100, finite Fourier inversion. -/
theorem card_mul_eq_sum_of_sum_char_mul_eq_zero {G : Type*} [CommGroup G] [Fintype G]
    {R : Type*} [CommSemiring R] [IsRightCancelMulZero R]
    [HasEnoughRootsOfUnity R (Monoid.exponent G)] [Fintype (G →* Rˣ)] (f : G → R)
    (hf : ∀ χ : G →* Rˣ, χ ≠ 1 → ∑ s : G, ((χ s : Rˣ) : R) * f s = 0) (u : G) :
    (Fintype.card (G →* Rˣ) : R) * f u = ∑ s : G, f s := by
  classical
  calc (Fintype.card (G →* Rˣ) : R) * f u
      = ∑ s : G, (if s = u then (Fintype.card (G →* Rˣ) : R) else 0) * f s := by
        simp
    _ = ∑ s : G, (∑ χ : G →* Rˣ, ((χ (u⁻¹ * s) : Rˣ) : R)) * f s := by
        refine Finset.sum_congr rfl fun s _ ↦ ?_; rw [sum_char_translate_eq_card_or_zero u s]
    _ = ∑ s : G, ∑ χ : G →* Rˣ, ((χ (u⁻¹ * s) : Rˣ) : R) * f s := by
        refine Finset.sum_congr rfl fun s _ ↦ ?_; rw [Finset.sum_mul]
    _ = ∑ χ : G →* Rˣ, ∑ s : G, ((χ (u⁻¹ * s) : Rˣ) : R) * f s := Finset.sum_comm
    _ = ∑ χ : G →* Rˣ, ((χ u⁻¹ : Rˣ) : R) * ∑ s : G, ((χ s : Rˣ) : R) * f s := by
        refine Finset.sum_congr rfl fun χ _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [map_mul, Units.val_mul, mul_assoc]
    _ = ∑ s : G, f s := by
        rw [Finset.sum_eq_single_of_mem (1 : G →* Rˣ) (Finset.mem_univ _)
          fun χ _ hχ ↦ by rw [hf χ hχ, mul_zero]]
        simp

/-- Source: AINTLIB CharacterOrthogonality.lean:107–114, cancellation of the dual cardinal. -/
theorem eq_of_sum_char_mul_eq_zero {G : Type*} [CommGroup G] [Fintype G]
    {R : Type*} [CommSemiring R] [IsRightCancelMulZero R] [CharZero R]
    [HasEnoughRootsOfUnity R (Monoid.exponent G)]
    (f : G → R) (hf : ∀ χ : G →* Rˣ, χ ≠ 1 → ∑ s : G, ((χ s : Rˣ) : R) * f s = 0) (u u' : G) :
    f u = f u' := by
  have : Fintype (G →* Rˣ) := Fintype.ofFinite _
  have : IsLeftCancelMulZero R := IsRightCancelMulZero.to_isLeftCancelMulZero
  have hcard0 : (Fintype.card (G →* Rˣ) : R) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact mul_left_cancel₀ hcard0
    ((card_mul_eq_sum_of_sum_char_mul_eq_zero f hf u).trans
      (card_mul_eq_sum_of_sum_char_mul_eq_zero f hf u').symm)

end Cox.Chebotarev
