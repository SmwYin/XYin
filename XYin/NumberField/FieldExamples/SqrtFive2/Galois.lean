import XYin.NumberField.FieldExamples.SqrtFive2.Euclidean

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace XYin.NumberField.SqrtFiveGoldenAdjoinRoot

/-! ## 9. Galois group -/

/-- The identity automorphism of `ℚ(√5)`. -/
noncomputable def idAut : K ≃ₐ[ℚ] K := AlgEquiv.refl

/-- The nontrivial conjugation automorphism, sending `√5` to `-√5`. -/
noncomputable def conjugation : K ≃ₐ[ℚ] K := conj'

/-- The conjugation automorphism sends `√5` to `-√5`. -/
theorem conjugation_apply_sqrtFive : conjugation sqrtFive = -sqrtFive := conj'_root

/-- The conjugation automorphism sends the golden ratio `φ` to its conjugate `1 - φ = -1/φ`. -/
theorem conjugation_apply_goldenInteger : conjugation goldenInteger = 1 - goldenInteger :=
  conj'_golden

theorem exists_conj :
    ∃ σ : K ≃ₐ[ℚ] K, σ goldenRoot = 1 - goldenRoot :=
  ⟨conjugation, conjugation_apply_goldenInteger⟩

/-- Quadratic extensions are Galois: `ℚ(√5)/ℚ` is a Galois extension. (Contrast with the
non-Galois cubic `ℚ(∛3)/ℚ`.) -/
theorem isGalois : IsGalois ℚ K := inferInstance

/-- Every `ℚ`-automorphism of `K` is the identity or the conjugation. -/
theorem aut_eq_or (σ : K ≃ₐ[ℚ] K) : σ = idAut ∨ σ = conjugation := aut_eq_or' σ

theorem aut_apply_goldenRoot (σ : K ≃ₐ[ℚ] K) :
    σ goldenRoot = goldenRoot ∨ σ goldenRoot = 1 - goldenRoot := by
  rcases aut_eq_or σ with hσ | hσ
  · left
    rw [hσ]
    rfl
  · right
    rw [hσ]
    exact conjugation_apply_goldenInteger

/-- The Galois group of `ℚ(√5)/ℚ` is cyclic of order `2`. -/
theorem galoisGroupStructure : Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 2)) := by
  have hconj_ne : conjugation ≠ idAut := by
    intro h
    have h1 : conjugation sqrtFive = sqrtFive := by rw [h]; rfl
    rw [conjugation_apply_sqrtFive] at h1
    have h2 : (2 : K) * sqrtFive = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · norm_num at h3
    · have h4 := sqrtFive_sq
      rw [h3] at h4
      norm_num at h4
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨idAut, conjugation, Ne.symm hconj_ne, ?_⟩
    ext σ
    simp [aut_eq_or σ]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨mulEquivOfPrimeCardEq hcard (by
    rw [show Nat.card (Multiplicative (ZMod 2)) = Nat.card (ZMod 2) from rfl, Nat.card_zmod])⟩



end XYin.NumberField.SqrtFiveGoldenAdjoinRoot
