import XYin.NumberField.FieldExamples.SqrtNegSixQuadraticAlgebra.Units

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors QuadraticAlgebra

namespace XYin.NumberField.New.SqrtNegSixQuadraticAlgebra


/-! ## 7. Class group -/

/-- The ramified prime `(2, θ)` as an element of the monoid of nonzero ideals: the concrete
representative of the nontrivial ideal class. -/
noncomputable def ramifiedIdealOverTwo : (Ideal (𝓞 K))⁰ :=
  ⟨primeAboveTwo, by
    rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors]
    rw [absNorm_primeAboveTwo]
    norm_num⟩

/-- The unit ideal as the representative of the trivial ideal class. -/
abbrev unitIdealRepresentative : (Ideal (𝓞 K))⁰ := ⟨(⊤ : Ideal (𝓞 K)), by simp⟩

/-- **The class number of `ℚ(√-6)` is `2`**: the Minkowski bound is `(2/π)√24 ≈ 3.12`, the
primes `2` and `3` below it generate the class group, and their classes coincide and are
nontrivial (`(2,θ)(3,θ) = (θ)` is principal while `(2, θ)` is not). -/
theorem classNumber_eq_two : NumberField.classNumber K = 2 := by
  sorry

/-- The class group of `𝓞 K` is cyclic of order `2`. -/
theorem classGroupStructure : Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 2)) := by
  have hcard : Nat.card (ClassGroup (𝓞 K)) = 2 := by
    simpa [NumberField.classNumber, Nat.card_eq_fintype_card] using classNumber_eq_two
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨mulEquivOfPrimeCardEq hcard (by
    rw [show Nat.card (Multiplicative (ZMod 2)) = Nat.card (ZMod 2) from rfl, Nat.card_zmod])⟩

/-- The class of the ramified prime `(2, θ)` is nontrivial in the class group. -/
theorem classGroup_mk0_ramified_ne :
    ClassGroup.mk0 ramifiedIdealOverTwo ≠ ClassGroup.mk0 unitIdealRepresentative := by
  intro h
  have hprincipal : (ramifiedIdealOverTwo : Ideal (𝓞 K)).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem ramifiedIdealOverTwo)]
    rw [h]
    rw [ClassGroup.mk0_eq_one_iff (SetLike.coe_mem unitIdealRepresentative)]
    infer_instance
  exact not_isPrincipal_primeAboveTwo (by simpa [ramifiedIdealOverTwo] using hprincipal)

/-- Every ideal class is represented by either `𝓞 K` or the ramified prime `(2, θ)`. -/
theorem classGroupRepresentatives (C : ClassGroup (𝓞 K)) :
    C = ClassGroup.mk0 unitIdealRepresentative ∨ C = ClassGroup.mk0 ramifiedIdealOverTwo := by
  have hcard : Nat.card (ClassGroup (𝓞 K)) = 2 := by
    simpa [NumberField.classNumber, Nat.card_eq_fintype_card] using classNumber_eq_two
  obtain ⟨y, _hy_ne, hy_unique⟩ :=
    (Nat.card_eq_two_iff' (ClassGroup.mk0 unitIdealRepresentative)).mp hcard
  have hram_eq : ClassGroup.mk0 ramifiedIdealOverTwo = y :=
    hy_unique (ClassGroup.mk0 ramifiedIdealOverTwo) classGroup_mk0_ramified_ne
  by_cases hC : C = ClassGroup.mk0 unitIdealRepresentative
  · exact Or.inl hC
  · exact Or.inr ((hy_unique C hC).trans hram_eq.symm)

end XYin.NumberField.New.SqrtNegSixQuadraticAlgebra
