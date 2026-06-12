import XYin.NumberField.FieldExamples.CyclotomicEight.RingOfIntegers

noncomputable section

open Module
open scoped NumberField nonZeroDivisors

namespace XYin.NumberField.New.CyclotomicEight

/-! ## 3. Discriminant -/

/-- The number-field discriminant of `ℚ(ζ₈)` is `256 = 2⁸`. In particular `2` is the only
ramified prime, cf. `ramified_iff_eq_two`. -/
theorem numberField_discr_eq : NumberField.discr K = (256 : ℤ) := by
  have : IsCyclotomicExtension {2 ^ 3} ℚ K := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
    infer_instance
  rw [IsCyclotomicExtension.Rat.discr_prime_pow 2 3 K,
    show ((2 : ℕ) ^ 3).totient = 4 from rfl]
  norm_num

/-- The discriminant of the explicit integral basis `1, ζ, ζ², ζ³` is `256`. -/
theorem concreteIntegralBasis_discr :
    Algebra.discr ℤ concreteIntegralBasis = (256 : ℤ) := by
  sorry


end XYin.NumberField.New.CyclotomicEight
