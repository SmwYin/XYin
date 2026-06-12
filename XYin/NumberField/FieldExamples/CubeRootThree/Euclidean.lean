import XYin.NumberField.FieldExamples.CubeRootThree.ClassGroup

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CubeRootThree

/-! ## 8. Euclidean structure -/

/-- `ℚ(∛3)` is norm-Euclidean: division with remainder in `ℤ[θ]` with respect to the absolute
value of the field norm. This is a classical result for the pure cubic field of smallest
discriminant, and strengthens `isPrincipalIdealRing`. -/
theorem normEuclidean (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry


end NumberField.CubeRootThree
