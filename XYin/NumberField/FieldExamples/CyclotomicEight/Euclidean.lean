import XYin.NumberField.FieldExamples.CyclotomicEight.ClassGroup

noncomputable section

open Module
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicEight

/-! ## 8. Euclidean structure -/

/-- `ℚ(ζ₈)` is norm-Euclidean. -/
theorem normEuclidean (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry


end NumberField.CyclotomicEight
