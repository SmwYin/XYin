import XYin.NumberField.FieldExamples.CyclotomicFive.ClassGroup

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicFive

/-! ## 8. Euclidean structure -/

/-- `ℤ[ζ₅]` is norm-Euclidean with respect to the absolute value of the field norm. -/
theorem normEuclidean (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry


end NumberField.CyclotomicFive

-- AUTO_AXIOM_CHECK_MARKER_DO_NOT_COMMIT
#print axioms NumberField.CyclotomicFive.normEuclidean
