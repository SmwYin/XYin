import XYin.NumberField.FieldExamples.SqrtTwo.ClassGroup

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial

namespace XYin.NumberField.SqrtTwo

/-! ## 8. Euclidean structure -/

/-- `ℚ(√2)` is norm-Euclidean: division with remainder in `ℤ[√2]` with respect to the
absolute value of the field norm. This is the classical Euclidean algorithm for the real
quadratic field of smallest discriminant, and strengthens
`sqrtTwo_ringOfIntegers_isPrincipalIdealRing`. -/
theorem normEuclidean (a b : O2) (hb : b ≠ 0) :
    ∃ q r : O2, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry


end XYin.NumberField.SqrtTwo
