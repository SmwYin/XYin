import XYin.NumberField.FieldExamples.SqrtFive2.ClassGroup

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial

namespace XYin.NumberField.SqrtFiveGoldenAdjoinRoot

/-! ## 8. Euclidean structure -/

/-- `ℚ(√5)` is norm-Euclidean: division with remainder in `ℤ[φ]` with respect to the
absolute value of the field norm. This strengthens `isPrincipalIdealRing`. -/
theorem normEuclidean (a b : 𝓞 QSqrtFive) (hb : b ≠ 0) :
    ∃ q r : 𝓞 QSqrtFive, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry


end XYin.NumberField.SqrtFiveGoldenAdjoinRoot
