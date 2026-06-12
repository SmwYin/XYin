import XYin.NumberField.FieldExamples.SqrtFive2.RingOfIntegers

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial

namespace XYin.NumberField.SqrtFiveGoldenAdjoinRoot

/-! ## 4. Norm form -/

/-- `φ` as an element of the abstract ring of integers `𝓞 QSqrtFive`. -/
noncomputable def goldenIntO : 𝓞 QSqrtFive := ⟨goldenRoot, goldenRoot_isIntegral⟩

/-- The integral norm form: on `𝓞 K = ℤ[φ]` the norm of `x + yφ` (with `x, y ∈ ℤ`) is
`x² + xy - y²`, the principal form of discriminant `5`. -/
theorem intNorm_eq_normForm (x y : ℤ) :
    Algebra.norm ℤ (x • (1 : 𝓞 QSqrtFive) + y • goldenIntO) = x ^ 2 + x * y - y ^ 2 := by
  sorry

/-- The Pell-type unit equation for `ℚ(√5)`: `x + yφ` is a unit of `ℤ[φ]` iff
`x² + xy - y² = ±1`. Combined with `fundamentalUnit_generates`, all integer solutions arise
from `±φⁿ`, `n ∈ ℤ`; concretely `φⁿ = F(n-1) + F(n)·φ`, so the solutions are exactly the
pairs of consecutive Fibonacci numbers (up to sign). -/
theorem isUnit_iff_normForm (x y : ℤ) :
    IsUnit (x • (1 : 𝓞 QSqrtFive) + y • goldenIntO) ↔
      x ^ 2 + x * y - y ^ 2 = 1 ∨ x ^ 2 + x * y - y ^ 2 = -1 := by
  sorry


end XYin.NumberField.SqrtFiveGoldenAdjoinRoot
