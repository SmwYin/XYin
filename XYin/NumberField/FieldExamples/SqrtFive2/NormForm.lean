import XYin.NumberField.FieldExamples.SqrtFive2.RingOfIntegers

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace XYin.NumberField.SqrtFiveGoldenAdjoinRoot

/-! ## 4. Norm form -/

/-- Compatibility alias for the older `SqrtFive2` name. -/
abbrev goldenIntO : 𝓞 K := goldenInt

/-- The norm form of `ℚ(√5)` in the basis `1, φ`: the field norm of `x + yφ` is the binary
quadratic form `x² + xy - y²` (the "Fibonacci form"). -/
theorem norm_eq_normForm (x y : ℚ) :
    Algebra.norm ℚ (x • (1 : K) + y • goldenInteger) = x ^ 2 + x * y - y ^ 2 :=
  norm_eq_normForm' x y

/-- The integral norm form: on `𝓞 K = ℤ[φ]` the norm of `x + yφ` (with `x, y ∈ ℤ`) is
`x² + xy - y²`. -/
theorem intNorm_eq_normForm (x y : ℤ) :
    Algebra.norm ℤ (x • (1 : 𝓞 K) + y • goldenInt) = x ^ 2 + x * y - y ^ 2 := by
  have h1 : ((Algebra.norm ℤ (x • (1 : 𝓞 K) + y • goldenInt) : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap (𝓞 K) K (x • (1 : 𝓞 K) + y • goldenInt)) :=
    Algebra.coe_norm_int _
  have h2 : algebraMap (𝓞 K) K (x • (1 : 𝓞 K) + y • goldenInt) =
      (x : ℚ) • (1 : K) + (y : ℚ) • goldenInteger := by
    rw [map_add, map_zsmul, map_zsmul, map_one]
    rw [Int.cast_smul_eq_zsmul ℚ x (1 : K), Int.cast_smul_eq_zsmul ℚ y goldenInteger]
    rfl
  rw [h2, norm_eq_normForm] at h1
  exact_mod_cast h1

/-- The "Pell equation" for `ℚ(√5)`: `x + yφ` is a unit of `ℤ[φ]` iff `x² + xy - y² = ±1`.
The solutions are exactly the pairs of consecutive Fibonacci numbers, up to sign: combined
with `unit_eq_torsion_mul_fundamentalUnit_zpow`, every solution arises from `±φⁿ`, and
`φⁿ = F(n-1) + F(n)·φ`. -/
theorem isUnit_iff_normForm (x y : ℤ) :
    IsUnit (x • (1 : 𝓞 K) + y • goldenInt) ↔
      x ^ 2 + x * y - y ^ 2 = 1 ∨ x ^ 2 + x * y - y ^ 2 = -1 := by
  rw [NumberField.isUnit_iff_norm, RingOfIntegers.coe_norm, ← Algebra.coe_norm_int,
    intNorm_eq_normForm, abs_eq (by norm_num : (0 : ℚ) ≤ 1)]
  constructor
  · rintro (h | h)
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  · rintro (h | h)
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)


end XYin.NumberField.SqrtFiveGoldenAdjoinRoot
