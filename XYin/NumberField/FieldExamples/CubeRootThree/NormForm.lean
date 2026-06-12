import XYin.NumberField.FieldExamples.CubeRootThree.Discriminant

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CubeRootThree

/-! ## 4. Norm form -/

/-- The integral norm form: on `𝓞 K = ℤ[θ]` the norm of `x + yθ + zθ²` (with `x, y, z ∈ ℤ`)
is `x³ + 3y³ + 9z³ - 9xyz`. -/
theorem intNorm_eq_normForm (x y z : ℤ) :
    Algebra.norm ℤ (x • (1 : 𝓞 K) + y • thetaInt + z • thetaInt ^ 2) =
      x ^ 3 + 3 * y ^ 3 + 9 * z ^ 3 - 9 * x * y * z := by
  have ht : ((thetaInt : 𝓞 K) : K) = cubeRootThree :=
    NumberField.RingOfIntegers.map_mk cubeRootThree cubeRootThree_integral
  -- prove the identity after the injective cast `ℤ ↪ ℚ`, reducing to `norm_eq_normForm`
  have key : (Algebra.norm ℤ (x • (1 : 𝓞 K) + y • thetaInt + z • thetaInt ^ 2) : ℚ)
      = ((x : ℚ) ^ 3 + 3 * (y : ℚ) ^ 3 + 9 * (z : ℚ) ^ 3 - 9 * x * y * z) := by
    rw [Algebra.coe_norm_int]
    push_cast [ht]
    rw [← Int.cast_smul_eq_zsmul ℚ x, ← Int.cast_smul_eq_zsmul ℚ y, ← Int.cast_smul_eq_zsmul ℚ z,
      norm_eq_normForm]
  exact_mod_cast key

/-- The "cubic Pell equation" for `ℚ(∛3)`: `x + yθ + zθ²` is a unit of `ℤ[θ]` iff
`x³ + 3y³ + 9z³ - 9xyz = ±1`. Combined with `unit_eq_torsion_mul_fundamentalUnit_zpow`, all
integer solutions of `x³ + 3y³ + 9z³ - 9xyz = ±1` arise from `±(θ² - 2)ⁿ`, `n ∈ ℤ`. -/
theorem isUnit_iff_normForm (x y z : ℤ) :
    IsUnit (x • (1 : 𝓞 K) + y • thetaInt + z • thetaInt ^ 2) ↔
      x ^ 3 + 3 * y ^ 3 + 9 * z ^ 3 - 9 * x * y * z = 1 ∨
        x ^ 3 + 3 * y ^ 3 + 9 * z ^ 3 - 9 * x * y * z = -1 := by
  rw [NumberField.isUnit_iff_norm, RingOfIntegers.coe_norm,
    ← Algebra.coe_norm_int, intNorm_eq_normForm]
  constructor
  · intro h
    have h' : |x ^ 3 + 3 * y ^ 3 + 9 * z ^ 3 - 9 * x * y * z| = 1 := by exact_mod_cast h
    exact (abs_eq (by norm_num)).mp h'
  · intro h
    have h' : |x ^ 3 + 3 * y ^ 3 + 9 * z ^ 3 - 9 * x * y * z| = 1 :=
      (abs_eq (by norm_num)).mpr h
    exact_mod_cast h'


end NumberField.CubeRootThree
