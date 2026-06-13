/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.RingOfIntegers

/-!
# `ℚ(√2)` Norm form

This file develops the norm form part of the `ℚ(√2)` number field example.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtTwo

/-- The norm form of `ℚ(√2)` in `QuadraticAlgebra` coordinates: the field norm of an element
with components `(re, im)` (i.e. `re + im·√2`) is the binary quadratic form `re² - 2·im²`,
the principal form of discriminant `8`. -/
theorem norm_eq_normForm (x : QSqrtTwo) :
    Algebra.norm ℚ x = x.re ^ 2 - 2 * x.im ^ 2 := by
  rw [Algebra.norm_apply]
  change LinearMap.det (DistribSMul.toLinearMap ℚ QSqrtTwo x) = x.re ^ 2 - 2 * x.im ^ 2
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm, QuadraticAlgebra.norm_def]
  ring

/-- The integral norm form: on `𝓞 K = ℤ[√2]` the norm of `x + y√2` (with `x, y ∈ ℤ`) is
`x² - 2y²`. -/
theorem intNorm_eq_normForm (x y : ℤ) :
    Algebra.norm ℤ (x • (1 : O2) + y • sqrtTwoInteger) = x ^ 2 - 2 * y ^ 2 := by
  have h1 : ((Algebra.norm ℤ (x • (1 : O2) + y • sqrtTwoInteger) : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap O2 QSqrtTwo (x • (1 : O2) + y • sqrtTwoInteger)) :=
    Algebra.coe_norm_int (K := QSqrtTwo) _
  have h2 : algebraMap O2 QSqrtTwo (x • (1 : O2) + y • sqrtTwoInteger) =
      (x : ℚ) • (1 : QSqrtTwo) + (y : ℚ) • sqrtTwoRoot := by
    rw [map_add, map_zsmul, map_zsmul, map_one]
    rw [Int.cast_smul_eq_zsmul ℚ x (1 : QSqrtTwo),
      Int.cast_smul_eq_zsmul ℚ y sqrtTwoRoot]
    rfl
  rw [h2, norm_eq_normForm] at h1
  norm_num at h1
  have h3 : (Algebra.norm ℤ ((x : O2) + (y : O2) * sqrtTwoInteger)) =
      x ^ 2 - 2 * y ^ 2 := by
    exact_mod_cast h1
  simpa [zsmul_eq_mul] using h3

/-- The Pell equation for `ℚ(√2)`: `x + y√2` is a unit of `ℤ[√2]` iff `x² - 2y² = ±1`.
Combined with `sqrtTwoFundamentalUnit_generates_unitGroup`, all integer solutions of
`x² - 2y² = ±1` arise from `±(1 + √2)ⁿ`, `n ∈ ℤ`. -/
theorem isUnit_iff_normForm (x y : ℤ) :
    IsUnit (x • (1 : O2) + y • sqrtTwoInteger) ↔
      x ^ 2 - 2 * y ^ 2 = 1 ∨ x ^ 2 - 2 * y ^ 2 = -1 := by
  rw [NumberField.isUnit_iff_norm, RingOfIntegers.coe_norm, ← Algebra.coe_norm_int,
    intNorm_eq_normForm, abs_eq (by norm_num : (0 : ℚ) ≤ 1)]
  constructor
  · rintro (h | h)
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  · rintro (h | h)
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)


end NumberField.SqrtTwo
