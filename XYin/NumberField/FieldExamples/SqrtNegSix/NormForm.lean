/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.RingOfIntegers

/-!
# `ℚ(√-6)` Norm form

This file develops the norm form part of the `ℚ(√-6)` number field example.
-/

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors QuadraticAlgebra

namespace NumberField.SqrtNegSix

/-- The norm form of `ℚ(√-6)` in the basis `1, θ`: the field norm of `x + yθ` is the
positive-definite binary quadratic form `x² + 6y²`. -/
theorem norm_eq_normForm (x y : ℚ) :
    Algebra.norm ℚ (x • (1 : K) + y • θ) = x ^ 2 + 6 * y ^ 2 := by
  have h : Algebra.norm ℚ (x • (1 : K) + y • θ) =
      QuadraticAlgebra.norm (x • (1 : K) + y • θ) := by
    rw [Algebra.norm_apply, ← QuadraticAlgebra.det_toLinearMap_eq_norm]
    congr 1
  rw [h]
  simp [QuadraticAlgebra.norm_def, θ]
  ring

/-- The integral norm form: on `𝓞 K = ℤ[θ]` the norm of `x + yθ` (with `x, y ∈ ℤ`) is
`x² + 6y²`. -/
theorem intNorm_eq_normForm (x y : ℤ) :
    Algebra.norm ℤ (x • (1 : 𝓞 K) + y • thetaInt) = x ^ 2 + 6 * y ^ 2 := by
  have h1 : ((Algebra.norm ℤ (x • (1 : 𝓞 K) + y • thetaInt) : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap (𝓞 K) K (x • (1 : 𝓞 K) + y • thetaInt)) :=
    Algebra.coe_norm_int _
  have h2 : algebraMap (𝓞 K) K (x • (1 : 𝓞 K) + y • thetaInt) =
      (x : ℚ) • (1 : K) + (y : ℚ) • θ := by
    rw [map_add, map_zsmul, map_zsmul, map_one]
    rw [Int.cast_smul_eq_zsmul ℚ x (1 : K), Int.cast_smul_eq_zsmul ℚ y θ]
    rfl
  rw [h2, norm_eq_normForm] at h1
  exact_mod_cast h1

theorem normForm_ne_two (x y : ℤ) : x ^ 2 + 6 * y ^ 2 ≠ 2 := by
  intro h
  have hy_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  have hx_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hy0 : y ^ 2 = 0 := by nlinarith
  have hx2 : x ^ 2 = 2 := by nlinarith
  have hx_le : x ≤ 1 := by nlinarith [sq_nonneg (x - 1)]
  have hx_ge : -1 ≤ x := by nlinarith [sq_nonneg (x + 1)]
  interval_cases x <;> norm_num at hx2

private theorem normForm_ne_three (x y : ℤ) : x ^ 2 + 6 * y ^ 2 ≠ 3 := by
  intro h
  have hy_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  have hx_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hy0 : y ^ 2 = 0 := by nlinarith
  have hx3 : x ^ 2 = 3 := by nlinarith
  have hx_le' : 4 * x ≤ 7 := by nlinarith [sq_nonneg (x - 2)]
  have hx_ge' : -7 ≤ 4 * x := by nlinarith [sq_nonneg (x + 2)]
  have hx_le : x ≤ 1 := by omega
  have hx_ge : -1 ≤ x := by omega
  interval_cases x <;> norm_num at hx3

private theorem normForm_ne_five (x y : ℤ) : x ^ 2 + 6 * y ^ 2 ≠ 5 := by
  intro h
  have hy_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  have hx_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hy0 : y ^ 2 = 0 := by nlinarith
  have hx5 : x ^ 2 = 5 := by nlinarith
  have hx_le' : 6 * x ≤ 14 := by nlinarith [sq_nonneg (x - 3)]
  have hx_ge' : -14 ≤ 6 * x := by nlinarith [sq_nonneg (x + 3)]
  have hx_le : x ≤ 2 := by omega
  have hx_ge : -2 ≤ x := by omega
  interval_cases x <;> norm_num at hx5

/-- The unit equation for `ℚ(√-6)`: `x + yθ` is a unit iff `x² + 6y² = 1`, i.e. iff
`(x, y) = (±1, 0)`. The form is positive definite, so there is no Pell phenomenon. -/
theorem isUnit_iff_normForm (x y : ℤ) :
    IsUnit (x • (1 : 𝓞 K) + y • thetaInt) ↔ x ^ 2 + 6 * y ^ 2 = 1 := by
  rw [NumberField.isUnit_iff_norm, RingOfIntegers.coe_norm, ← Algebra.coe_norm_int,
    intNorm_eq_normForm, abs_eq (by norm_num : (0 : ℚ) ≤ 1)]
  constructor
  · rintro (h | h)
    · exact_mod_cast h
    · have hq : x ^ 2 + 6 * y ^ 2 = (-1 : ℤ) := by exact_mod_cast h
      have hnonneg : (0 : ℤ) ≤ x ^ 2 + 6 * y ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg y]
      omega
  · intro h
    left
    exact_mod_cast h

theorem intNorm_nonneg (z : 𝓞 K) : 0 ≤ Algebra.norm ℤ z := by
  obtain ⟨x, y, hz⟩ := exists_eq_smul_one_add_smul_theta z
  rw [hz, intNorm_eq_normForm]
  nlinarith [sq_nonneg x, sq_nonneg y]

theorem isUnit_iff_intNorm_eq_one (z : 𝓞 K) :
    IsUnit z ↔ Algebra.norm ℤ z = 1 := by
  obtain ⟨x, y, hz⟩ := exists_eq_smul_one_add_smul_theta z
  rw [hz, isUnit_iff_normForm, intNorm_eq_normForm]

theorem intNorm_ne_two (z : 𝓞 K) : Algebra.norm ℤ z ≠ 2 := by
  intro hz2
  obtain ⟨x, y, hz⟩ := exists_eq_smul_one_add_smul_theta z
  rw [hz, intNorm_eq_normForm] at hz2
  exact normForm_ne_two x y hz2

theorem intNorm_ne_three (z : 𝓞 K) : Algebra.norm ℤ z ≠ 3 := by
  intro hz3
  obtain ⟨x, y, hz⟩ := exists_eq_smul_one_add_smul_theta z
  rw [hz, intNorm_eq_normForm] at hz3
  exact normForm_ne_three x y hz3

theorem intNorm_ne_five (z : 𝓞 K) : Algebra.norm ℤ z ≠ 5 := by
  intro hz5
  obtain ⟨x, y, hz⟩ := exists_eq_smul_one_add_smul_theta z
  rw [hz, intNorm_eq_normForm] at hz5
  exact normForm_ne_five x y hz5


end NumberField.SqrtNegSix
