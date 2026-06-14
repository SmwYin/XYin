/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.RingOfIntegers

/-!
# `ℚ(√5)` Norm form

This file develops the norm form part of the `ℚ(√5)` number field example.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtFive

/-- `φ` as an element of the abstract ring of integers `𝓞 K`. -/
noncomputable def goldenIntO : 𝓞 K := ⟨goldenRoot, goldenRoot_isIntegral⟩

/-- The norm form of `ℚ(√5)` in the basis `1, φ`: the field norm of `x + yφ` is the binary
quadratic form `x² + xy - y²`. -/
theorem norm_eq_normForm (x y : ℚ) :
    Algebra.norm ℚ (x • (1 : K) + y • goldenRoot) = x ^ 2 + x * y - y ^ 2 := by
  rw [golden_norm_eq]
  norm_num [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]

/-- The integral norm form: on `𝓞 K = ℤ[φ]` the norm of `x + yφ` (with `x, y ∈ ℤ`) is
`x² + xy - y²`, the principal form of discriminant `5`. -/
theorem intNorm_eq_normForm (x y : ℤ) :
    Algebra.norm ℤ (x • (1 : 𝓞 K) + y • goldenIntO) = x ^ 2 + x * y - y ^ 2 := by
  have h1 : ((Algebra.norm ℤ (x • (1 : 𝓞 K) + y • goldenIntO) : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap (𝓞 K) K
        (x • (1 : 𝓞 K) + y • goldenIntO)) :=
    Algebra.coe_norm_int _
  have h2 : algebraMap (𝓞 K) K
      (x • (1 : 𝓞 K) + y • goldenIntO) =
      (x : ℚ) • (1 : K) + (y : ℚ) • goldenRoot := by
    simp [goldenIntO, Int.cast_smul_eq_zsmul]
  rw [h2, norm_eq_normForm] at h1
  norm_num at h1 ⊢
  exact_mod_cast h1

/-- The Pell-type unit equation for `ℚ(√5)`: `x + yφ` is a unit of `ℤ[φ]` iff
`x² + xy - y² = ±1`. Combined with `fundamentalUnit_generates`, all integer solutions arise
from `±φⁿ`, `n ∈ ℤ`; concretely `φⁿ = F(n-1) + F(n)·φ`, so the solutions are exactly the
pairs of consecutive Fibonacci numbers (up to sign). -/
theorem isUnit_iff_normForm (x y : ℤ) :
    IsUnit (x • (1 : 𝓞 K) + y • goldenIntO) ↔
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


end NumberField.SqrtFive
