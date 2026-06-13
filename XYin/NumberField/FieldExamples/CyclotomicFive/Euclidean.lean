/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicFive.ClassGroup

/-!
# `ℚ(ζ₅)` Euclidean structure

This file develops the Euclidean structure part of the `ℚ(ζ₅)` number field example.
-/

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicFive

/-- `ℤ[ζ₅]` is norm-Euclidean with respect to the absolute value of the field norm. -/
theorem normEuclidean (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry

end NumberField.CyclotomicFive
