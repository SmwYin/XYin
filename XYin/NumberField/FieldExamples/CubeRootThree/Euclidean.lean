/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.ClassGroup

/-!
# `ℚ(∛3)` Euclidean structure

This file develops the Euclidean structure part of the `ℚ(∛3)` number field example.
-/

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CubeRootThree

/-- `ℚ(∛3)` is norm-Euclidean: division with remainder in `ℤ[θ]` with respect to the absolute
value of the field norm. This is a classical result for the pure cubic field of smallest
discriminant, and strengthens `isPrincipalIdealRing`. -/
theorem normEuclidean (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry


end NumberField.CubeRootThree
