/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.Embeddings
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Infinite completions of `ℚ(√2)`

This file records the archimedean completion viewpoint for the `ℚ(√2)` example.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open NumberField

namespace NumberField.SqrtTwo

/-- The completion of `ℚ(√2)` at an infinite place. -/
abbrev InfiniteCompletion (v : NumberField.InfinitePlace K) : Type :=
  v.Completion

/-- Every infinite completion of `ℚ(√2)` is a real completion. -/
theorem infiniteCompletion_equiv_real (v : NumberField.InfinitePlace K) :
    Nonempty (InfiniteCompletion v ≃+* ℝ) := by
  sorry

/-- The real isomorphism sends the image of `√2` to the expected real absolute value. -/
theorem infiniteCompletion_sqrtTwoRoot_norm (v : NumberField.InfinitePlace K) :
    ‖(algebraMap K (InfiniteCompletion v) sqrtTwoRoot)‖ = Real.sqrt 2 := by
  sorry

end NumberField.SqrtTwo
