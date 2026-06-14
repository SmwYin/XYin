/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.Embeddings
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Infinite completions of `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

abbrev InfiniteCompletion (v : NumberField.InfinitePlace K) : Type :=
  v.Completion

theorem infiniteCompletion_equiv_real (v : NumberField.InfinitePlace K) :
    Nonempty (InfiniteCompletion v ≃+* ℝ) := by
  sorry

theorem infiniteCompletion_goldenRoot_norm (v : NumberField.InfinitePlace K) :
    ∃ r : ℝ, ‖(algebraMap K (InfiniteCompletion v) goldenRoot)‖ = r := by
  sorry

end NumberField.SqrtFive
