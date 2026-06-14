/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicThree.Embeddings
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Infinite completions of `ℚ(ζ₃)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicThree

abbrev InfiniteCompletion (v : NumberField.InfinitePlace K) : Type :=
  v.Completion

theorem infiniteCompletion_equiv_complex (v : NumberField.InfinitePlace K) :
    Nonempty (InfiniteCompletion v ≃+* ℂ) := by
  sorry

theorem infiniteCompletion_zeta_norm (v : NumberField.InfinitePlace K) :
    ‖(algebraMap K (InfiniteCompletion v) ζ)‖ = 1 := by
  sorry

end NumberField.CyclotomicThree
