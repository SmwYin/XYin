/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.Embeddings
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Infinite completions of `ℚ(∛3)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

abbrev InfiniteCompletion (v : NumberField.InfinitePlace K) : Type :=
  v.Completion

theorem infiniteCompletion_equiv_real_of_isReal
    (v : NumberField.InfinitePlace K) (hv : NumberField.InfinitePlace.IsReal v) :
    Nonempty (InfiniteCompletion v ≃+* ℝ) := by
  sorry

theorem infiniteCompletion_equiv_complex_of_isComplex
    (v : NumberField.InfinitePlace K) (hv : NumberField.InfinitePlace.IsComplex v) :
    Nonempty (InfiniteCompletion v ≃+* ℂ) := by
  sorry

end NumberField.CubeRootThree
