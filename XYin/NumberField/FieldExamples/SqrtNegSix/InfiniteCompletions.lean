/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.Embeddings
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Infinite completions of `ℚ(√-6)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

abbrev InfiniteCompletion (v : NumberField.InfinitePlace K) : Type :=
  v.Completion

theorem infiniteCompletion_equiv_complex (v : NumberField.InfinitePlace K) :
    Nonempty (InfiniteCompletion v ≃+* ℂ) := by
  exact ⟨NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (infinitePlace_isComplex v)⟩

theorem infiniteCompletion_theta_norm (v : NumberField.InfinitePlace K) :
    ∃ r : ℝ, ‖(algebraMap K (InfiniteCompletion v) θ)‖ = r := by
  exact ⟨‖(algebraMap K (InfiniteCompletion v) θ)‖, rfl⟩

end NumberField.SqrtNegSix
