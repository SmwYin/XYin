/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.Units
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Embeddings and infinite places of `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

theorem infinitePlace_card_eq_two :
    Fintype.card (NumberField.InfinitePlace K) = 2 := by
  sorry

theorem infinitePlace_isReal (v : NumberField.InfinitePlace K) :
    NumberField.InfinitePlace.IsReal v := by
  sorry

theorem exists_realEmbedding_goldenRatio :
    ∃ σ : K →ₐ[ℚ] ℝ, σ goldenRoot = (1 + Real.sqrt 5) / 2 := by
  sorry

theorem exists_realEmbedding_conjugateGoldenRatio :
    ∃ σ : K →ₐ[ℚ] ℝ, σ goldenRoot = (1 - Real.sqrt 5) / 2 := by
  sorry

end NumberField.SqrtFive
