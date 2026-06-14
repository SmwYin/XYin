/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.Units
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Embeddings and infinite places of `ℚ(∛3)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

theorem infinitePlace_card_eq_two :
    Fintype.card (NumberField.InfinitePlace K) = 2 := by
  sorry

theorem infinitePlace_signature :
    NumberField.InfinitePlace.nrRealPlaces K = 1 ∧
      NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
  sorry

theorem exists_realEmbedding_cubeRootThree :
    ∃ σ : K →ₐ[ℚ] ℝ, σ cubeRootThree = (3 : ℝ) ^ ((1 : ℝ) / 3) := by
  sorry

theorem exists_complexEmbedding_cubeRootThree :
    ∃ σ : K →+* ℂ, σ cubeRootThree ^ 3 = 3 := by
  sorry

end NumberField.CubeRootThree
