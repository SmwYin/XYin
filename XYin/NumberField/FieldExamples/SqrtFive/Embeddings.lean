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
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_eq_two,
    nrComplexPlaces_eq_zero]

theorem infinitePlace_isReal (v : NumberField.InfinitePlace K) :
    NumberField.InfinitePlace.IsReal v := by
  exact isTotallyReal.isReal v

theorem exists_realEmbedding_goldenRatio :
    ∃ σ : K →ₐ[ℚ] ℝ, σ goldenRoot = (1 + Real.sqrt 5) / 2 := by
  refine ⟨QuadraticAlgebra.lift ⟨(1 + Real.sqrt 5) / 2, by
    have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
    rw [show ((1 + Real.sqrt 5) / 2) * ((1 + Real.sqrt 5) / 2) =
        (3 + Real.sqrt 5) / 2 by nlinarith]
    simp
    ring⟩, ?_⟩
  simp [goldenRoot]

theorem exists_realEmbedding_conjugateGoldenRatio :
    ∃ σ : K →ₐ[ℚ] ℝ, σ goldenRoot = (1 - Real.sqrt 5) / 2 := by
  refine ⟨QuadraticAlgebra.lift ⟨(1 - Real.sqrt 5) / 2, by
    have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
    rw [show ((1 - Real.sqrt 5) / 2) * ((1 - Real.sqrt 5) / 2) =
        (3 - Real.sqrt 5) / 2 by nlinarith]
    simp
    ring⟩, ?_⟩
  simp [goldenRoot]

end NumberField.SqrtFive
