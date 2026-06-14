/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.Units
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Embeddings and infinite places of `ℚ(√-6)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

theorem infinitePlace_card_eq_one :
    Fintype.card (NumberField.InfinitePlace K) = 1 := by
  sorry

theorem infinitePlace_isComplex (v : NumberField.InfinitePlace K) :
    NumberField.InfinitePlace.IsComplex v := by
  sorry

theorem exists_complexEmbedding_theta_pos :
    ∃ σ : K →+* ℂ, σ θ = Complex.I * (Real.sqrt 6 : ℂ) := by
  sorry

theorem exists_complexEmbedding_theta_neg :
    ∃ σ : K →+* ℂ, σ θ = -Complex.I * (Real.sqrt 6 : ℂ) := by
  sorry

end NumberField.SqrtNegSix
