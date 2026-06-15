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
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_eq_zero,
    nrComplexPlaces_eq_one]

theorem infinitePlace_isComplex (v : NumberField.InfinitePlace K) :
    NumberField.InfinitePlace.IsComplex v := by
  exact isTotallyComplex.isComplex v

theorem exists_complexEmbedding_theta_pos :
    ∃ σ : K →+* ℂ, σ θ = Complex.I * (Real.sqrt 6 : ℂ) := by
  refine ⟨(QuadraticAlgebra.lift (R := ℚ) (a := (-6 : ℚ)) (b := 0)
      ⟨Complex.I * (Real.sqrt 6 : ℂ), ?_⟩).toRingHom, ?_⟩
  · ring_nf
    rw [pow_two, Complex.I_mul_I]
    rw [← Complex.ofReal_pow, Real.sq_sqrt]
    · norm_num
    · norm_num
  · simp [θ]

theorem exists_complexEmbedding_theta_neg :
    ∃ σ : K →+* ℂ, σ θ = -Complex.I * (Real.sqrt 6 : ℂ) := by
  refine ⟨(QuadraticAlgebra.lift (R := ℚ) (a := (-6 : ℚ)) (b := 0)
      ⟨-Complex.I * (Real.sqrt 6 : ℂ), ?_⟩).toRingHom, ?_⟩
  · ring_nf
    rw [pow_two, Complex.I_mul_I]
    rw [← Complex.ofReal_pow, Real.sq_sqrt]
    · norm_num
    · norm_num
  · simp [θ]

end NumberField.SqrtNegSix
