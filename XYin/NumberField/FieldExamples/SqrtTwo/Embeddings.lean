/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.Galois
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Embeddings and infinite places of `ℚ(√2)`

This file records the explicit archimedean picture of the `ℚ(√2)` example.
It is deliberately separate from `Galois.lean`: the Galois file is the source
of truth for automorphisms, while this file packages the two real embeddings
and the corresponding infinite places.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtTwo

/-- The positive real embedding sends `√2` to the positive square root in `ℝ`. -/
theorem exists_realEmbedding_pos :
    ∃ σ : K →ₐ[ℚ] ℝ, σ sqrtTwoRoot = Real.sqrt 2 := by
  refine ⟨(QuadraticAlgebra.lift (R := ℚ) (a := (2 : ℚ)) (b := 0)) ⟨Real.sqrt 2, ?_⟩, ?_⟩
  · rw [Real.mul_self_sqrt]
    · norm_num
    · norm_num
  · simp [sqrtTwoRoot]

/-- The negative real embedding sends `√2` to the negative square root in `ℝ`. -/
theorem exists_realEmbedding_neg :
    ∃ σ : K →ₐ[ℚ] ℝ, σ sqrtTwoRoot = -Real.sqrt 2 := by
  refine ⟨(QuadraticAlgebra.lift (R := ℚ) (a := (2 : ℚ)) (b := 0)) ⟨-Real.sqrt 2, ?_⟩, ?_⟩
  · rw [neg_mul_neg, Real.mul_self_sqrt]
    · norm_num
    · norm_num
  · simp [sqrtTwoRoot]

/-- Every real embedding of `ℚ(√2)` is one of the two expected embeddings. -/
theorem realEmbedding_root_eq_pos_or_neg (σ : K →ₐ[ℚ] ℝ) :
    σ sqrtTwoRoot = Real.sqrt 2 ∨ σ sqrtTwoRoot = -Real.sqrt 2 := by
  have hsq : (σ sqrtTwoRoot) ^ 2 = (Real.sqrt 2) ^ 2 := by
    rw [← map_pow, sqrtTwoRoot_sq]
    change σ (algebraMap ℚ K (2 : ℚ)) = (Real.sqrt 2) ^ 2
    rw [σ.commutes (2 : ℚ), Real.sq_sqrt]
    · norm_num
    · norm_num
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq

/-- The infinite places of `ℚ(√2)` are the two real places. -/
theorem infinitePlace_card_eq_two :
    Fintype.card (NumberField.InfinitePlace K) = 2 := by
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrRealPlaces_eq_two, nrComplexPlaces_eq_zero]

/-- Every infinite place of `ℚ(√2)` is real. -/
theorem infinitePlace_isReal (v : NumberField.InfinitePlace K) :
    NumberField.InfinitePlace.IsReal v := by
  haveI : NumberField.IsTotallyReal K := isTotallyReal
  exact NumberField.IsTotallyReal.isReal v

/-- Both infinite absolute values take `√2` to the usual positive value `√2`. -/
theorem infinitePlace_apply_sqrtTwoRoot (v : NumberField.InfinitePlace K) :
    v sqrtTwoRoot = Real.sqrt 2 := by
  rw [← NumberField.InfinitePlace.norm_embedding_eq v sqrtTwoRoot]
  have hsq :
      (NumberField.InfinitePlace.embedding v sqrtTwoRoot) ^ 2 =
        ((Real.sqrt 2 : ℂ) ^ 2) := by
    rw [← map_pow, sqrtTwoRoot_sq]
    change (NumberField.InfinitePlace.embedding v).comp (algebraMap ℚ K) (2 : ℚ) =
      ((Real.sqrt 2 : ℂ) ^ 2)
    calc
      (NumberField.InfinitePlace.embedding v).comp (algebraMap ℚ K) (2 : ℚ) = (2 : ℂ) := by
        exact map_ratCast ((NumberField.InfinitePlace.embedding v).comp (algebraMap ℚ K)) (2 : ℚ)
      _ = ((Real.sqrt 2 : ℂ) ^ 2) := by
        rw [pow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt]
        · norm_num
        · norm_num
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · rw [h]
    simp [Real.sqrt_nonneg]
  · rw [h]
    simp [Real.sqrt_nonneg]

end NumberField.SqrtTwo
