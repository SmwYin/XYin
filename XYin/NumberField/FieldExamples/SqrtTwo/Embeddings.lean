/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.Galois

/-!
# `ℚ(√2)` Embeddings

Real and complex embeddings, signature, infinite places, and lightweight canonical embedding facts.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Signature and archimedean type
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtTwo

private theorem ringHom_ext_sqrtTwo {f g : K →+* ℂ} (h : f sqrtTwoRoot = g sqrtTwoRoot) :
    f = g := by
  ext z
  obtain ⟨x, y⟩ := z
  rw [QuadraticAlgebra.mk_eq_add_smul_omega, map_add, map_add]
  congr 1
  · exact (eq_ratCast (f.comp (algebraMap ℚ K)) x).trans
      (eq_ratCast (g.comp (algebraMap ℚ K)) x).symm
  · rw [Algebra.smul_def, map_mul, map_mul]
    exact congrArg₂ (fun a b => a * b)
      ((eq_ratCast (f.comp (algebraMap ℚ K)) y).trans
        (eq_ratCast (g.comp (algebraMap ℚ K)) y).symm) h

/-- `ℚ(√2)` is totally real. -/
theorem isTotallyReal : NumberField.IsTotallyReal K := by
  refine ⟨fun v => ?_⟩
  rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
  refine ringHom_ext_sqrtTwo ?_
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  set z := NumberField.InfinitePlace.embedding v sqrtTwoRoot with hz
  have hsq : z ^ 2 = 2 := by
    rw [hz, ← map_pow, sqrtTwoRoot_sq]
    change (NumberField.InfinitePlace.embedding v).comp (algebraMap ℚ K) (2 : ℚ) = (2 : ℂ)
    exact map_ratCast ((NumberField.InfinitePlace.embedding v).comp (algebraMap ℚ K)) 2
  have hc : (starRingEnd ℂ) z ^ 2 = 2 := by
    rw [← map_pow, hsq]
    exact map_ofNat (starRingEnd ℂ) 2
  have hfac : ((starRingEnd ℂ) z - z) * ((starRingEnd ℂ) z + z) = 0 := by
    linear_combination hc - hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hre : z.re = 0 := by
      have hcr := congrArg Complex.re h
      simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at hcr
      linarith
    have hreal := congrArg Complex.re hsq
    simp only [sq, Complex.mul_re, hre, zero_mul] at hreal
    norm_num at hreal
    nlinarith [sq_nonneg z.im]

/-- The field `ℚ(√2)` has no complex infinite places. -/
theorem nrComplexPlaces_eq_zero :
    NumberField.InfinitePlace.nrComplexPlaces K = 0 := by
  haveI := isTotallyReal
  exact NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K

/-- The field `ℚ(√2)` has two real infinite places: the signature is `(r₁, r₂) = (2, 0)`,
i.e. the field is totally real. -/
theorem nrRealPlaces_eq_two :
    NumberField.InfinitePlace.nrRealPlaces K = 2 := by
  have hfin : Module.finrank ℚ K = 2 := by
    rw [PowerBasis.finrank sqrtTwoPowerBasis]
    exact sqrtTwoPowerBasis_dim
  have hsig := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  rw [hfin, nrComplexPlaces_eq_zero] at hsig
  omega
end NumberField.SqrtTwo


/-!
## Embeddings
-/

noncomputable section


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
