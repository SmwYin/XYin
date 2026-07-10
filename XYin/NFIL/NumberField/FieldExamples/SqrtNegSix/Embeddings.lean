/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NFIL.NumberField.FieldExamples.SqrtNegSix.Galois

/-!
# `ℚ(√-6)` Embeddings

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

namespace NumberField.SqrtNegSix

theorem isTotallyComplex : NumberField.IsTotallyComplex K := by
  refine ⟨fun v => ?_⟩
  rw [NumberField.InfinitePlace.isComplex_iff]
  intro hreal
  set z := NumberField.InfinitePlace.embedding v θ with hz
  have hsq : z ^ 2 = (-6 : ℂ) := by
    rw [hz, ← map_pow, theta_sq]
    rw [map_neg, map_ofNat]
  have hconj := RingHom.congr_fun (NumberField.ComplexEmbedding.isReal_iff.mp hreal) θ
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← hz] at hconj
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hconj
  have hre := congrArg Complex.re hsq
  rw [sq, Complex.mul_re, him] at hre
  norm_num at hre
  nlinarith [sq_nonneg z.re]

theorem nrRealPlaces_eq_zero : NumberField.InfinitePlace.nrRealPlaces K = 0 := by
  haveI := isTotallyComplex
  exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero K

theorem nrComplexPlaces_eq_one : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [nrRealPlaces_eq_zero, degree_eq_two] at h
  omega
end NumberField.SqrtNegSix


/-!
## Embeddings
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
