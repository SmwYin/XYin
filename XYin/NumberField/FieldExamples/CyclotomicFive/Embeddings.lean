/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicFive.Galois

/-!
# `ℚ(ζ₅)` Embeddings

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

namespace NumberField.CyclotomicFive

theorem isTotallyComplex : NumberField.IsTotallyComplex K :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 5) K (by norm_num)

theorem nrRealPlaces_eq_zero : NumberField.InfinitePlace.nrRealPlaces K = 0 :=
  IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 5) K (by norm_num)

theorem nrComplexPlaces_eq_two : NumberField.InfinitePlace.nrComplexPlaces K = 2 := by
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [nrRealPlaces_eq_zero, degree_eq_four] at h
  omega
end NumberField.CyclotomicFive


/-!
## Embeddings
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

theorem infinitePlace_card_eq_two :
    Fintype.card (NumberField.InfinitePlace K) = 2 := by
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_eq_zero,
    nrComplexPlaces_eq_two]

theorem infinitePlace_isComplex (v : NumberField.InfinitePlace K) :
    NumberField.InfinitePlace.IsComplex v := by
  exact isTotallyComplex.isComplex v

theorem exists_complexEmbedding_zeta :
    ∃ σ : K →+* ℂ, σ ζ = Complex.exp (2 * Real.pi * Complex.I / 5) := by
  let ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)
  have hξprim : IsPrimitiveRoot ξ 5 := by
    simpa [ξ] using Complex.isPrimitiveRoot_exp 5 (by norm_num)
  have hξroot : zetaFivePolynomial.eval₂ (Algebra.ofId ℚ ℂ) ξ = 0 := by
    rw [zetaFivePolynomial]
    simp
    have hsum := hξprim.geom_sum_eq_zero (by norm_num)
    simp [Finset.sum_range_succ] at hsum
    linear_combination hsum
  refine ⟨((AdjoinRoot.liftAlgHom zetaFivePolynomial (Algebra.ofId ℚ ℂ) ξ hξroot).comp
    adjoinRootEquivCyclotomic.symm.toAlgHom).toRingHom, ?_⟩
  change (AdjoinRoot.liftAlgHom zetaFivePolynomial (Algebra.ofId ℚ ℂ) ξ hξroot)
    (adjoinRootEquivCyclotomic.symm ζ) = ξ
  rw [← adjoinRootEquivCyclotomic_root]
  simp

end NumberField.CyclotomicFive
