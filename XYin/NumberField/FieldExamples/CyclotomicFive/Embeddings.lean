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
  sorry

theorem infinitePlace_isComplex (v : NumberField.InfinitePlace K) :
    NumberField.InfinitePlace.IsComplex v := by
  sorry

theorem exists_complexEmbedding_zeta :
    ∃ σ : K →+* ℂ, σ ζ = Complex.exp (2 * Real.pi * Complex.I / 5) := by
  sorry

end NumberField.CyclotomicFive
