/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicThree.Galois

/-!
# `ℚ(ζ₃)` Embeddings

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

namespace NumberField.CyclotomicThree

theorem nrRealPlaces_eq_zero : InfinitePlace.nrRealPlaces K = 0 := by
  exact IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 3) K (by norm_num)

theorem isTotallyComplex : IsTotallyComplex K :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 3) K (by norm_num)

theorem nrComplexPlaces_eq_one : InfinitePlace.nrComplexPlaces K = 1 := by
  rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := 3) K]
  rw [Nat.totient_prime Nat.prime_three]
end NumberField.CyclotomicThree


/-!
## Embeddings
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicThree

theorem infinitePlace_card_eq_one :
    Fintype.card (NumberField.InfinitePlace K) = 1 := by
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_eq_zero,
    nrComplexPlaces_eq_one]

theorem infinitePlace_isComplex (v : NumberField.InfinitePlace K) :
    NumberField.InfinitePlace.IsComplex v := by
  exact isTotallyComplex.isComplex v

theorem exists_complexEmbedding_zeta :
    ∃ σ : K →+* ℂ, σ ζ = Complex.exp (2 * Real.pi * Complex.I / 3) := by
  let ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hξprim : IsPrimitiveRoot ξ 3 := by
    simpa [ξ] using Complex.isPrimitiveRoot_exp 3 (by norm_num)
  have hξroot : zetaThreePolynomial.eval₂ (Algebra.ofId ℚ ℂ) ξ = 0 := by
    rw [zetaThreePolynomial, ← cyclotomic_three ℚ]
    simpa [IsRoot, Polynomial.aeval_def] using hξprim.isRoot_cyclotomic (by norm_num : 0 < 3)
  refine ⟨((AdjoinRoot.liftAlgHom zetaThreePolynomial (Algebra.ofId ℚ ℂ) ξ hξroot).comp
    adjoinRootEquivCyclotomic.symm.toAlgHom).toRingHom, ?_⟩
  change (AdjoinRoot.liftAlgHom zetaThreePolynomial (Algebra.ofId ℚ ℂ) ξ hξroot)
    (adjoinRootEquivCyclotomic.symm ζ) = ξ
  rw [← adjoinRootEquivCyclotomic_root]
  simp

end NumberField.CyclotomicThree
