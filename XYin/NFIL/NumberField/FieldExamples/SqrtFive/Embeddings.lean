/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NFIL.NumberField.FieldExamples.SqrtFive.Galois

/-!
# `ℚ(√5)` Embeddings

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

namespace NumberField.SqrtFive

private theorem ringHom_ext_golden {f g : K →+* ℂ} (h : f goldenRoot = g goldenRoot) :
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

theorem isTotallyReal : NumberField.IsTotallyReal K := by
  refine ⟨fun v => ?_⟩
  rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
  refine ringHom_ext_golden ?_
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  set z := NumberField.InfinitePlace.embedding v goldenRoot with hz
  have hsq : z ^ 2 = z + 1 := by
    rw [hz, ← map_pow, goldenRoot_sq, map_add, map_one]
  have hc : (starRingEnd ℂ) z ^ 2 = (starRingEnd ℂ) z + 1 := by
    rw [← map_pow, hsq, map_add, map_one]
  have hfac : ((starRingEnd ℂ) z - z) * ((starRingEnd ℂ) z + z - 1) = 0 := by
    linear_combination hc - hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hre : z.re = 1 / 2 := by
      have hcr := congrArg Complex.re h
      rw [Complex.sub_re, Complex.add_re, Complex.conj_re] at hcr
      norm_num at hcr
      linarith
    have hreal := congrArg Complex.re hsq
    rw [sq, Complex.mul_re, Complex.add_re, Complex.one_re, hre] at hreal
    norm_num at hreal
    nlinarith [sq_nonneg z.im]

theorem nrRealPlaces_eq_two : InfinitePlace.nrRealPlaces K = 2 := by
  haveI := isTotallyReal
  have hcomplex := NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [hcomplex, degree_eq_two] at h
  omega

theorem nrComplexPlaces_eq_zero : InfinitePlace.nrComplexPlaces K = 0 := by
  haveI := isTotallyReal
  exact NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K
end NumberField.SqrtFive


/-!
## Embeddings
-/

noncomputable section


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
