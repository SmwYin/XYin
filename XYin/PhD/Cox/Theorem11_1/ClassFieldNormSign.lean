/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Norm.Basic

noncomputable section
open NumberField
open scoped ComplexConjugate
/-! Interfaces for Janusz III.3.3 and V.5.1.1–5.1.2. The actual readiness proofs are retained
separately.
-/

namespace Cox.ClassFieldTheory

open Classical in
/-- The embeddings inducing a fixed infinite place form its conjugate pair. -/
theorem infinitePlace_embeddings_eq_pair (K : Type*) [Field K] [Fintype (K →+* ℂ)]
    (w : InfinitePlace K) :
    ({φ : K →+* ℂ | InfinitePlace.mk φ = w} : Finset _) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  have hcc : ∀ ψ : K →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate ψ) = ψ :=
    fun ψ => RingHom.ext fun y => by
      simp only [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  conv_lhs => rw [← InfinitePlace.mk_embedding w]
  rw [InfinitePlace.mk_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [← h, hcc]
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h, hcc]

/-- The rational norm in a totally complex field is a product of squared complex norms. -/
theorem norm_eq_prod_normSq_of_isTotallyComplex
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (x : K) :
    (Algebra.norm ℚ x : ℂ) =
      ((∏ w : InfinitePlace K, Complex.normSq (w.embedding x) : ℝ) : ℂ) := by
  classical
  rw [show (Algebra.norm ℚ x : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ x) from rfl,
    Algebra.norm_eq_prod_embeddings ℚ ℂ x,
    ← Fintype.prod_equiv RingHom.equivRatAlgHom (fun φ : K →+* ℂ => φ x) _ (fun φ => rfl),
    ← Finset.prod_fiberwise Finset.univ (fun φ : K →+* ℂ => InfinitePlace.mk φ) (fun φ => φ x)]
  push_cast
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    (InfinitePlace.isComplex_iff.mp (IsTotallyComplex.isComplex w))
      (ComplexEmbedding.isReal_iff.mpr h.symm)
  have hpair := infinitePlace_embeddings_eq_pair K w
  rw [show (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} by
    rw [← hpair], Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq,
    Complex.mul_conj]

/-- The rational norm in a totally complex number field is nonnegative. -/
theorem norm_nonneg_of_isTotallyComplex
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] (x : K) :
    0 ≤ Algebra.norm ℚ x := by
  have h := congrArg Complex.re (norm_eq_prod_normSq_of_isTotallyComplex K x)
  rw [Complex.ratCast_re, Complex.ofReal_re] at h
  have hnn : (0 : ℝ) ≤ (Algebra.norm ℚ x : ℝ) := by
    rw [h]
    exact Finset.prod_nonneg fun w _ => Complex.normSq_nonneg _
  exact_mod_cast hnn

end Cox.ClassFieldTheory
