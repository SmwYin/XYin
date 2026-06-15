/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.Euclidean

/-!
# `ℚ(√5)` Local-global

Finite and infinite places, completions, product formula, canonical embedding geometry, house,
adeles, and zeta statements.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Finite Places
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open IsDedekindDomain

namespace NumberField.SqrtFive

/-- The finite place over `5`, represented by the ramified prime `(√5)`. -/
def heightOneFive : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {sqrtFiveIntO}
  isPrime := by
    exact isPrime_span_sqrtFiveIntO
  ne_bot := by
    intro hbot
    have hzero : sqrtFiveIntO = 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hbot
    have hsqrt : sqrtFiveIntO ^ 2 = (5 : 𝓞 K) := by
      apply Subtype.ext
      change (2 * goldenRoot - 1) ^ 2 = (5 : K)
      exact sqrtFiveRoot_sq
    rw [hzero] at hsqrt
    norm_num at hsqrt

/-- The finite absolute value associated to the ramified place over `5`. -/
abbrev vFive : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk heightOneFive

theorem vFive_ramificationIdx :
    (Ideal.span {(5 : ℤ)}).ramificationIdx heightOneFive.asIdeal = 2 := by
  exact ramificationIdx_span_sqrtFiveIntO

theorem vFive_inertiaDeg :
    (Ideal.span {(5 : ℤ)}).inertiaDeg heightOneFive.asIdeal = 1 := by
  exact inertiaDeg_span_sqrtFiveIntO

end NumberField.SqrtFive


/-!
## Completions
-/

noncomputable section


open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

/-- The completion of `ℚ(√5)` at the ramified finite place over `5`. -/
abbrev CompletionAtFive : Type :=
  heightOneFive.adicCompletion K

theorem completionAtFive_contains_goldenRoot :
    ∃ x : CompletionAtFive,
      x = NumberField.FinitePlace.embedding (K := K) heightOneFive goldenRoot := by
  exact ⟨NumberField.FinitePlace.embedding (K := K) heightOneFive goldenRoot, rfl⟩

end NumberField.SqrtFive


/-!
## Infinite Completions
-/

noncomputable section


open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

abbrev InfiniteCompletion (v : NumberField.InfinitePlace K) : Type :=
  v.Completion

theorem infiniteCompletion_equiv_real (v : NumberField.InfinitePlace K) :
    Nonempty (InfiniteCompletion v ≃+* ℝ) := by
  exact ⟨NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (infinitePlace_isReal v)⟩

theorem infiniteCompletion_goldenRoot_norm (v : NumberField.InfinitePlace K) :
    ∃ r : ℝ, ‖(algebraMap K (InfiniteCompletion v) goldenRoot)‖ = r := by
  exact ⟨‖(algebraMap K (InfiniteCompletion v) goldenRoot)‖, rfl⟩

end NumberField.SqrtFive


/-!
## Product Formula
-/

noncomputable section


open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

theorem product_formula_goldenRoot :
    ((∏ w : NumberField.InfinitePlace K, w goldenRoot ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K, v goldenRoot) = 1 := by
  exact NumberField.prod_abs_eq_one (K := K) (x := goldenRoot) (by
    intro h
    have hsq := goldenRoot_sq
    rw [h] at hsq
    norm_num at hsq)

theorem product_formula_fundamentalUnit :
    ((∏ w : NumberField.InfinitePlace K,
          w (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K,
          v (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))) = 1 := by
  exact NumberField.prod_abs_eq_one (K := K)
    (x := algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) (by
      intro h
      exact Units.ne_zero fundamentalUnit (RingOfIntegers.coe_injective h))

end NumberField.SqrtFive


/-!
## Infinite Adele Ring
-/

noncomputable section


open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

abbrev SqrtFiveInfiniteAdeleRing : Type :=
  NumberField.InfiniteAdeleRing K

abbrev infinitePrincipalAdele_goldenRoot : SqrtFiveInfiniteAdeleRing :=
  algebraMap K SqrtFiveInfiniteAdeleRing goldenRoot

abbrev infinitePrincipalAdele_fundamentalUnit : SqrtFiveInfiniteAdeleRing :=
  algebraMap K SqrtFiveInfiniteAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

theorem infiniteAdele_norm_goldenRoot :
    ‖infinitePrincipalAdele_goldenRoot‖ = |Algebra.norm ℚ goldenRoot| := by
  exact NumberField.InfiniteAdeleRing.coe_norm_eq_abs_norm goldenRoot

theorem infiniteAdele_denseRange :
    DenseRange (algebraMap K SqrtFiveInfiniteAdeleRing) := by
  exact NumberField.InfiniteAdeleRing.denseRange_algebraMap K

end NumberField.SqrtFive


/-!
## Canonical Embedding
-/

noncomputable section


open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

theorem canonicalEmbedding_apply_goldenRoot (σ : K →+* ℂ) :
    NumberField.canonicalEmbedding K goldenRoot σ = σ goldenRoot := by
  rfl

theorem canonicalEmbedding_goldenIntO_mem_integerLattice :
    NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K goldenIntO) ∈
      NumberField.canonicalEmbedding.integerLattice K := by
  simp [NumberField.canonicalEmbedding.integerLattice]

theorem canonicalEmbedding_fundamentalUnit_coordinates :
    ∃ x : (K →+* ℂ) → ℂ,
      x = NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) := by
  exact ⟨NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)),
    rfl⟩

end NumberField.SqrtFive

/-!
## Canonical Embedding Geometry
-/

noncomputable section


open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open MeasureTheory

namespace NumberField.SqrtFive

abbrev mixedEmbedding_goldenRoot : NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.mixedEmbedding K goldenRoot

theorem mixedEmbedding_goldenRoot_mem_convexBodyLT
    (f : NumberField.InfinitePlace K → NNReal)
    (hf : ∀ w : NumberField.InfinitePlace K, w goldenRoot < f w) :
    mixedEmbedding_goldenRoot ∈ NumberField.mixedEmbedding.convexBodyLT K f := by
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ,
    NumberField.mixedEmbedding.mixedEmbedding_apply_isReal, Metric.mem_ball,
    dist_zero_right, Real.norm_eq_abs, forall_const, Subtype.forall,
    NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
  constructor
  · intro a ha
    simpa [← NumberField.InfinitePlace.norm_embedding_of_isReal ha goldenRoot] using hf a
  · intro a ha
    have hreal := infinitePlace_isReal a
    have hnot : ¬ NumberField.InfinitePlace.IsReal a :=
      NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr ha
    exact False.elim (hnot hreal)

theorem measurableSet_fundamentalCone :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone K) := by
  exact NumberField.mixedEmbedding.measurableSet_fundamentalCone K

theorem measurableSet_normLeOne :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone.normLeOne K) := by
  exact NumberField.mixedEmbedding.fundamentalCone.measurableSet_normLeOne K

theorem polarSpace_nonempty :
    Nonempty (NumberField.mixedEmbedding.polarSpace K) := by
  infer_instance

end NumberField.SqrtFive


/-!
## House
-/

noncomputable section


open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

theorem house_goldenRoot_pos :
    0 < NumberField.house goldenRoot := by
  exact lt_of_lt_of_le zero_lt_one
    (NumberField.one_le_house_of_isIntegral goldenRoot_isIntegral (by
      intro h
      have hsq := goldenRoot_sq
      rw [h] at hsq
      norm_num at hsq))

theorem house_fundamentalUnit :
    NumberField.house (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) =
      (1 + Real.sqrt 5) / 2 := by
  sorry

end NumberField.SqrtFive


/-!
## Adele Ring
-/

noncomputable section


open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

/-- The adele ring of `ℚ(√5)`. -/
abbrev SqrtFiveAdeleRing : Type :=
  NumberField.AdeleRing (𝓞 K) K

abbrev principalAdele_goldenRoot : SqrtFiveAdeleRing :=
  algebraMap K SqrtFiveAdeleRing goldenRoot

abbrev principalAdele_fundamentalUnit : SqrtFiveAdeleRing :=
  algebraMap K SqrtFiveAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

theorem principalAdele_goldenRoot_ne_zero : principalAdele_goldenRoot ≠ 0 := by
  intro h
  have hroot : goldenRoot = 0 :=
    NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K) h
  have hsq := goldenRoot_sq
  rw [hroot] at hsq
  norm_num at hsq

theorem principalAdele_fundamentalUnit_is_unit_everywhere :
    ∀ v : NumberField.FinitePlace K,
      v (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) = 1 := by
  intro v
  rw [← NumberField.FinitePlace.norm_embedding_eq v
    (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))]
  rw [NumberField.FinitePlace.norm_eq_one_iff_notMem (K := K)
    (v := NumberField.FinitePlace.maximalIdeal v)]
  intro hmem
  have hmul : (fundamentalUnit : 𝓞 K) * ((fundamentalUnit⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
    exact fundamentalUnit.val_inv
  have h_mem_mul :
      (fundamentalUnit : 𝓞 K) * ((fundamentalUnit⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ∈
        (NumberField.FinitePlace.maximalIdeal v).asIdeal :=
    Ideal.mul_mem_right ((fundamentalUnit⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
      (NumberField.FinitePlace.maximalIdeal v).asIdeal hmem
  have h_one : (1 : 𝓞 K) ∈ (NumberField.FinitePlace.maximalIdeal v).asIdeal := by
    rwa [hmul] at h_mem_mul
  exact (NumberField.FinitePlace.maximalIdeal v).isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr h_one)

end NumberField.SqrtFive


/-!
## Dedekind Zeta
-/

noncomputable section


open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

abbrev sqrtFiveDedekindZeta (s : ℂ) : ℂ :=
  NumberField.dedekindZeta K s

abbrev sqrtFiveDedekindZetaResidue : ℝ :=
  NumberField.dedekindZeta_residue K

theorem dedekindZeta_residue_pos :
    0 < sqrtFiveDedekindZetaResidue := by
  exact NumberField.dedekindZeta_residue_pos K

theorem dedekindZeta_residue_class_number_formula :
    sqrtFiveDedekindZetaResidue =
      (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
          (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          NumberField.Units.regulator K * NumberField.classNumber K) /
        (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|) := by
  exact NumberField.dedekindZeta_residue_def K

end NumberField.SqrtFive
