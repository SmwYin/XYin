/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.Euclidean

/-!
# `ℚ(√-6)` Local-global

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

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open IsDedekindDomain

namespace NumberField.SqrtNegSix

/-- The finite place over `2`, represented by the non-principal ramified prime. -/
def heightOneTwo : HeightOneSpectrum (𝓞 K) where
  asIdeal := primeAboveTwo
  isPrime := by
    exact isPrime_primeAboveTwo
  ne_bot := by
    intro h
    have hnorm := absNorm_primeAboveTwo
    rw [h] at hnorm
    norm_num at hnorm

/-- The finite place over `3`, represented by the non-principal ramified prime. -/
def heightOneThree : HeightOneSpectrum (𝓞 K) where
  asIdeal := primeAboveThree
  isPrime := by
    exact isPrime_primeAboveThree
  ne_bot := by
    intro h
    have hnorm := absNorm_primeAboveThree
    rw [h] at hnorm
    norm_num at hnorm

abbrev vTwo : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk heightOneTwo

abbrev vThree : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk heightOneThree

theorem vTwo_ramificationIdx :
    (Ideal.span {(2 : ℤ)}).ramificationIdx heightOneTwo.asIdeal = 2 := by
  exact ramificationIdx_primeAboveTwo

theorem vThree_ramificationIdx :
    (Ideal.span {(3 : ℤ)}).ramificationIdx heightOneThree.asIdeal = 2 := by
  exact ramificationIdx_primeAboveThree

theorem vTwo_inertiaDeg :
    (Ideal.span {(2 : ℤ)}).inertiaDeg heightOneTwo.asIdeal = 1 := by
  exact inertiaDeg_primeAboveTwo

theorem vThree_inertiaDeg :
    (Ideal.span {(3 : ℤ)}).inertiaDeg heightOneThree.asIdeal = 1 := by
  exact inertiaDeg_primeAboveThree

end NumberField.SqrtNegSix


/-!
## Completions
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

abbrev CompletionAtTwo : Type :=
  heightOneTwo.adicCompletion K

abbrev CompletionAtThree : Type :=
  heightOneThree.adicCompletion K

theorem completionAtTwo_contains_theta :
    ∃ x : CompletionAtTwo,
      x = NumberField.FinitePlace.embedding (K := K) heightOneTwo θ := by
  exact ⟨NumberField.FinitePlace.embedding (K := K) heightOneTwo θ, rfl⟩

theorem completionAtThree_contains_theta :
    ∃ x : CompletionAtThree,
      x = NumberField.FinitePlace.embedding (K := K) heightOneThree θ := by
  exact ⟨NumberField.FinitePlace.embedding (K := K) heightOneThree θ, rfl⟩

end NumberField.SqrtNegSix


/-!
## Infinite Completions
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

abbrev InfiniteCompletion (v : NumberField.InfinitePlace K) : Type :=
  v.Completion

theorem infiniteCompletion_equiv_complex (v : NumberField.InfinitePlace K) :
    Nonempty (InfiniteCompletion v ≃+* ℂ) := by
  exact ⟨NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (infinitePlace_isComplex v)⟩

theorem infiniteCompletion_theta_norm (v : NumberField.InfinitePlace K) :
    ∃ r : ℝ, ‖(algebraMap K (InfiniteCompletion v) θ)‖ = r := by
  exact ⟨‖(algebraMap K (InfiniteCompletion v) θ)‖, rfl⟩

end NumberField.SqrtNegSix


/-!
## Product Formula
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

theorem product_formula_theta :
    ((∏ w : NumberField.InfinitePlace K, w θ ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K, v θ) = 1 := by
  exact NumberField.prod_abs_eq_one (K := K) (x := θ) (by
    intro h
    have hsq := theta_sq
    rw [h] at hsq
    norm_num at hsq)

theorem product_formula_torsionGenerator :
    ((∏ w : NumberField.InfinitePlace K,
          w (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K)) ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K,
          v (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K))) = 1 := by
  exact NumberField.prod_abs_eq_one (K := K)
    (x := algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K)) (by
      intro h
      exact Units.ne_zero torsionGenerator (RingOfIntegers.coe_injective h))

end NumberField.SqrtNegSix


/-!
## Infinite Adele Ring
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

abbrev SqrtNegSixInfiniteAdeleRing : Type :=
  NumberField.InfiniteAdeleRing K

abbrev infinitePrincipalAdele_theta : SqrtNegSixInfiniteAdeleRing :=
  algebraMap K SqrtNegSixInfiniteAdeleRing θ

abbrev infinitePrincipalAdele_torsionGenerator : SqrtNegSixInfiniteAdeleRing :=
  algebraMap K SqrtNegSixInfiniteAdeleRing (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K))

theorem infiniteAdele_norm_theta :
    ‖infinitePrincipalAdele_theta‖ = |Algebra.norm ℚ θ| := by
  exact NumberField.InfiniteAdeleRing.coe_norm_eq_abs_norm θ

theorem infiniteAdele_denseRange :
    DenseRange (algebraMap K SqrtNegSixInfiniteAdeleRing) := by
  exact NumberField.InfiniteAdeleRing.denseRange_algebraMap K

end NumberField.SqrtNegSix


/-!
## Canonical Embedding
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

theorem canonicalEmbedding_apply_theta (σ : K →+* ℂ) :
    NumberField.canonicalEmbedding K θ σ = σ θ := by
  rfl

theorem canonicalEmbedding_thetaInt_mem_integerLattice :
    NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K thetaInt) ∈
      NumberField.canonicalEmbedding.integerLattice K := by
  simp [NumberField.canonicalEmbedding.integerLattice]

end NumberField.SqrtNegSix

/-!
## Canonical Embedding Geometry
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open MeasureTheory

namespace NumberField.SqrtNegSix

abbrev mixedEmbedding_theta : NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.mixedEmbedding K θ

theorem mixedEmbedding_theta_mem_convexBodyLT
    (f : NumberField.InfinitePlace K → NNReal)
    (hf : ∀ w : NumberField.InfinitePlace K, w θ < f w) :
    mixedEmbedding_theta ∈ NumberField.mixedEmbedding.convexBodyLT K f := by
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ,
    NumberField.mixedEmbedding.mixedEmbedding_apply_isReal, Metric.mem_ball, dist_zero_right,
    Real.norm_eq_abs, forall_const, Subtype.forall,
    NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
  constructor
  · intro a ha
    exact False.elim ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr ha)
      (infinitePlace_isComplex a))
  · intro a _ha
    simpa [NumberField.InfinitePlace.norm_embedding_eq a θ] using hf a

theorem measurableSet_fundamentalCone :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone K) := by
  exact NumberField.mixedEmbedding.measurableSet_fundamentalCone K

theorem measurableSet_normLeOne :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone.normLeOne K) := by
  exact NumberField.mixedEmbedding.fundamentalCone.measurableSet_normLeOne K

theorem polarSpace_nonempty :
    Nonempty (NumberField.mixedEmbedding.polarSpace K) := by
  infer_instance

end NumberField.SqrtNegSix


/-!
## House
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

theorem house_theta_pos :
    0 < NumberField.house θ := by
  exact lt_of_lt_of_le zero_lt_one
    (NumberField.one_le_house_of_isIntegral theta_integral (by
      intro h
      have hsq := theta_sq
      rw [h] at hsq
      norm_num at hsq))

theorem house_torsionGenerator :
    NumberField.house (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K)) = 1 := by
  simpa [torsionGenerator] using (NumberField.house_intCast (K := K) (-1 : ℤ))

end NumberField.SqrtNegSix


/-!
## Adele Ring
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

/-- The adele ring of `ℚ(√-6)`. -/
abbrev SqrtNegSixAdeleRing : Type :=
  NumberField.AdeleRing (𝓞 K) K

abbrev principalAdele_theta : SqrtNegSixAdeleRing :=
  algebraMap K SqrtNegSixAdeleRing θ

abbrev principalAdele_torsionGenerator : SqrtNegSixAdeleRing :=
  algebraMap K SqrtNegSixAdeleRing (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K))

theorem principalAdele_theta_ne_zero : principalAdele_theta ≠ 0 := by
  intro h
  have htheta : θ = 0 := by
    exact NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K) h
  have hsq := theta_sq
  rw [htheta] at hsq
  norm_num at hsq

theorem principalAdele_torsionGenerator_is_unit_everywhere :
    ∀ v : NumberField.FinitePlace K,
      v (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K)) = 1 := by
  intro v
  simp [torsionGenerator]

end NumberField.SqrtNegSix


/-!
## Dedekind Zeta
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

abbrev sqrtNegSixDedekindZeta (s : ℂ) : ℂ :=
  NumberField.dedekindZeta K s

abbrev sqrtNegSixDedekindZetaResidue : ℝ :=
  NumberField.dedekindZeta_residue K

theorem dedekindZeta_residue_pos :
    0 < sqrtNegSixDedekindZetaResidue := by
  exact NumberField.dedekindZeta_residue_pos K

theorem dedekindZeta_residue_class_number_formula :
    sqrtNegSixDedekindZetaResidue =
      (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
          (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          NumberField.Units.regulator K * NumberField.classNumber K) /
        (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|) := by
  exact NumberField.dedekindZeta_residue_def K

end NumberField.SqrtNegSix
