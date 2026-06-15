/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicFive.Euclidean

/-!
# `ℚ(ζ₅)` Local-global

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

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial
open IsDedekindDomain

namespace NumberField.CyclotomicFive

/-- The finite place over `5`, represented by the totally ramified prime `(1 - ζ)`. -/
def heightOneFive : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {1 - zetaInt}
  isPrime := by
    exact isPrime_span_one_sub_zeta
  ne_bot := by
    intro h
    have hnorm := absNorm_span_one_sub_zeta
    rw [h] at hnorm
    norm_num at hnorm

abbrev vFive : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk heightOneFive

theorem vFive_ramificationIdx :
    (Ideal.span {(5 : ℤ)}).ramificationIdx heightOneFive.asIdeal = 4 := by
  exact ramificationIdx_span_one_sub_zeta

theorem vFive_inertiaDeg :
    (Ideal.span {(5 : ℤ)}).inertiaDeg heightOneFive.asIdeal = 1 := by
  exact inertiaDeg_span_one_sub_zeta

end NumberField.CyclotomicFive


/-!
## Completions
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

/-- The completion of `ℚ(ζ₅)` at the totally ramified finite place above `5`. -/
abbrev CompletionAtFive : Type :=
  heightOneFive.adicCompletion K

theorem completionAtFive_contains_zeta :
    ∃ x : CompletionAtFive,
      x = NumberField.FinitePlace.embedding (K := K) heightOneFive ζ := by
  exact ⟨NumberField.FinitePlace.embedding (K := K) heightOneFive ζ, rfl⟩

end NumberField.CyclotomicFive


/-!
## Infinite Completions
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

abbrev InfiniteCompletion (v : NumberField.InfinitePlace K) : Type :=
  v.Completion

private theorem complexEmbedding_norm_zeta_eq_one (φ : K →+* ℂ) : ‖φ ζ‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (ζ := φ ζ) (n := 5) (by
    rw [← map_pow, zeta_isPrimitiveRoot.pow_eq_one, map_one]) (by norm_num : 5 ≠ 0)

theorem infiniteCompletion_equiv_complex (v : NumberField.InfinitePlace K) :
    Nonempty (InfiniteCompletion v ≃+* ℂ) := by
  exact ⟨NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (infinitePlace_isComplex v)⟩

theorem infiniteCompletion_zeta_norm (v : NumberField.InfinitePlace K) :
    ‖(algebraMap K (InfiniteCompletion v) ζ)‖ = 1 := by
  change ‖(((WithAbs.equiv v.1).symm ζ : WithAbs v.1) : v.Completion)‖ = 1
  rw [NumberField.InfinitePlace.Completion.norm_coe, (WithAbs.equiv v.1).apply_symm_apply]
  rw [← NumberField.InfinitePlace.norm_embedding_eq]
  exact complexEmbedding_norm_zeta_eq_one (NumberField.InfinitePlace.embedding v)

end NumberField.CyclotomicFive


/-!
## Product Formula
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

private theorem zeta_ne_zero : ζ ≠ 0 := by
  intro h
  have hpow := zeta_isPrimitiveRoot.pow_eq_one
  rw [h] at hpow
  norm_num at hpow

theorem product_formula_zeta :
    ((∏ w : NumberField.InfinitePlace K, w ζ ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K, v ζ) = 1 := by
  exact NumberField.prod_abs_eq_one (K := K) (x := ζ) zeta_ne_zero

theorem product_formula_fundamentalUnit :
    ((∏ w : NumberField.InfinitePlace K,
          w (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K,
          v (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))) = 1 := by
  exact NumberField.prod_abs_eq_one (K := K)
    (x := algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) (by
      intro h
      exact Units.ne_zero fundamentalUnit (RingOfIntegers.coe_injective h))

end NumberField.CyclotomicFive


/-!
## Infinite Adele Ring
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

abbrev CyclotomicFiveInfiniteAdeleRing : Type :=
  NumberField.InfiniteAdeleRing K

abbrev infinitePrincipalAdele_zeta : CyclotomicFiveInfiniteAdeleRing :=
  algebraMap K CyclotomicFiveInfiniteAdeleRing ζ

abbrev infinitePrincipalAdele_fundamentalUnit : CyclotomicFiveInfiniteAdeleRing :=
  algebraMap K CyclotomicFiveInfiniteAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

theorem infiniteAdele_norm_zeta :
    ‖infinitePrincipalAdele_zeta‖ = |Algebra.norm ℚ ζ| := by
  exact NumberField.InfiniteAdeleRing.coe_norm_eq_abs_norm ζ

theorem infiniteAdele_denseRange :
    DenseRange (algebraMap K CyclotomicFiveInfiniteAdeleRing) := by
  exact NumberField.InfiniteAdeleRing.denseRange_algebraMap K

end NumberField.CyclotomicFive


/-!
## Canonical Embedding
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

theorem canonicalEmbedding_apply_zeta (σ : K →+* ℂ) :
    NumberField.canonicalEmbedding K ζ σ = σ ζ := by
  rfl

theorem canonicalEmbedding_zetaInt_mem_integerLattice :
    NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K zetaInt) ∈
      NumberField.canonicalEmbedding.integerLattice K := by
  change NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K zetaInt) ∈
    (RingHom.range (algebraMap (𝓞 K) K)).map (NumberField.canonicalEmbedding K)
  exact ⟨algebraMap (𝓞 K) K zetaInt, ⟨zetaInt, rfl⟩, rfl⟩

end NumberField.CyclotomicFive

/-!
## Canonical Embedding Geometry
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open MeasureTheory

namespace NumberField.CyclotomicFive

abbrev mixedEmbedding_zeta : NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.mixedEmbedding K ζ

theorem mixedEmbedding_zeta_mem_convexBodyLT
    (f : NumberField.InfinitePlace K → NNReal)
    (hf : ∀ w : NumberField.InfinitePlace K, w ζ < f w) :
    mixedEmbedding_zeta ∈ NumberField.mixedEmbedding.convexBodyLT K f := by
  exact (NumberField.mixedEmbedding.convexBodyLT_mem (K := K) (f := f) (x := ζ)).2 hf

theorem measurableSet_fundamentalCone :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone K) := by
  exact NumberField.mixedEmbedding.measurableSet_fundamentalCone K

theorem measurableSet_normLeOne :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone.normLeOne K) := by
  exact NumberField.mixedEmbedding.fundamentalCone.measurableSet_normLeOne K

theorem polarSpace_nonempty :
    Nonempty (NumberField.mixedEmbedding.polarSpace K) := by
  infer_instance

end NumberField.CyclotomicFive


/-!
## House
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

theorem house_zeta :
    NumberField.house ζ = 1 := by
  rw [NumberField.house]
  apply le_antisymm
  · rw [NumberField.canonicalEmbedding.norm_le_iff]
    intro φ
    rw [complexEmbedding_norm_zeta_eq_one φ]
  · obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
    calc
      1 = ‖NumberField.canonicalEmbedding K ζ φ‖ := by
        rw [NumberField.canonicalEmbedding.apply_at, complexEmbedding_norm_zeta_eq_one φ]
      _ ≤ ‖NumberField.canonicalEmbedding K ζ‖ := norm_le_pi_norm _ φ

theorem house_fundamentalUnit_pos :
    0 < NumberField.house (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) := by
  exact lt_of_lt_of_le zero_lt_one
    (NumberField.one_le_house_of_isIntegral
      (NumberField.RingOfIntegers.isIntegral_coe (fundamentalUnit : 𝓞 K)) (by
      intro h
      exact Units.ne_zero fundamentalUnit (RingOfIntegers.coe_injective h)))

end NumberField.CyclotomicFive


/-!
## Adele Ring
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

/-- The adele ring of `ℚ(ζ₅)`. -/
abbrev CyclotomicFiveAdeleRing : Type :=
  NumberField.AdeleRing (𝓞 K) K

abbrev principalAdele_zeta : CyclotomicFiveAdeleRing :=
  algebraMap K CyclotomicFiveAdeleRing ζ

abbrev principalAdele_fundamentalUnit : CyclotomicFiveAdeleRing :=
  algebraMap K CyclotomicFiveAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

theorem principalAdele_zeta_ne_zero : principalAdele_zeta ≠ 0 := by
  intro h
  exact zeta_ne_zero (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K) h)

theorem principalAdele_fundamentalUnit_is_unit_everywhere :
    ∀ v : NumberField.FinitePlace K,
      v (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) = 1 := by
  intro v
  rw [← NumberField.FinitePlace.norm_embedding_eq v
    (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))]
  rw [NumberField.FinitePlace.norm_eq_one_iff_notMem (K := K)
    (v := NumberField.FinitePlace.maximalIdeal v)]
  intro hmem
  have hmul : (fundamentalUnit : 𝓞 K) *
      ((fundamentalUnit⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
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

end NumberField.CyclotomicFive


/-!
## Dedekind Zeta
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

abbrev cyclotomicFiveDedekindZeta (s : ℂ) : ℂ :=
  NumberField.dedekindZeta K s

abbrev cyclotomicFiveDedekindZetaResidue : ℝ :=
  NumberField.dedekindZeta_residue K

theorem dedekindZeta_residue_pos :
    0 < cyclotomicFiveDedekindZetaResidue := by
  exact NumberField.dedekindZeta_residue_pos K

theorem dedekindZeta_residue_class_number_formula :
    cyclotomicFiveDedekindZetaResidue =
      (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
          (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          NumberField.Units.regulator K * NumberField.classNumber K) /
        (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|) := by
  exact NumberField.dedekindZeta_residue_def K

end NumberField.CyclotomicFive
