/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicEight.Euclidean

/-!
# `ℚ(ζ₈)` Local-global

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

namespace NumberField.CyclotomicEight

/-- The finite place over `2`, represented by the totally ramified prime `(1 - ζ)`. -/
def heightOneTwo : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {1 - zetaInt}
  isPrime := by
    exact isPrime_span_one_sub_zeta
  ne_bot := by
    intro h
    have hnorm := absNorm_span_one_sub_zeta
    rw [h] at hnorm
    norm_num at hnorm

/-- One degree-two finite place over `3`. -/
def heightOneThreeLeft : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {(3 : 𝓞 K), zetaInt ^ 2 + zetaInt + 2}
  isPrime := by
    exact isPrime_primesAboveThree.1
  ne_bot := by
    intro h
    have h3mem : (3 : 𝓞 K) ∈ Ideal.span {(3 : 𝓞 K), zetaInt ^ 2 + zetaInt + 2} :=
      Ideal.subset_span (by simp)
    rw [h] at h3mem
    norm_num at h3mem

/-- The other degree-two finite place over `3`. -/
def heightOneThreeRight : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {(3 : 𝓞 K), zetaInt ^ 2 + 2 * zetaInt + 2}
  isPrime := by
    exact isPrime_primesAboveThree.2
  ne_bot := by
    intro h
    have h3mem : (3 : 𝓞 K) ∈ Ideal.span {(3 : 𝓞 K), zetaInt ^ 2 + 2 * zetaInt + 2} :=
      Ideal.subset_span (by simp)
    rw [h] at h3mem
    norm_num at h3mem

abbrev vTwo : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk heightOneTwo

example :
    (Ideal.span {(2 : ℤ)}).ramificationIdx heightOneTwo.asIdeal = 4 := by
  exact ramificationIdx_span_one_sub_zeta

example :
    (Ideal.span {(2 : ℤ)}).inertiaDeg heightOneTwo.asIdeal = 1 := by
  exact inertiaDeg_span_one_sub_zeta

theorem vThreeLeft_inertiaDeg :
    (Ideal.span {(3 : ℤ)}).inertiaDeg heightOneThreeLeft.asIdeal = 2 := by
  haveI : heightOneThreeLeft.asIdeal.LiesOver (Ideal.span {(3 : ℤ)}) := by
    rw [Ideal.liesOver_span_iff heightOneThreeLeft.isPrime.ne_top
      (show Prime (3 : ℤ) by norm_num)]
    change (3 : 𝓞 K) ∈ heightOneThreeLeft.asIdeal
    exact Ideal.subset_span (by simp)
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := heightOneThreeLeft.asIdeal)
    (p := 3) Nat.prime_three
  change Ideal.absNorm (Ideal.span {(3 : 𝓞 K), zetaInt ^ 2 + zetaInt + 2}) =
    3 ^ (Ideal.span {(3 : ℤ)}).inertiaDeg heightOneThreeLeft.asIdeal at h
  rw [absNorm_primeAboveThreeLeft] at h
  have hpow : 3 ^ (Ideal.span {(3 : ℤ)}).inertiaDeg heightOneThreeLeft.asIdeal = 3 ^ 2 := by
    rw [← h]
    norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow

theorem vThreeRight_inertiaDeg :
    (Ideal.span {(3 : ℤ)}).inertiaDeg heightOneThreeRight.asIdeal = 2 := by
  haveI : heightOneThreeRight.asIdeal.LiesOver (Ideal.span {(3 : ℤ)}) := by
    rw [Ideal.liesOver_span_iff heightOneThreeRight.isPrime.ne_top
      (show Prime (3 : ℤ) by norm_num)]
    change (3 : 𝓞 K) ∈ heightOneThreeRight.asIdeal
    exact Ideal.subset_span (by simp)
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := heightOneThreeRight.asIdeal)
    (p := 3) Nat.prime_three
  change Ideal.absNorm (Ideal.span {(3 : 𝓞 K), zetaInt ^ 2 + 2 * zetaInt + 2}) =
    3 ^ (Ideal.span {(3 : ℤ)}).inertiaDeg heightOneThreeRight.asIdeal at h
  rw [absNorm_primeAboveThreeRight] at h
  have hpow : 3 ^ (Ideal.span {(3 : ℤ)}).inertiaDeg heightOneThreeRight.asIdeal = 3 ^ 2 := by
    rw [← h]
    norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow

end NumberField.CyclotomicEight

/-!
## Completions
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

/-- The completion of `ℚ(ζ₈)` at the totally ramified finite place above `2`. -/
abbrev CompletionAtTwo : Type :=
  heightOneTwo.adicCompletion K

end NumberField.CyclotomicEight

/-!
## Infinite Completions
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

abbrev InfiniteCompletion (v : NumberField.InfinitePlace K) : Type :=
  v.Completion

private theorem complexEmbedding_norm_zeta_eq_one (φ : K →+* ℂ) : ‖φ ζ‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (ζ := φ ζ) (n := 8) (by
    rw [← map_pow, zeta_isPrimitiveRoot.pow_eq_one, map_one]) (by norm_num : 8 ≠ 0)

example (v : NumberField.InfinitePlace K) :
    Nonempty (InfiniteCompletion v ≃+* ℂ) := by
  exact ⟨NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (infinitePlace_isComplex v)⟩

theorem infiniteCompletion_zeta_norm (v : NumberField.InfinitePlace K) :
    ‖(algebraMap K (InfiniteCompletion v) ζ)‖ = 1 := by
  change ‖(((WithAbs.equiv v.1).symm ζ : WithAbs v.1) : v.Completion)‖ = 1
  rw [NumberField.InfinitePlace.Completion.norm_coe, (WithAbs.equiv v.1).apply_symm_apply]
  rw [← NumberField.InfinitePlace.norm_embedding_eq]
  exact complexEmbedding_norm_zeta_eq_one (NumberField.InfinitePlace.embedding v)

end NumberField.CyclotomicEight

/-!
## Product Formula
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

private theorem zeta_ne_zero : ζ ≠ 0 := by
  intro h
  have hpow := zeta_isPrimitiveRoot.pow_eq_one
  rw [h] at hpow
  norm_num at hpow

example :
    ((∏ w : NumberField.InfinitePlace K, w ζ ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K, v ζ) = 1 := by
  exact NumberField.prod_abs_eq_one (K := K) (x := ζ) zeta_ne_zero

example :
    ((∏ w : NumberField.InfinitePlace K,
          w (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K,
          v (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))) = 1 := by
  exact NumberField.prod_abs_eq_one (K := K)
    (x := algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) (by
      intro h
      exact Units.ne_zero fundamentalUnit (RingOfIntegers.coe_injective h))

end NumberField.CyclotomicEight

/-!
## Infinite Adele Ring
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

abbrev CyclotomicEightInfiniteAdeleRing : Type :=
  NumberField.InfiniteAdeleRing K

abbrev infinitePrincipalAdele_zeta : CyclotomicEightInfiniteAdeleRing :=
  algebraMap K CyclotomicEightInfiniteAdeleRing ζ

abbrev infinitePrincipalAdele_fundamentalUnit : CyclotomicEightInfiniteAdeleRing :=
  algebraMap K CyclotomicEightInfiniteAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

example :
    ‖infinitePrincipalAdele_zeta‖ = |Algebra.norm ℚ ζ| := by
  exact NumberField.InfiniteAdeleRing.coe_norm_eq_abs_norm ζ

example :
    DenseRange (algebraMap K CyclotomicEightInfiniteAdeleRing) := by
  exact NumberField.InfiniteAdeleRing.denseRange_algebraMap K

end NumberField.CyclotomicEight

/-!
## Canonical Embedding
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

theorem canonicalEmbedding_zetaInt_mem_integerLattice :
    NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K zetaInt) ∈
      NumberField.canonicalEmbedding.integerLattice K := by
  change NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K zetaInt) ∈
    (RingHom.range (algebraMap (𝓞 K) K)).map (NumberField.canonicalEmbedding K)
  exact ⟨algebraMap (𝓞 K) K zetaInt, ⟨zetaInt, rfl⟩, rfl⟩

end NumberField.CyclotomicEight

/-!
## Canonical Embedding Geometry
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open MeasureTheory

namespace NumberField.CyclotomicEight

abbrev mixedEmbedding_zeta : NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.mixedEmbedding K ζ

example
    (f : NumberField.InfinitePlace K → NNReal)
    (hf : ∀ w : NumberField.InfinitePlace K, w ζ < f w) :
    mixedEmbedding_zeta ∈ NumberField.mixedEmbedding.convexBodyLT K f := by
  exact (NumberField.mixedEmbedding.convexBodyLT_mem (K := K) (f := f) (x := ζ)).2 hf

example :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone K) := by
  exact NumberField.mixedEmbedding.measurableSet_fundamentalCone K

example :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone.normLeOne K) := by
  exact NumberField.mixedEmbedding.fundamentalCone.measurableSet_normLeOne K

theorem polarSpace_nonempty :
    Nonempty (NumberField.mixedEmbedding.polarSpace K) := by
  infer_instance

end NumberField.CyclotomicEight

/-!
## House
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

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

example :
    0 < NumberField.house (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) := by
  exact lt_of_lt_of_le zero_lt_one
    (NumberField.one_le_house_of_isIntegral
      (NumberField.RingOfIntegers.isIntegral_coe (fundamentalUnit : 𝓞 K)) (by
      intro h
      exact Units.ne_zero fundamentalUnit (RingOfIntegers.coe_injective h)))

end NumberField.CyclotomicEight

/-!
## Adele Ring
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

/-- The adele ring of `ℚ(ζ₈)`. -/
abbrev CyclotomicEightAdeleRing : Type :=
  NumberField.AdeleRing (𝓞 K) K

abbrev principalAdele_zeta : CyclotomicEightAdeleRing :=
  algebraMap K CyclotomicEightAdeleRing ζ

abbrev principalAdele_fundamentalUnit : CyclotomicEightAdeleRing :=
  algebraMap K CyclotomicEightAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

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

end NumberField.CyclotomicEight

/-!
## Dedekind Zeta
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

abbrev cyclotomicEightDedekindZeta (s : ℂ) : ℂ :=
  NumberField.dedekindZeta K s

abbrev cyclotomicEightDedekindZetaResidue : ℝ :=
  NumberField.dedekindZeta_residue K

example :
    0 < cyclotomicEightDedekindZetaResidue := by
  exact NumberField.dedekindZeta_residue_pos K

example :
    cyclotomicEightDedekindZetaResidue =
      (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
          (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          NumberField.Units.regulator K * NumberField.classNumber K) /
        (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|) := by
  exact NumberField.dedekindZeta_residue_def K

end NumberField.CyclotomicEight
