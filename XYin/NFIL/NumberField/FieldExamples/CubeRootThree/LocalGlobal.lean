/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NFIL.NumberField.FieldExamples.CubeRootThree.Euclidean

/-!
# `ℚ(∛3)` Local-global

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

namespace NumberField.CubeRootThree

/-- The finite place over `3`, represented by the totally ramified prime `(θ)`. -/
def heightOneThree : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {thetaInt}
  isPrime := by
    exact isPrime_span_theta
  ne_bot := by
    intro h
    have hnorm := absNorm_span_theta
    rw [h, Ideal.absNorm_bot] at hnorm
    norm_num at hnorm

/-- The degree-one prime above `2`, represented by `(θ - 1)`. -/
def heightOneTwoLinear : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {thetaInt - 1}
  isPrime := by
    exact isPrime_span_theta_sub_one
  ne_bot := by
    intro h
    have hnorm := absNorm_span_theta_sub_one
    rw [h, Ideal.absNorm_bot] at hnorm
    norm_num at hnorm

/-- The degree-two prime above `2`, represented by `(θ² + θ + 1)`. -/
def heightOneTwoQuadratic : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {thetaInt ^ 2 + thetaInt + 1}
  isPrime := by
    exact isPrime_span_theta_sq_add_theta_add_one
  ne_bot := by
    intro h
    have hnorm := absNorm_span_theta_sq_add_theta_add_one
    rw [h, Ideal.absNorm_bot] at hnorm
    norm_num at hnorm

/-- The inert finite place above `7`. -/
def heightOneSeven : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {(7 : 𝓞 K)}
  isPrime := by
    exact isPrime_span_seven
  ne_bot := by
    intro h
    have hnorm := absNorm_span_seven
    rw [h, Ideal.absNorm_bot] at hnorm
    norm_num at hnorm

/-- One degree-one finite place above `61`. -/
def heightOneSixtyOneFour : HeightOneSpectrum (𝓞 K) where
  asIdeal := primeAbove61 4
  isPrime := by
    exact isPrime_primeAbove61 4 (Or.inl rfl)
  ne_bot := by
    intro h
    have hnorm := absNorm_primeAbove61 4 (Or.inl rfl)
    rw [h, Ideal.absNorm_bot] at hnorm
    norm_num at hnorm

/-- One degree-one finite place above `61`. -/
def heightOneSixtyOneFive : HeightOneSpectrum (𝓞 K) where
  asIdeal := primeAbove61 5
  isPrime := by
    exact isPrime_primeAbove61 5 (Or.inr (Or.inl rfl))
  ne_bot := by
    intro h
    have hnorm := absNorm_primeAbove61 5 (Or.inr (Or.inl rfl))
    rw [h, Ideal.absNorm_bot] at hnorm
    norm_num at hnorm

/-- One degree-one finite place above `61`. -/
def heightOneSixtyOneFiftyTwo : HeightOneSpectrum (𝓞 K) where
  asIdeal := primeAbove61 52
  isPrime := by
    exact isPrime_primeAbove61 52 (Or.inr (Or.inr rfl))
  ne_bot := by
    intro h
    have hnorm := absNorm_primeAbove61 52 (Or.inr (Or.inr rfl))
    rw [h, Ideal.absNorm_bot] at hnorm
    norm_num at hnorm

abbrev vThree : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk heightOneThree

example :
    (Ideal.span {(3 : ℤ)}).ramificationIdx heightOneThree.asIdeal = 3 := by
  exact ramificationIdx_span_theta

example :
    (Ideal.span {(3 : ℤ)}).inertiaDeg heightOneThree.asIdeal = 1 := by
  exact inertiaDeg_span_theta

example :
    (Ideal.span {(2 : ℤ)}).inertiaDeg heightOneTwoLinear.asIdeal = 1 := by
  exact inertiaDeg_span_theta_sub_one

example :
    (Ideal.span {(2 : ℤ)}).inertiaDeg heightOneTwoQuadratic.asIdeal = 2 := by
  exact inertiaDeg_span_theta_sq_add_theta_add_one

example :
    (Ideal.span {(7 : ℤ)}).inertiaDeg heightOneSeven.asIdeal = 3 := by
  exact inertiaDeg_span_seven

example :
    (Ideal.span {(61 : ℤ)}).inertiaDeg heightOneSixtyOneFour.asIdeal = 1 ∧
      (Ideal.span {(61 : ℤ)}).inertiaDeg heightOneSixtyOneFive.asIdeal = 1 ∧
        (Ideal.span {(61 : ℤ)}).inertiaDeg heightOneSixtyOneFiftyTwo.asIdeal = 1 := by
  exact ⟨inertiaDeg_primeAbove61 4 (Or.inl rfl),
    inertiaDeg_primeAbove61 5 (Or.inr (Or.inl rfl)),
    inertiaDeg_primeAbove61 52 (Or.inr (Or.inr rfl))⟩

end NumberField.CubeRootThree

/-!
## Completions
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

/-- The completion of `ℚ(∛3)` at the totally ramified finite place above `3`. -/
abbrev CompletionAtThree : Type :=
  heightOneThree.adicCompletion K

end NumberField.CubeRootThree

/-!
## Infinite Completions
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

abbrev InfiniteCompletion (v : NumberField.InfinitePlace K) : Type :=
  v.Completion

example
    (v : NumberField.InfinitePlace K) (hv : NumberField.InfinitePlace.IsReal v) :
    Nonempty (InfiniteCompletion v ≃+* ℝ) := by
  exact ⟨NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv⟩

example
    (v : NumberField.InfinitePlace K) (hv : NumberField.InfinitePlace.IsComplex v) :
    Nonempty (InfiniteCompletion v ≃+* ℂ) := by
  exact ⟨NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv⟩

end NumberField.CubeRootThree

/-!
## Product Formula
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

theorem product_formula_cubeRootThree :
    ((∏ w : NumberField.InfinitePlace K, w cubeRootThree ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K, v cubeRootThree) = 1 := by
  have hne : cubeRootThree ≠ 0 := by
    intro h
    have hcube := cubeRootThree_cube
    rw [h] at hcube
    norm_num at hcube
  exact NumberField.prod_abs_eq_one (K := K) (x := cubeRootThree) (h_x_nezero := hne)

example :
    ((∏ w : NumberField.InfinitePlace K,
          w (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K,
          v (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))) = 1 := by
  have hne : algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K) ≠ 0 := by
    intro h
    have h' : (fundamentalUnit : 𝓞 K) = 0 :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K h
    exact Units.ne_zero fundamentalUnit h'
  exact NumberField.prod_abs_eq_one (K := K)
    (x := algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) (h_x_nezero := hne)

end NumberField.CubeRootThree

/-!
## Infinite Adele Ring
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

abbrev CubeRootThreeInfiniteAdeleRing : Type :=
  NumberField.InfiniteAdeleRing K

abbrev infinitePrincipalAdele_cubeRootThree : CubeRootThreeInfiniteAdeleRing :=
  algebraMap K CubeRootThreeInfiniteAdeleRing cubeRootThree

abbrev infinitePrincipalAdele_fundamentalUnit : CubeRootThreeInfiniteAdeleRing :=
  algebraMap K CubeRootThreeInfiniteAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

example :
    ‖infinitePrincipalAdele_cubeRootThree‖ = |Algebra.norm ℚ cubeRootThree| := by
  exact NumberField.InfiniteAdeleRing.coe_norm_eq_abs_norm cubeRootThree

example :
    DenseRange (algebraMap K CubeRootThreeInfiniteAdeleRing) := by
  exact NumberField.InfiniteAdeleRing.denseRange_algebraMap (K := K)

end NumberField.CubeRootThree

/-!
## Canonical Embedding
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

theorem canonicalEmbedding_thetaInt_mem_integerLattice :
    NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K thetaInt) ∈
      NumberField.canonicalEmbedding.integerLattice K := by
  simp [NumberField.canonicalEmbedding.integerLattice]

end NumberField.CubeRootThree

/-!
## Canonical Embedding Geometry
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open MeasureTheory

namespace NumberField.CubeRootThree

abbrev mixedEmbedding_cubeRootThree : NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.mixedEmbedding K cubeRootThree

example
    (f : NumberField.InfinitePlace K → NNReal)
    (hf : ∀ w : NumberField.InfinitePlace K, w cubeRootThree < f w) :
    mixedEmbedding_cubeRootThree ∈ NumberField.mixedEmbedding.convexBodyLT K f := by
  exact (NumberField.mixedEmbedding.convexBodyLT_mem (K := K) (f := f) (x := cubeRootThree)).mpr hf

example :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone K) := by
  exact NumberField.mixedEmbedding.measurableSet_fundamentalCone K

example :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone.normLeOne K) := by
  exact NumberField.mixedEmbedding.fundamentalCone.measurableSet_normLeOne K

theorem polarSpace_nonempty :
    Nonempty (NumberField.mixedEmbedding.polarSpace K) := by
  infer_instance

end NumberField.CubeRootThree

/-!
## House
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

theorem house_cubeRootThree_pos :
    0 < NumberField.house cubeRootThree := by
  exact lt_of_lt_of_le zero_lt_one
    (NumberField.one_le_house_of_isIntegral cubeRootThree_integral (by
      intro h
      have hcube := cubeRootThree_cube
      rw [h] at hcube
      norm_num at hcube))

theorem house_thetaInt_pos :
    0 < NumberField.house (algebraMap (𝓞 K) K thetaInt) := by
  have ht : algebraMap (𝓞 K) K thetaInt = cubeRootThree :=
    NumberField.RingOfIntegers.map_mk cubeRootThree cubeRootThree_integral
  rw [ht]
  exact house_cubeRootThree_pos

end NumberField.CubeRootThree

/-!
## Adele Ring
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

/-- The adele ring of `ℚ(∛3)`. -/
abbrev CubeRootThreeAdeleRing : Type :=
  NumberField.AdeleRing (𝓞 K) K

abbrev principalAdele_cubeRootThree : CubeRootThreeAdeleRing :=
  algebraMap K CubeRootThreeAdeleRing cubeRootThree

abbrev principalAdele_fundamentalUnit : CubeRootThreeAdeleRing :=
  algebraMap K CubeRootThreeAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

theorem principalAdele_cubeRootThree_ne_zero : principalAdele_cubeRootThree ≠ 0 := by
  intro h
  have h0 : cubeRootThree = 0 :=
    NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K) h
  have hcube := cubeRootThree_cube
  rw [h0] at hcube
  norm_num at hcube

theorem principalAdele_fundamentalUnit_is_unit_everywhere :
    ∀ v : NumberField.FinitePlace K,
      v (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) = 1 := by
  intro v
  have hnot : (fundamentalUnit : 𝓞 K) ∉ v.maximalIdeal.asIdeal := by
    intro hmem
    exact v.maximalIdeal.isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmem (Units.isUnit fundamentalUnit))
  rw [← NumberField.FinitePlace.norm_embedding_eq v]
  exact (NumberField.FinitePlace.norm_eq_one_iff_notMem (K := K) (v := v.maximalIdeal)
    (x := (fundamentalUnit : 𝓞 K))).mpr hnot

end NumberField.CubeRootThree

/-!
## Dedekind Zeta
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

abbrev cubeRootThreeDedekindZeta (s : ℂ) : ℂ :=
  NumberField.dedekindZeta K s

abbrev cubeRootThreeDedekindZetaResidue : ℝ :=
  NumberField.dedekindZeta_residue K

example :
    0 < cubeRootThreeDedekindZetaResidue := by
  exact NumberField.dedekindZeta_residue_pos K

example :
    cubeRootThreeDedekindZetaResidue =
      (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
          (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          NumberField.Units.regulator K * NumberField.classNumber K) /
        (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|) := by
  rfl

end NumberField.CubeRootThree
