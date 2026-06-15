/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.Euclidean

/-!
# `ℚ(√2)` Local-global

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

namespace NumberField.SqrtTwo

/-- The finite place over `2`, represented by the ramified prime `(√2)`. -/
def vTwo : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {sqrtTwoInteger}
  isPrime := isPrime_span_sqrtTwoInteger
  ne_bot := by
    intro h
    have hnorm := absNorm_span_sqrtTwoInteger
    rw [h] at hnorm
    norm_num at hnorm

/-- The inert finite place over `3`, represented by the prime ideal `(3)`. -/
def vThree : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {(3 : 𝓞 K)}
  isPrime := isPrime_span_three
  ne_bot := by
    intro h
    have hnorm := absNorm_span_three
    rw [h] at hnorm
    norm_num at hnorm

/-- One of the two finite places over `7`, represented by `(3 + √2)`. -/
def vSevenPlus : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {3 + sqrtTwoInteger}
  isPrime := isPrime_span_three_add_sqrtTwo
  ne_bot := by
    intro h
    have hnorm := absNorm_span_three_add_sqrtTwo
    rw [h] at hnorm
    norm_num at hnorm

/-- The other finite place over `7`, represented by `(3 - √2)`. -/
def vSevenMinus : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {3 - sqrtTwoInteger}
  isPrime := isPrime_span_three_sub_sqrtTwo
  ne_bot := by
    intro h
    have hnorm := absNorm_span_three_sub_sqrtTwo
    rw [h] at hnorm
    norm_num at hnorm

/-- The finite absolute value associated to the ramified place over `2`. -/
abbrev finitePlaceTwo : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk vTwo

/-- The finite absolute value associated to the inert place over `3`. -/
abbrev finitePlaceThree : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk vThree

/-- The first finite absolute value above `7`. -/
abbrev finitePlaceSevenPlus : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk vSevenPlus

/-- The second finite absolute value above `7`. -/
abbrev finitePlaceSevenMinus : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk vSevenMinus

example :
    (Ideal.span {(2 : ℤ)}).ramificationIdx vTwo.asIdeal = 2 := by
  exact ramificationIdx_span_sqrtTwoInteger

example :
    (Ideal.span {(2 : ℤ)}).inertiaDeg vTwo.asIdeal = 1 := by
  exact inertiaDeg_span_sqrtTwoInteger

example :
    (Ideal.span {(3 : ℤ)}).ramificationIdx vThree.asIdeal = 1 := by
  exact ramificationIdx_span_three

example :
    (Ideal.span {(3 : ℤ)}).inertiaDeg vThree.asIdeal = 2 := by
  exact inertiaDeg_span_three

example :
    (Ideal.span {(7 : ℤ)}).ramificationIdx vSevenPlus.asIdeal = 1 := by
  exact ramificationIdx_span_three_add_sqrtTwo

example :
    (Ideal.span {(7 : ℤ)}).ramificationIdx vSevenMinus.asIdeal = 1 := by
  exact ramificationIdx_span_three_sub_sqrtTwo

example :
    (Ideal.span {(7 : ℤ)}).inertiaDeg vSevenPlus.asIdeal = 1 := by
  exact inertiaDeg_span_three_add_sqrtTwo

example :
    (Ideal.span {(7 : ℤ)}).inertiaDeg vSevenMinus.asIdeal = 1 := by
  exact inertiaDeg_span_three_sub_sqrtTwo

end NumberField.SqrtTwo

/-!
## Completions
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtTwo

/-- The completion of `ℚ(√2)` at the ramified finite place over `2`. -/
abbrev CompletionAtTwo : Type :=
  vTwo.adicCompletion K

/-- The completion of `ℚ(√2)` at the inert finite place over `3`. -/
abbrev CompletionAtThree : Type :=
  vThree.adicCompletion K

/-- One completion of `ℚ(√2)` at a split finite place over `7`. -/
abbrev CompletionAtSevenPlus : Type :=
  vSevenPlus.adicCompletion K

/-- The other completion of `ℚ(√2)` at a split finite place over `7`. -/
abbrev CompletionAtSevenMinus : Type :=
  vSevenMinus.adicCompletion K

/-- The `2`-adic completion remembers the ramification index `2`. -/
example :
    (Ideal.span {(2 : ℤ)}).ramificationIdx vTwo.asIdeal = 2 := by
  exact ramificationIdx_span_sqrtTwoInteger

/-- The `3`-adic completion is the inert local factor, with residue degree `2`. -/
example :
    (Ideal.span {(3 : ℤ)}).inertiaDeg vThree.asIdeal = 2 := by
  exact inertiaDeg_span_three

/-- The two completions over `7` both have residue degree `1`. -/
example :
    (Ideal.span {(7 : ℤ)}).inertiaDeg vSevenPlus.asIdeal = 1 ∧
      (Ideal.span {(7 : ℤ)}).inertiaDeg vSevenMinus.asIdeal = 1 := by
  exact ⟨inertiaDeg_span_three_add_sqrtTwo, inertiaDeg_span_three_sub_sqrtTwo⟩

end NumberField.SqrtTwo

/-!
## Infinite Completions
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open NumberField

namespace NumberField.SqrtTwo

/-- The completion of `ℚ(√2)` at an infinite place. -/
abbrev InfiniteCompletion (v : NumberField.InfinitePlace K) : Type :=
  v.Completion

/-- Every infinite completion of `ℚ(√2)` is a real completion. -/
example (v : NumberField.InfinitePlace K) :
    Nonempty (InfiniteCompletion v ≃+* ℝ) := by
  exact ⟨NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (infinitePlace_isReal v)⟩

/-- The real isomorphism sends the image of `√2` to the expected real absolute value. -/
theorem infiniteCompletion_sqrtTwoRoot_norm (v : NumberField.InfinitePlace K) :
    ‖(algebraMap K (InfiniteCompletion v) sqrtTwoRoot)‖ = Real.sqrt 2 := by
  change ‖(((WithAbs.equiv v.1).symm sqrtTwoRoot : WithAbs v.1) : v.Completion)‖ =
    Real.sqrt 2
  rw [NumberField.InfinitePlace.Completion.norm_coe, (WithAbs.equiv v.1).apply_symm_apply]
  exact infinitePlace_apply_sqrtTwoRoot v

open scoped Classical in
/-- The completion-ramification formula at infinity specializes to the degree `2` of
`ℚ(√2)/ℚ`. -/
theorem infinitePlace_sum_inertiaDeg_eq_two (v : NumberField.InfinitePlace ℚ) :
    ∑ w ∈ v.placesOver K, v.inertiaDeg w = 2 := by
  rw [NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank (K := ℚ) (L := K) v]
  exact degree_eq_two

end NumberField.SqrtTwo

/-!
## Product Formula
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open IsDedekindDomain HeightOneSpectrum

namespace NumberField.SqrtTwo

/-- Product formula for the generator `√2`. -/
example :
    (∏ w : NumberField.InfinitePlace K, w sqrtTwoRoot ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K, v sqrtTwoRoot = 1 := by
  exact NumberField.prod_abs_eq_one (K := K) (x := sqrtTwoRoot) (by
    intro h
    have htwo : (2 : K) = 0 := by
      rw [← sqrtTwoRoot_sq, h]
      ring
    norm_num at htwo)

/-- Product formula for the fundamental unit `1 + √2`. -/
example :
    (∏ w : NumberField.InfinitePlace K,
          w (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K)) ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K,
          v (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K)) = 1 := by
  exact NumberField.prod_abs_eq_one (K := K)
    (x := algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K)) (by
      intro h
      have hunit : (sqrtTwoFundamentalUnit : 𝓞 K) = 0 := RingOfIntegers.coe_injective h
      exact Units.ne_zero sqrtTwoFundamentalUnit hunit)

/-- The finite-place contribution for the integral generator `√2` is concentrated at `vTwo`. -/
theorem finite_support_sqrtTwoRoot_only_vTwo
    (v : NumberField.FinitePlace K) (hv : v ≠ finitePlaceTwo) :
    v sqrtTwoRoot = 1 := by
  rw [← NumberField.FinitePlace.norm_embedding_eq v sqrtTwoRoot]
  change ‖NumberField.FinitePlace.embedding (NumberField.FinitePlace.maximalIdeal v)
      (algebraMap (𝓞 K) K sqrtTwoInteger)‖ = 1
  rw [NumberField.FinitePlace.norm_eq_one_iff_notMem (K := K)
    (v := NumberField.FinitePlace.maximalIdeal v)]
  intro hmem
  have hle : Ideal.span {sqrtTwoInteger} ≤
      (NumberField.FinitePlace.maximalIdeal v).asIdeal := by
    exact (Ideal.span_singleton_le_iff_mem
      (NumberField.FinitePlace.maximalIdeal v).asIdeal).mpr hmem
  have hmax_eq : NumberField.FinitePlace.maximalIdeal v = vTwo := by
    apply HeightOneSpectrum.ext_iff.mpr
    exact (Ideal.IsMaximal.eq_of_le (isMaximal vTwo) Ideal.IsPrime.ne_top' hle).symm
  apply hv
  rw [← NumberField.FinitePlace.mk_maximalIdeal v, hmax_eq]

end NumberField.SqrtTwo

/-!
## Infinite Adele Ring
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open NumberField

namespace NumberField.SqrtTwo

/-- The infinite adele ring of `ℚ(√2)`. -/
abbrev SqrtTwoInfiniteAdeleRing : Type :=
  NumberField.InfiniteAdeleRing K

/-- The principal infinite adele attached to `√2`. -/
abbrev infinitePrincipalAdele_sqrtTwoRoot : SqrtTwoInfiniteAdeleRing :=
  algebraMap K SqrtTwoInfiniteAdeleRing sqrtTwoRoot

/-- The principal infinite adele attached to the fundamental unit `1 + √2`. -/
abbrev infinitePrincipalAdele_fundamentalUnit : SqrtTwoInfiniteAdeleRing :=
  algebraMap K SqrtTwoInfiniteAdeleRing
    (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K))

example :
    ‖infinitePrincipalAdele_sqrtTwoRoot‖ = |Algebra.norm ℚ sqrtTwoRoot| := by
  exact NumberField.InfiniteAdeleRing.coe_norm_eq_abs_norm sqrtTwoRoot

example :
    ‖infinitePrincipalAdele_fundamentalUnit‖ =
      |Algebra.norm ℚ (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K))| := by
  exact NumberField.InfiniteAdeleRing.coe_norm_eq_abs_norm
    (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K))

example :
    DenseRange (algebraMap K SqrtTwoInfiniteAdeleRing) := by
  exact NumberField.InfiniteAdeleRing.denseRange_algebraMap K

end NumberField.SqrtTwo

/-!
## Canonical Embedding
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtTwo

private theorem complexEmbedding_norm_sqrtTwoRoot (φ : K →+* ℂ) :
    ‖φ sqrtTwoRoot‖ = Real.sqrt 2 := by
  simpa using infinitePlace_apply_sqrtTwoRoot (NumberField.InfinitePlace.mk φ)

/-- The canonical embedding of `√2` has house/norm equal to the positive square root `√2`. -/
theorem canonicalEmbedding_norm_sqrtTwoRoot :
    ‖NumberField.canonicalEmbedding K sqrtTwoRoot‖ = Real.sqrt 2 := by
  apply le_antisymm
  · rw [NumberField.canonicalEmbedding.norm_le_iff]
    intro φ
    rw [complexEmbedding_norm_sqrtTwoRoot φ]
  · obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
    calc
      Real.sqrt 2 = ‖NumberField.canonicalEmbedding K sqrtTwoRoot φ‖ := by
        rw [NumberField.canonicalEmbedding.apply_at, complexEmbedding_norm_sqrtTwoRoot φ]
      _ ≤ ‖NumberField.canonicalEmbedding K sqrtTwoRoot‖ := norm_le_pi_norm _ φ

/-- The integral generator maps into the canonical integer lattice. -/
theorem canonicalEmbedding_sqrtTwoInteger_mem_integerLattice :
    NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K sqrtTwoInteger) ∈
      NumberField.canonicalEmbedding.integerLattice K := by
  change NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K sqrtTwoInteger) ∈
    (RingHom.range (algebraMap (𝓞 K) K)).map (NumberField.canonicalEmbedding K)
  exact ⟨algebraMap (𝓞 K) K sqrtTwoInteger, ⟨sqrtTwoInteger, rfl⟩, rfl⟩

/-- The fundamental unit has archimedean coordinates `1 + √2` and `1 - √2`. -/
theorem canonicalEmbedding_fundamentalUnit_coordinates :
    ∃ σ τ : K →+* ℂ,
      σ (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K)) =
          (1 + Real.sqrt 2 : ℝ) ∧
        τ (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K)) =
          (1 - Real.sqrt 2 : ℝ) := by
  obtain ⟨σ, hσ⟩ := exists_realEmbedding_pos
  obtain ⟨τ, hτ⟩ := exists_realEmbedding_neg
  refine ⟨Complex.ofRealHom.comp σ.toRingHom, Complex.ofRealHom.comp τ.toRingHom, ?_, ?_⟩
  · change ↑(σ (sqrtTwoRoot + 1)) = ((1 + Real.sqrt 2 : ℝ) : ℂ)
    rw [map_add, hσ]
    norm_num [add_comm]
  · change ↑(τ (sqrtTwoRoot + 1)) = ((1 - Real.sqrt 2 : ℝ) : ℂ)
    rw [map_add, hτ, map_one]
    ring_nf

end NumberField.SqrtTwo

/-!
## Canonical Embedding Geometry
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open MeasureTheory NumberField

namespace NumberField.SqrtTwo

/-- The mixed embedding of the generator `√2`. -/
abbrev mixedEmbedding_sqrtTwoRoot : NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.mixedEmbedding K sqrtTwoRoot

example
    (f : NumberField.InfinitePlace K → NNReal)
    (hf : ∀ w : NumberField.InfinitePlace K, w sqrtTwoRoot < f w) :
    mixedEmbedding_sqrtTwoRoot ∈ NumberField.mixedEmbedding.convexBodyLT K f := by
  exact (NumberField.mixedEmbedding.convexBodyLT_mem (K := K) (f := f) (x := sqrtTwoRoot)).2 hf

example :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone K) := by
  exact NumberField.mixedEmbedding.measurableSet_fundamentalCone K

example :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone.normLeOne K) := by
  exact NumberField.mixedEmbedding.fundamentalCone.measurableSet_normLeOne K

theorem polarSpace_nonempty :
    Nonempty (NumberField.mixedEmbedding.polarSpace K) := by
  infer_instance

/-- In `ℚ(√2)`, a unit sends a point of the fundamental cone back into the same
fundamental cone iff it is one of the two roots of unity `±1`. -/
theorem unit_smul_mem_fundamentalCone_iff_eq_one_or_neg_one
    {x : NumberField.mixedEmbedding.mixedSpace K}
    (hx : x ∈ NumberField.mixedEmbedding.fundamentalCone K)
    (u : (𝓞 K)ˣ) :
    u • x ∈ NumberField.mixedEmbedding.fundamentalCone K ↔ u = 1 ∨ u = -1 := by
  rw [NumberField.mixedEmbedding.fundamentalCone.unit_smul_mem_iff_mem_torsion hx u]
  exact mem_torsion_iff_eq_one_or_neg_one u

end NumberField.SqrtTwo

/-!
## House
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtTwo

/-- The house of `√2` is `√2`. -/
theorem house_sqrtTwoRoot :
    NumberField.house sqrtTwoRoot = Real.sqrt 2 := by
  rw [NumberField.house, canonicalEmbedding_norm_sqrtTwoRoot]

/-- The house of the integral generator `√2 ∈ 𝓞 K` is `√2`. -/
theorem house_sqrtTwoInteger :
    NumberField.house (algebraMap (𝓞 K) K sqrtTwoInteger) = Real.sqrt 2 := by
  simpa [sqrtTwoInteger] using house_sqrtTwoRoot

/-- The house of the fundamental unit `1 + √2` is `1 + √2`. -/
theorem house_sqrtTwoFundamentalUnit :
    NumberField.house (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K)) =
      1 + Real.sqrt 2 := by
  change NumberField.house (sqrtTwoRoot + 1) = 1 + Real.sqrt 2
  apply le_antisymm
  · rw [NumberField.house, NumberField.canonicalEmbedding.norm_le_iff]
    intro φ
    have hnorm : ‖φ sqrtTwoRoot‖ = Real.sqrt 2 := by
      simpa using infinitePlace_apply_sqrtTwoRoot (NumberField.InfinitePlace.mk φ)
    calc
      ‖φ (sqrtTwoRoot + 1)‖ ≤ ‖φ sqrtTwoRoot‖ + ‖φ 1‖ := by
        simpa [map_add] using norm_add_le (φ sqrtTwoRoot) (φ 1)
      _ = 1 + Real.sqrt 2 := by rw [hnorm, map_one, norm_one, add_comm]
  · obtain ⟨σ, _, hσ, _⟩ := canonicalEmbedding_fundamentalUnit_coordinates
    calc
      1 + Real.sqrt 2 =
          ‖σ (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K))‖ := by
        rw [hσ, Complex.norm_of_nonneg]
        positivity
      _ = ‖σ (sqrtTwoRoot + 1)‖ := by rfl
      _ = ‖NumberField.canonicalEmbedding K (sqrtTwoRoot + 1) σ‖ := by
        rw [NumberField.canonicalEmbedding.apply_at]
      _ ≤ ‖NumberField.canonicalEmbedding K (sqrtTwoRoot + 1)‖ := norm_le_pi_norm _ σ

end NumberField.SqrtTwo

/-!
## Adele Ring
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtTwo

/-- The adele ring of `ℚ(√2)` with respect to its ring of integers. -/
abbrev SqrtTwoAdeleRing : Type :=
  NumberField.AdeleRing (𝓞 K) K

/-- The principal adele associated to `√2`. -/
abbrev principalAdele_sqrtTwoRoot : SqrtTwoAdeleRing :=
  algebraMap K SqrtTwoAdeleRing sqrtTwoRoot

/-- The principal adele associated to the fundamental unit `1 + √2`. -/
abbrev principalAdele_fundamentalUnit : SqrtTwoAdeleRing :=
  algebraMap K SqrtTwoAdeleRing (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K))

/-- The diagonal embedding sends the nonzero element `√2` to a nonzero adele. -/
theorem principalAdele_sqrtTwoRoot_ne_zero :
    principalAdele_sqrtTwoRoot ≠ 0 := by
  intro h
  have hroot : sqrtTwoRoot = 0 :=
    NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K) h
  have htwo : (2 : K) = 0 := by
    rw [← sqrtTwoRoot_sq, hroot]
    ring
  norm_num at htwo

/-- The principal adele of the fundamental unit is a unit in every local component. -/
theorem principalAdele_fundamentalUnit_is_unit_everywhere :
    ∀ v : NumberField.FinitePlace K,
      v (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K)) = 1 := by
  intro v
  rw [← NumberField.FinitePlace.norm_embedding_eq v
    (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K))]
  rw [NumberField.FinitePlace.norm_eq_one_iff_notMem (K := K)
    (v := NumberField.FinitePlace.maximalIdeal v)]
  intro hmem
  have hmul :
      (sqrtTwoFundamentalUnit : 𝓞 K) *
          ((sqrtTwoFundamentalUnit⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
    change (sqrtTwoInteger + 1) * (sqrtTwoInteger - 1) = (1 : 𝓞 K)
    apply Subtype.ext
    change (sqrtTwoRoot + 1) * (sqrtTwoRoot - 1) = (1 : K)
    calc
      (sqrtTwoRoot + 1) * (sqrtTwoRoot - 1) = sqrtTwoRoot ^ 2 - 1 := by ring
      _ = (1 : K) := by rw [sqrtTwoRoot_sq]; ring
  have h_mem_mul :
      (sqrtTwoFundamentalUnit : 𝓞 K) *
          ((sqrtTwoFundamentalUnit⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ∈
        (NumberField.FinitePlace.maximalIdeal v).asIdeal :=
    Ideal.mul_mem_right ((sqrtTwoFundamentalUnit⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
      (NumberField.FinitePlace.maximalIdeal v).asIdeal hmem
  have h_one : (1 : 𝓞 K) ∈ (NumberField.FinitePlace.maximalIdeal v).asIdeal := by
    rwa [hmul] at h_mem_mul
  exact (NumberField.FinitePlace.maximalIdeal v).isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr h_one)

end NumberField.SqrtTwo

/-!
## Dedekind Zeta
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open NumberField

namespace NumberField.SqrtTwo

/-- The Dedekind zeta function of `ℚ(√2)`. -/
abbrev sqrtTwoDedekindZeta (s : ℂ) : ℂ :=
  NumberField.dedekindZeta K s

/-- The class-number-formula residue for `ℚ(√2)`. -/
abbrev sqrtTwoDedekindZetaResidue : ℝ :=
  NumberField.dedekindZeta_residue K

example :
    0 < sqrtTwoDedekindZetaResidue := by
  exact NumberField.dedekindZeta_residue_pos K

example :
    sqrtTwoDedekindZetaResidue =
      (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
          (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          NumberField.Units.regulator K * NumberField.classNumber K) /
        (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|) := by
  exact NumberField.dedekindZeta_residue_def K

end NumberField.SqrtTwo
