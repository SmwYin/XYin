/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.Embeddings
import XYin.NumberField.FieldExamples.SqrtTwo.FinitePlaces
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# Product formula examples in `ℚ(√2)`

This file specializes mathlib's number-field product formula to the standard
elements of the `ℚ(√2)` example.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open IsDedekindDomain HeightOneSpectrum

namespace NumberField.SqrtTwo

/-- Product formula for the generator `√2`. -/
theorem product_formula_sqrtTwoRoot :
    (∏ w : NumberField.InfinitePlace K, w sqrtTwoRoot ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K, v sqrtTwoRoot = 1 := by
  exact NumberField.prod_abs_eq_one (K := K) (x := sqrtTwoRoot) (by
    intro h
    have htwo : (2 : K) = 0 := by
      rw [← sqrtTwoRoot_sq, h]
      ring
    norm_num at htwo)

/-- Product formula for the fundamental unit `1 + √2`. -/
theorem product_formula_fundamentalUnit :
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
