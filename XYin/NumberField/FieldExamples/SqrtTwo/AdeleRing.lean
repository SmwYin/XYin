/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.ProductFormula
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Adele ring statements for `ℚ(√2)`

This file only names the adelic objects attached to the example and records the
principal adeles coming from the standard generator and fundamental unit.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

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
