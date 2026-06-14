/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.PrimeSplitting
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Finite places of `ℚ(√2)`

The concrete prime ideals from `PrimeSplitting.lean` are repackaged here as
height-one primes / finite places.  This avoids re-proving the splitting facts
while making the finite-place API visible in the example.
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

theorem vTwo_ramificationIdx :
    (Ideal.span {(2 : ℤ)}).ramificationIdx vTwo.asIdeal = 2 := by
  exact ramificationIdx_span_sqrtTwoInteger

theorem vTwo_inertiaDeg :
    (Ideal.span {(2 : ℤ)}).inertiaDeg vTwo.asIdeal = 1 := by
  exact inertiaDeg_span_sqrtTwoInteger

theorem vThree_ramificationIdx :
    (Ideal.span {(3 : ℤ)}).ramificationIdx vThree.asIdeal = 1 := by
  exact ramificationIdx_span_three

theorem vThree_inertiaDeg :
    (Ideal.span {(3 : ℤ)}).inertiaDeg vThree.asIdeal = 2 := by
  exact inertiaDeg_span_three

theorem vSevenPlus_ramificationIdx :
    (Ideal.span {(7 : ℤ)}).ramificationIdx vSevenPlus.asIdeal = 1 := by
  exact ramificationIdx_span_three_add_sqrtTwo

theorem vSevenMinus_ramificationIdx :
    (Ideal.span {(7 : ℤ)}).ramificationIdx vSevenMinus.asIdeal = 1 := by
  exact ramificationIdx_span_three_sub_sqrtTwo

theorem vSevenPlus_inertiaDeg :
    (Ideal.span {(7 : ℤ)}).inertiaDeg vSevenPlus.asIdeal = 1 := by
  exact inertiaDeg_span_three_add_sqrtTwo

theorem vSevenMinus_inertiaDeg :
    (Ideal.span {(7 : ℤ)}).inertiaDeg vSevenMinus.asIdeal = 1 := by
  exact inertiaDeg_span_three_sub_sqrtTwo

end NumberField.SqrtTwo
