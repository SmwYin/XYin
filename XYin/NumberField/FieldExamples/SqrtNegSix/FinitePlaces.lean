/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.PrimeSplitting
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Finite places of `ℚ(√-6)`
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
