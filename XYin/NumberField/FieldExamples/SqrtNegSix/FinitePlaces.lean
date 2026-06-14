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
    sorry
  ne_bot := by
    sorry

/-- The finite place over `3`, represented by the non-principal ramified prime. -/
def heightOneThree : HeightOneSpectrum (𝓞 K) where
  asIdeal := primeAboveThree
  isPrime := by
    sorry
  ne_bot := by
    sorry

abbrev vTwo : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk heightOneTwo

abbrev vThree : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk heightOneThree

theorem vTwo_ramificationIdx :
    (Ideal.span {(2 : ℤ)}).ramificationIdx heightOneTwo.asIdeal = 2 := by
  sorry

theorem vThree_ramificationIdx :
    (Ideal.span {(3 : ℤ)}).ramificationIdx heightOneThree.asIdeal = 2 := by
  sorry

theorem vTwo_inertiaDeg :
    (Ideal.span {(2 : ℤ)}).inertiaDeg heightOneTwo.asIdeal = 1 := by
  sorry

theorem vThree_inertiaDeg :
    (Ideal.span {(3 : ℤ)}).inertiaDeg heightOneThree.asIdeal = 1 := by
  sorry

end NumberField.SqrtNegSix
