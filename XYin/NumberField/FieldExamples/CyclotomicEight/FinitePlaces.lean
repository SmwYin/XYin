/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicEight.PrimeSplitting
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Finite places of `ℚ(ζ₈)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial
open IsDedekindDomain
open NumberField.FieldExamples

namespace NumberField.CyclotomicEight

/-- The finite place over `2`, represented by the totally ramified prime `(1 - ζ)`. -/
def heightOneTwo : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {1 - zetaInt}
  isPrime := by
    sorry
  ne_bot := by
    sorry

/-- One degree-two finite place over `3`. -/
def heightOneThreeLeft : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {(3 : 𝓞 K), zetaInt ^ 2 + zetaInt + 2}
  isPrime := by
    sorry
  ne_bot := by
    sorry

/-- The other degree-two finite place over `3`. -/
def heightOneThreeRight : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {(3 : 𝓞 K), zetaInt ^ 2 + 2 * zetaInt + 2}
  isPrime := by
    sorry
  ne_bot := by
    sorry

abbrev vTwo : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk heightOneTwo

theorem vTwo_ramificationIdx :
    (Ideal.span {(2 : ℤ)}).ramificationIdx heightOneTwo.asIdeal = 4 := by
  sorry

theorem vTwo_inertiaDeg :
    (Ideal.span {(2 : ℤ)}).inertiaDeg heightOneTwo.asIdeal = 1 := by
  sorry

theorem vThreeLeft_inertiaDeg :
    (Ideal.span {(3 : ℤ)}).inertiaDeg heightOneThreeLeft.asIdeal = 2 := by
  sorry

theorem vThreeRight_inertiaDeg :
    (Ideal.span {(3 : ℤ)}).inertiaDeg heightOneThreeRight.asIdeal = 2 := by
  sorry

end NumberField.CyclotomicEight
