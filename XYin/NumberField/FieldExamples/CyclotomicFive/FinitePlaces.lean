/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicFive.PrimeSplitting
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Finite places of `ℚ(ζ₅)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial
open IsDedekindDomain
open NumberField.FieldExamples

namespace NumberField.CyclotomicFive

/-- The finite place over `5`, represented by the totally ramified prime `(1 - ζ)`. -/
def heightOneFive : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {1 - zetaInt}
  isPrime := by
    sorry
  ne_bot := by
    sorry

abbrev vFive : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk heightOneFive

theorem vFive_ramificationIdx :
    (Ideal.span {(5 : ℤ)}).ramificationIdx heightOneFive.asIdeal = 4 := by
  sorry

theorem vFive_inertiaDeg :
    (Ideal.span {(5 : ℤ)}).inertiaDeg heightOneFive.asIdeal = 1 := by
  sorry

end NumberField.CyclotomicFive
