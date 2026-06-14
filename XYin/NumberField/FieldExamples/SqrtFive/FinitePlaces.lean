/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.PrimeSplitting
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Finite places of `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open IsDedekindDomain
open NumberField.FieldExamples

namespace NumberField.SqrtFive

/-- The finite place over `5`, represented by the ramified prime `(√5)`. -/
def heightOneFive : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {sqrtFiveIntO}
  isPrime := by
    sorry
  ne_bot := by
    sorry

/-- The finite absolute value associated to the ramified place over `5`. -/
abbrev vFive : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk heightOneFive

theorem vFive_ramificationIdx :
    (Ideal.span {(5 : ℤ)}).ramificationIdx heightOneFive.asIdeal = 2 := by
  sorry

theorem vFive_inertiaDeg :
    (Ideal.span {(5 : ℤ)}).inertiaDeg heightOneFive.asIdeal = 1 := by
  sorry

end NumberField.SqrtFive
