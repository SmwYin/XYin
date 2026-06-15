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
    exact isPrime_span_sqrtFiveIntO
  ne_bot := by
    intro hbot
    have hzero : sqrtFiveIntO = 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hbot
    have hsqrt : sqrtFiveIntO ^ 2 = (5 : 𝓞 K) := by
      apply Subtype.ext
      change (2 * goldenRoot - 1) ^ 2 = (5 : K)
      exact sqrtFiveRoot_sq
    rw [hzero] at hsqrt
    norm_num at hsqrt

/-- The finite absolute value associated to the ramified place over `5`. -/
abbrev vFive : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk heightOneFive

theorem vFive_ramificationIdx :
    (Ideal.span {(5 : ℤ)}).ramificationIdx heightOneFive.asIdeal = 2 := by
  exact ramificationIdx_span_sqrtFiveIntO

theorem vFive_inertiaDeg :
    (Ideal.span {(5 : ℤ)}).inertiaDeg heightOneFive.asIdeal = 1 := by
  exact inertiaDeg_span_sqrtFiveIntO

end NumberField.SqrtFive
