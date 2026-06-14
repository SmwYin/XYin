/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicThree.PrimeSplitting
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Finite places of `ℚ(ζ₃)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial
open IsDedekindDomain

namespace NumberField.CyclotomicThree

/-- The finite place over `3`, represented by the ramified prime `(ζ - 1)`. -/
def heightOneThree : HeightOneSpectrum (𝓞 K) where
  asIdeal := Ideal.span {zetaInt - 1}
  isPrime := by
    sorry
  ne_bot := by
    sorry

abbrev vThree : NumberField.FinitePlace K :=
  NumberField.FinitePlace.mk heightOneThree

theorem vThree_ramificationIdx :
    (Ideal.span {(3 : ℤ)}).ramificationIdx heightOneThree.asIdeal = 2 := by
  sorry

theorem vThree_inertiaDeg :
    (Ideal.span {(3 : ℤ)}).inertiaDeg heightOneThree.asIdeal = 1 := by
  sorry

end NumberField.CyclotomicThree
