/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicEight.FinitePlaces

/-!
# Finite completions of `ℚ(ζ₈)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

/-- The completion of `ℚ(ζ₈)` at the totally ramified finite place above `2`. -/
abbrev CompletionAtTwo : Type :=
  heightOneTwo.adicCompletion K

theorem completionAtTwo_contains_zeta :
    ∃ x : CompletionAtTwo,
      x = NumberField.FinitePlace.embedding (K := K) heightOneTwo ζ := by
  sorry

end NumberField.CyclotomicEight
