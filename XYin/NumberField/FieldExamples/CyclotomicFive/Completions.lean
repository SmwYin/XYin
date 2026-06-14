/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicFive.FinitePlaces

/-!
# Finite completions of `ℚ(ζ₅)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

/-- The completion of `ℚ(ζ₅)` at the totally ramified finite place above `5`. -/
abbrev CompletionAtFive : Type :=
  heightOneFive.adicCompletion K

theorem completionAtFive_contains_zeta :
    ∃ x : CompletionAtFive,
      x = NumberField.FinitePlace.embedding (K := K) heightOneFive ζ := by
  sorry

end NumberField.CyclotomicFive
