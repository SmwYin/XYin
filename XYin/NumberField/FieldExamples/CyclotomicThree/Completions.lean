/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicThree.FinitePlaces

/-!
# Finite completions of `ℚ(ζ₃)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicThree

/-- The completion of `ℚ(ζ₃)` at the ramified finite place over `3`. -/
abbrev CompletionAtThree : Type :=
  heightOneThree.adicCompletion K

theorem completionAtThree_contains_zeta :
    ∃ x : CompletionAtThree,
      x = NumberField.FinitePlace.embedding (K := K) heightOneThree ζ := by
  sorry

end NumberField.CyclotomicThree
