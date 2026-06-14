/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.FinitePlaces

/-!
# Finite completions of `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

/-- The completion of `ℚ(√5)` at the ramified finite place over `5`. -/
abbrev CompletionAtFive : Type :=
  heightOneFive.adicCompletion K

theorem completionAtFive_contains_goldenRoot :
    ∃ x : CompletionAtFive,
      x = NumberField.FinitePlace.embedding (K := K) heightOneFive goldenRoot := by
  sorry

end NumberField.SqrtFive
