/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.FinitePlaces

/-!
# Finite completions of `ℚ(∛3)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

/-- The completion of `ℚ(∛3)` at the totally ramified finite place above `3`. -/
abbrev CompletionAtThree : Type :=
  heightOneThree.adicCompletion K

theorem completionAtThree_contains_cubeRootThree :
    ∃ x : CompletionAtThree,
      x = NumberField.FinitePlace.embedding (K := K) heightOneThree cubeRootThree := by
  sorry

end NumberField.CubeRootThree
