/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.FinitePlaces

/-!
# Finite completions of `ℚ(√-6)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

abbrev CompletionAtTwo : Type :=
  heightOneTwo.adicCompletion K

abbrev CompletionAtThree : Type :=
  heightOneThree.adicCompletion K

theorem completionAtTwo_contains_theta :
    ∃ x : CompletionAtTwo,
      x = NumberField.FinitePlace.embedding (K := K) heightOneTwo θ := by
  sorry

theorem completionAtThree_contains_theta :
    ∃ x : CompletionAtThree,
      x = NumberField.FinitePlace.embedding (K := K) heightOneThree θ := by
  sorry

end NumberField.SqrtNegSix
