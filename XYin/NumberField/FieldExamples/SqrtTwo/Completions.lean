/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.FinitePlaces

/-!
# Finite completions of `ℚ(√2)`

This file records completion-level statements attached to the concrete finite
places from `FinitePlaces.lean`.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtTwo

/-- The completion of `ℚ(√2)` at the ramified finite place over `2`. -/
abbrev CompletionAtTwo : Type :=
  vTwo.adicCompletion K

/-- The completion of `ℚ(√2)` at the inert finite place over `3`. -/
abbrev CompletionAtThree : Type :=
  vThree.adicCompletion K

/-- One completion of `ℚ(√2)` at a split finite place over `7`. -/
abbrev CompletionAtSevenPlus : Type :=
  vSevenPlus.adicCompletion K

/-- The other completion of `ℚ(√2)` at a split finite place over `7`. -/
abbrev CompletionAtSevenMinus : Type :=
  vSevenMinus.adicCompletion K

/-- The canonical image of `√2` in the ramified `2`-adic completion. -/
theorem completionAtTwo_contains_sqrtTwo :
    ∃ x : CompletionAtTwo,
      x = NumberField.FinitePlace.embedding (K := K) vTwo sqrtTwoRoot := by
  exact ⟨NumberField.FinitePlace.embedding (K := K) vTwo sqrtTwoRoot, rfl⟩

/-- The `2`-adic completion remembers the ramification index `2`. -/
theorem completionAtTwo_ramificationIdx :
    (Ideal.span {(2 : ℤ)}).ramificationIdx vTwo.asIdeal = 2 := by
  exact vTwo_ramificationIdx

/-- The `3`-adic completion is the inert local factor, with residue degree `2`. -/
theorem completionAtThree_inertiaDeg :
    (Ideal.span {(3 : ℤ)}).inertiaDeg vThree.asIdeal = 2 := by
  exact vThree_inertiaDeg

/-- The two completions over `7` both have residue degree `1`. -/
theorem completionAtSeven_inertiaDegs :
    (Ideal.span {(7 : ℤ)}).inertiaDeg vSevenPlus.asIdeal = 1 ∧
      (Ideal.span {(7 : ℤ)}).inertiaDeg vSevenMinus.asIdeal = 1 := by
  exact ⟨vSevenPlus_inertiaDeg, vSevenMinus_inertiaDeg⟩

end NumberField.SqrtTwo
