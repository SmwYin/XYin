/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicThree.Units
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Regulator of `ℚ(ζ₃)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicThree

theorem regulator_eq_one_statement :
    NumberField.Units.regulator K = 1 := by
  sorry

end NumberField.CyclotomicThree
