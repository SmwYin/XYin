/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicEight.Units
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Regulator of `ℚ(ζ₈)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

theorem regulator_eq_two_mul_log_one_add_sqrtTwo :
    NumberField.Units.regulator K = 2 * Real.log (1 + Real.sqrt 2) := by
  sorry

end NumberField.CyclotomicEight
