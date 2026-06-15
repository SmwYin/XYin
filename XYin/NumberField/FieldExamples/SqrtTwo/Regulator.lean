/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.Units
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Regulator of `ℚ(√2)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtTwo

theorem regulator_eq_log_one_add_sqrtTwo :
    NumberField.Units.regulator K = Real.log (1 + Real.sqrt 2) := by
  exact regulator_eq

end NumberField.SqrtTwo
