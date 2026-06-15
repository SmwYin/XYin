/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.Units
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Regulator of `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

theorem regulator_eq_log_goldenRatio :
    NumberField.Units.regulator K = Real.log ((1 + Real.sqrt 5) / 2) := by
  exact regulator_eq

end NumberField.SqrtFive
