/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.Units
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Regulator of `ℚ(∛3)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

theorem regulator_eq_regOfFamily_fundamentalUnit :
    NumberField.Units.regulator K =
      NumberField.Units.regOfFamily
        (fun _ : Fin (NumberField.Units.rank K) => fundamentalUnit) := by
  sorry

theorem regulator_eq_real_log_statement :
    NumberField.Units.regulator K = |Real.log ((3 : ℝ) ^ ((2 : ℝ) / 3) - 2)| := by
  sorry

end NumberField.CubeRootThree
