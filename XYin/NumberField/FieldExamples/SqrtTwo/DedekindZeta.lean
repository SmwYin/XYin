/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.Regulator
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Dedekind zeta statements for `ℚ(√2)`

This file gives statement-level anchors for the Dedekind zeta function and its residue.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open NumberField

namespace NumberField.SqrtTwo

/-- The Dedekind zeta function of `ℚ(√2)`. -/
abbrev sqrtTwoDedekindZeta (s : ℂ) : ℂ :=
  NumberField.dedekindZeta K s

/-- The class-number-formula residue for `ℚ(√2)`. -/
abbrev sqrtTwoDedekindZetaResidue : ℝ :=
  NumberField.dedekindZeta_residue K

theorem dedekindZeta_residue_pos :
    0 < sqrtTwoDedekindZetaResidue := by
  sorry

theorem dedekindZeta_residue_class_number_formula :
    sqrtTwoDedekindZetaResidue =
      (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
          (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          NumberField.Units.regulator K * NumberField.classNumber K) /
        (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|) := by
  sorry

end NumberField.SqrtTwo
