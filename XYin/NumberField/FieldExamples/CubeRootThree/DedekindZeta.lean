/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.Regulator
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Dedekind zeta statements for `ℚ(∛3)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

abbrev cubeRootThreeDedekindZeta (s : ℂ) : ℂ :=
  NumberField.dedekindZeta K s

abbrev cubeRootThreeDedekindZetaResidue : ℝ :=
  NumberField.dedekindZeta_residue K

theorem dedekindZeta_residue_pos :
    0 < cubeRootThreeDedekindZetaResidue := by
  sorry

theorem dedekindZeta_residue_class_number_formula :
    cubeRootThreeDedekindZetaResidue =
      (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
          (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          NumberField.Units.regulator K * NumberField.classNumber K) /
        (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|) := by
  sorry

end NumberField.CubeRootThree
