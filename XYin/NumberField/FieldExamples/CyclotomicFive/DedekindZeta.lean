/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicFive.Regulator
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Dedekind zeta statements for `ℚ(ζ₅)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

abbrev cyclotomicFiveDedekindZeta (s : ℂ) : ℂ :=
  NumberField.dedekindZeta K s

abbrev cyclotomicFiveDedekindZetaResidue : ℝ :=
  NumberField.dedekindZeta_residue K

theorem dedekindZeta_residue_pos :
    0 < cyclotomicFiveDedekindZetaResidue := by
  sorry

theorem dedekindZeta_residue_class_number_formula :
    cyclotomicFiveDedekindZetaResidue =
      (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
          (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          NumberField.Units.regulator K * NumberField.classNumber K) /
        (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|) := by
  sorry

end NumberField.CyclotomicFive
