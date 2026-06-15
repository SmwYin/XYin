/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.Regulator
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Dedekind zeta statements for `ℚ(√-6)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

abbrev sqrtNegSixDedekindZeta (s : ℂ) : ℂ :=
  NumberField.dedekindZeta K s

abbrev sqrtNegSixDedekindZetaResidue : ℝ :=
  NumberField.dedekindZeta_residue K

theorem dedekindZeta_residue_pos :
    0 < sqrtNegSixDedekindZetaResidue := by
  exact NumberField.dedekindZeta_residue_pos K

theorem dedekindZeta_residue_class_number_formula :
    sqrtNegSixDedekindZetaResidue =
      (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
          (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          NumberField.Units.regulator K * NumberField.classNumber K) /
        (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|) := by
  exact NumberField.dedekindZeta_residue_def K

end NumberField.SqrtNegSix
