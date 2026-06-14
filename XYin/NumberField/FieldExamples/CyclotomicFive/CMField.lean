/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicFive.Embeddings
import Mathlib.NumberTheory.NumberField.CMField

/-!
# CM-field structure for `ℚ(ζ₅)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

theorem isCMField : NumberField.IsCMField K := by
  sorry

theorem cmField_isTotallyComplex : NumberField.IsTotallyComplex K := by
  sorry

theorem cmField_quadratic_over_maximalRealSubfield :
    Algebra.IsQuadraticExtension (NumberField.maximalRealSubfield K) K := by
  sorry

theorem cmField_unitsRank_eq_maximalRealSubfield :
    NumberField.Units.rank (NumberField.maximalRealSubfield K) =
      NumberField.Units.rank K := by
  sorry

end NumberField.CyclotomicFive
