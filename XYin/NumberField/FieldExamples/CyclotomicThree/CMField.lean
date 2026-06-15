/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicThree.Embeddings

/-!
# `ℚ(ζ₃)` CMField

CM-field structure and related statements.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicThree

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

end NumberField.CyclotomicThree
