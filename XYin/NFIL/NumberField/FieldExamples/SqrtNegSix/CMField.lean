/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NFIL.NumberField.FieldExamples.SqrtNegSix.Embeddings

/-!
# `ℚ(√-6)` CMField

CM-field structure and related statements.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

theorem isCMField : NumberField.IsCMField K := by
  haveI : NumberField.IsTotallyComplex K := isTotallyComplex
  exact NumberField.IsCMField.ofCMExtension ℚ K

theorem cmField_isTotallyComplex : NumberField.IsTotallyComplex K := by
  exact isTotallyComplex

theorem cmField_quadratic_over_maximalRealSubfield :
    Algebra.IsQuadraticExtension (NumberField.maximalRealSubfield K) K := by
  haveI : NumberField.IsCMField K := isCMField
  exact NumberField.IsCMField.isQuadraticExtension K

theorem cmField_unitsRank_eq_maximalRealSubfield :
    NumberField.Units.rank (NumberField.maximalRealSubfield K) =
      NumberField.Units.rank K := by
  haveI : NumberField.IsCMField K := isCMField
  exact NumberField.IsCMField.units_rank_eq_units_rank K

end NumberField.SqrtNegSix
