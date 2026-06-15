/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicEight.Discriminant

/-!
# `ℚ(ζ₈)` Subfields

Subfield structure special to this field.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

noncomputable section

open Module
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicEight

/-- `√2 = ζ + ζ⁻¹` inside `ℚ(ζ₈)`: one has `(ζ + ζ⁷)² = 2`, since `ζ² + ζ⁻² = 0`. -/
theorem sqrt_two_sq : (ζ + ζ ^ 7) ^ 2 = 2 := by
  linear_combination (ζ ^ 10 - ζ ^ 6 + 2 * ζ ^ 4 + ζ ^ 2 - 2) * zeta_pow_four

/-- `i = ζ²` inside `ℚ(ζ₈)`: one has `(ζ²)² = -1`. -/
theorem i_sq : (ζ ^ 2) ^ 2 = -1 := by
  linear_combination zeta_pow_four

/-- `√-2 = ζ - ζ⁻¹` inside `ℚ(ζ₈)`: one has `(ζ - ζ⁷)² = -2`. Together with `sqrt_two_sq`
and `i_sq` this exhibits the three quadratic subfields `ℚ(√2), ℚ(i), ℚ(√-2)` — matching the
three index-`2` subgroups of the Klein-four Galois group. -/
theorem sqrt_neg_two_sq : (ζ - ζ ^ 7) ^ 2 = -2 := by
  linear_combination (ζ ^ 10 - ζ ^ 6 - 2 * ζ ^ 4 + ζ ^ 2 + 2) * zeta_pow_four


end NumberField.CyclotomicEight
