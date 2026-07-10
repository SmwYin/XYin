/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NFIL.NumberField.FieldExamples.CyclotomicEight.Units

/-!
# `ℚ(ζ₈)` Euclidean

Euclidean or non-Euclidean properties and their arithmetic consequences.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Euclidean
-/

noncomputable section

open Module
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicEight

/-- `ℚ(ζ₈)` is norm-Euclidean. -/
theorem normEuclidean (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry


end NumberField.CyclotomicEight
