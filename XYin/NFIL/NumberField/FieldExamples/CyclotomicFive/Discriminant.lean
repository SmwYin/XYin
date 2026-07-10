/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NFIL.NumberField.FieldExamples.CyclotomicFive.RingOfIntegers

/-!
# `ℚ(ζ₅)` Discriminant

Discriminant computations and immediate discriminant consequences.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Discriminant
-/

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicFive

/-- The number-field discriminant of `ℚ(ζ₅)` is `125 = 5³` (for an odd prime `p` the
discriminant of `ℚ(ζ_p)` is `(-1)^((p-1)/2) p^(p-2)`). In particular `5` is the only
ramified prime, cf. `ramified_iff_eq_five`. -/
theorem numberField_discr_eq : NumberField.discr K = (125 : ℤ) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [IsCyclotomicExtension.Rat.discr_prime 5 K]
  norm_num

/-- The discriminant of the explicit integral basis `1, ζ, ζ², ζ³` is `125`. -/
theorem concreteIntegralBasis_discr :
    Algebra.discr ℤ concreteIntegralBasis = (125 : ℤ) := by
  simpa [numberField_discr_eq] using
    (NumberField.discr_eq_discr (K := K) concreteIntegralBasis)

/-- The discriminant of mathlib's canonical field integral basis is `125`. -/
theorem integralBasis_discr :
    Algebra.discr ℚ (NumberField.integralBasis K) = (125 : ℚ) := by
  have h := NumberField.coe_discr K
  rw [numberField_discr_eq] at h
  simpa using h.symm


end NumberField.CyclotomicFive
