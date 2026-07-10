/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NFIL.NumberField.FieldExamples.CyclotomicThree.RingOfIntegers

/-!
# `ℚ(ζ₃)` Discriminant

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

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial

namespace NumberField.CyclotomicThree

/-- The number-field discriminant of `ℚ(ζ₃) = ℚ(√-3)` is `-3`: the quadratic field of
smallest absolute discriminant. In particular `3` is the only ramified prime, cf.
`ramified_iff_eq_three`. -/
theorem numberField_discr_eq : NumberField.discr K = -3 := by
  rw [IsCyclotomicExtension.Rat.discr_prime 3 K]
  norm_num

theorem zetaExplicitIntegralBasis_discr :
    Algebra.discr ℤ zetaExplicitIntegralBasis = (-3 : ℤ) := by
  calc
    Algebra.discr ℤ zetaExplicitIntegralBasis = NumberField.discr K := by
      simpa using (NumberField.discr_eq_discr (K := K) zetaExplicitIntegralBasis)
    _ = -3 := by
      rw [IsCyclotomicExtension.Rat.discr_prime 3 K]
      norm_num

/--
`NumberField.coe_discr` says `(NumberField.discr K : ℚ) = Algebra.discr ℚ (integralBasis K)`.
This bridges the integer-valued field discriminant to the concrete `Algebra.discr ℚ`
computed from mathlib's canonical `ℚ`-basis of `K`.
-/
theorem integralBasis_discr :
    Algebra.discr ℚ (NumberField.integralBasis K) = (-3 : ℚ) := by
  have h := NumberField.coe_discr K
  rw [show NumberField.discr K = -3 from by
        rw [IsCyclotomicExtension.Rat.discr_prime 3 K]; norm_num] at h
  simpa using h.symm

/-
`Algebra.discr_of_matrix_mulVec`: replacing basis `b` by `Pb` scales the discriminant by `det(P)²`.
This is the key formula behind the fact that all `ℤ`-bases of `𝓞 K` yield the same
`NumberField.discr K`: change-of-basis matrices between them are unimodular (`det = ±1`),
so `det(P)² = 1` and the discriminant is preserved.
-/
example
    (P : Matrix (Free.ChooseBasisIndex ℤ (𝓞 K)) (Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ) :
    Algebra.discr ℚ (Matrix.mulVec (P.map (algebraMap ℚ K)) (NumberField.integralBasis K)) =
      P.det ^ 2 * Algebra.discr ℚ (NumberField.integralBasis K) :=
  Algebra.discr_of_matrix_mulVec _ _

/- Concretely: a unimodular change of basis preserves the discriminant `-3`. -/
example
    (P : Matrix (Free.ChooseBasisIndex ℤ (𝓞 K)) (Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ)
    (hdet : P.det = 1 ∨ P.det = -1) :
    Algebra.discr ℚ (Matrix.mulVec (P.map (algebraMap ℚ K)) (NumberField.integralBasis K)) =
        (-3 : ℚ) := by
  have hdisc :
      Algebra.discr ℚ (Matrix.mulVec (P.map (algebraMap ℚ K)) (NumberField.integralBasis K)) =
        P.det ^ 2 * Algebra.discr ℚ (NumberField.integralBasis K) :=
    Algebra.discr_of_matrix_mulVec _ _
  rw [hdisc, integralBasis_discr]
  rcases hdet with h | h <;> simp [h]


end NumberField.CyclotomicThree
