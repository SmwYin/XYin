/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.PrimeSplitting
import Mathlib.NumberTheory.KummerDedekind

/-!
# Kummer-Dedekind viewpoint for `ℚ(√-6)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open Polynomial

namespace NumberField.SqrtNegSix

/-- The reduction of the integral generator polynomial `X^2 + 6` modulo `p`. -/
abbrev sqrtNegSixPolynomialMod (p : ℕ) : (ZMod p)[X] :=
  X ^ 2 + C (6 : ZMod p)

theorem kummerDedekind_splits_iff_mod_twentyfour
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) ↔
        p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 := by
  exact splits_iff_mod_twentyfour p hp hp2 hp3

theorem kummerDedekind_inert_iff_mod_twentyfour
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Irreducible (sqrtNegSixPolynomialMod p) ↔
      p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := by
  sorry

theorem kummerDedekind_ramified_iff_two_or_three (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔
      p = 2 ∨ p = 3 := by
  exact ramified_iff p hp

theorem kummerDedekind_splittingType_mod_twentyfour
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ((∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
        Ideal.span {(p : 𝓞 K)} = P * Q) ↔
        p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11) ∧
      (Irreducible (sqrtNegSixPolynomialMod p) ↔
        p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23) := by
  exact ⟨kummerDedekind_splits_iff_mod_twentyfour p hp hp2 hp3,
    kummerDedekind_inert_iff_mod_twentyfour p hp hp2 hp3⟩

end NumberField.SqrtNegSix
