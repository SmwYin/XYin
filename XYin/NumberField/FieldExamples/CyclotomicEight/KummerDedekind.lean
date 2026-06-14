/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicEight.PrimeSplitting
import Mathlib.NumberTheory.KummerDedekind

/-!
# Kummer-Dedekind viewpoint for `ℚ(ζ₈)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial
open Polynomial

namespace NumberField.CyclotomicEight

/-- The reduction of the eighth cyclotomic polynomial modulo `p`. -/
abbrev zetaEightPolynomialMod (p : ℕ) : (ZMod p)[X] :=
  X ^ 4 + C (1 : ZMod p)

theorem kummerDedekind_splitsCompletely_iff_one_mod_eight
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧
      Ideal.absNorm P = p) ↔ p % 8 = 1 := by
  sorry

theorem kummerDedekind_two_quadratic_primes_iff_not_one_mod_eight
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q ∧ Ideal.absNorm P = p ^ 2 ∧
        Ideal.absNorm Q = p ^ 2) ↔ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
  sorry

theorem kummerDedekind_no_inert_prime (p : ℕ) (hp : p.Prime) :
    ¬ Irreducible (zetaEightPolynomialMod p) := by
  sorry

theorem kummerDedekind_ramified_iff_eq_two (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔ p = 2 := by
  sorry

theorem kummerDedekind_splittingType_mod_eight
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ((∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧
        Ideal.absNorm P = p) ↔ p % 8 = 1) ∧
      ((∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
        Ideal.span {(p : 𝓞 K)} = P * Q ∧ Ideal.absNorm P = p ^ 2 ∧
          Ideal.absNorm Q = p ^ 2) ↔ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7) := by
  sorry

end NumberField.CyclotomicEight
