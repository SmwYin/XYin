/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicFive.PrimeSplitting
import Mathlib.NumberTheory.KummerDedekind

/-!
# Kummer-Dedekind viewpoint for `ℚ(ζ₅)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial
open Polynomial

namespace NumberField.CyclotomicFive

/-- The reduction of the fifth cyclotomic polynomial modulo `p`. -/
abbrev zetaFivePolynomialMod (p : ℕ) : (ZMod p)[X] :=
  X ^ 4 + X ^ 3 + X ^ 2 + X + C (1 : ZMod p)

theorem kummerDedekind_splitsCompletely_iff_one_mod_five
    (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧
      Ideal.absNorm P = p) ↔ p % 5 = 1 := by
  sorry

theorem kummerDedekind_two_quadratic_primes_iff_four_mod_five
    (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q ∧ Ideal.absNorm P = p ^ 2 ∧
        Ideal.absNorm Q = p ^ 2) ↔ p % 5 = 4 := by
  sorry

theorem kummerDedekind_inert_iff_two_or_three_mod_five
    (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    Irreducible (zetaFivePolynomialMod p) ↔ p % 5 = 2 ∨ p % 5 = 3 := by
  sorry

theorem kummerDedekind_ramified_iff_eq_five (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔ p = 5 := by
  sorry

theorem kummerDedekind_splittingType_mod_five
    (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    ((∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧
        Ideal.absNorm P = p) ↔ p % 5 = 1) ∧
      ((∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
        Ideal.span {(p : 𝓞 K)} = P * Q ∧ Ideal.absNorm P = p ^ 2 ∧
          Ideal.absNorm Q = p ^ 2) ↔ p % 5 = 4) ∧
      (Irreducible (zetaFivePolynomialMod p) ↔ p % 5 = 2 ∨ p % 5 = 3) := by
  sorry

end NumberField.CyclotomicFive
