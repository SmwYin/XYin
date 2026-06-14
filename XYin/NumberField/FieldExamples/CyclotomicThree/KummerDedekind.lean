/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicThree.PrimeSplitting
import Mathlib.NumberTheory.KummerDedekind

/-!
# Kummer-Dedekind viewpoint for `ℚ(ζ₃)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial
open Polynomial

namespace NumberField.CyclotomicThree

/-- The reduction of the third cyclotomic polynomial modulo `p`. -/
abbrev zetaThreePolynomialMod (p : ℕ) : (ZMod p)[X] :=
  X ^ 2 + X + C (1 : ZMod p)

theorem kummerDedekind_splits_iff_one_mod_three
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) ↔ p % 3 = 1 := by
  sorry

theorem kummerDedekind_inert_iff_two_mod_three
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    Irreducible (zetaThreePolynomialMod p) ↔ p % 3 = 2 := by
  sorry

theorem kummerDedekind_ramified_iff_eq_three (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔ p = 3 := by
  sorry

theorem kummerDedekind_splittingType_mod_three
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    ((∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
        Ideal.span {(p : 𝓞 K)} = P * Q) ↔ p % 3 = 1) ∧
      (Irreducible (zetaThreePolynomialMod p) ↔ p % 3 = 2) := by
  sorry

end NumberField.CyclotomicThree
