/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.PrimeSplitting
import Mathlib.NumberTheory.KummerDedekind

/-!
# Kummer-Dedekind viewpoint for `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open Polynomial

namespace NumberField.SqrtFive

/-- The reduction of the integral generator polynomial `X^2 - X - 1` modulo `p`. -/
abbrev goldenPolynomialMod (p : ℕ) : (ZMod p)[X] :=
  X ^ 2 - X - C (1 : ZMod p)

theorem kummerDedekind_splits_iff_pm_one_mod_five
    (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) ↔ p % 5 = 1 ∨ p % 5 = 4 := by
  sorry

theorem kummerDedekind_inert_iff_two_or_three_mod_five
    (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    Irreducible (goldenPolynomialMod p) ↔ p % 5 = 2 ∨ p % 5 = 3 := by
  sorry

theorem kummerDedekind_ramified_iff_eq_five (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔ p = 5 := by
  sorry

theorem kummerDedekind_splittingType_mod_five
    (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    ((∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
        Ideal.span {(p : 𝓞 K)} = P * Q) ↔ p % 5 = 1 ∨ p % 5 = 4) ∧
      (Irreducible (goldenPolynomialMod p) ↔ p % 5 = 2 ∨ p % 5 = 3) := by
  sorry

end NumberField.SqrtFive
