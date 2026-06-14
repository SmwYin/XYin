/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.PrimeSplitting
import Mathlib.NumberTheory.KummerDedekind

/-!
# Kummer-Dedekind viewpoint for `ℚ(∛3)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial
open Polynomial

namespace NumberField.CubeRootThree

/-- The reduction of the polynomial `X^3 - 3` modulo `p`. -/
abbrev cubeRootThreePolynomialMod (p : ℕ) : (ZMod p)[X] :=
  X ^ 3 - C (3 : ZMod p)

theorem kummerDedekind_degree_one_prime_iff_cube_root_mod_p
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧
      Ideal.absNorm P = p) ↔ ∃ r : ZMod p, r ^ 3 = (3 : ZMod p) := by
  sorry

theorem kummerDedekind_irreducible_iff_no_cube_root_mod_p
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    Irreducible (cubeRootThreePolynomialMod p) ↔
      ¬ ∃ r : ZMod p, r ^ 3 = (3 : ZMod p) := by
  sorry

theorem kummerDedekind_splitsCompletely_iff_three_roots_mod_p
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    (∃ r s t : ZMod p,
      r ≠ s ∧ r ≠ t ∧ s ≠ t ∧
        cubeRootThreePolynomialMod p = (X - C r) * (X - C s) * (X - C t)) ↔
      ∃ P Q R : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ R.IsPrime ∧
        P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ Ideal.span {(p : 𝓞 K)} = P * Q * R := by
  sorry

theorem kummerDedekind_ramified_iff_eq_three (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔ p = 3 := by
  sorry

end NumberField.CubeRootThree
