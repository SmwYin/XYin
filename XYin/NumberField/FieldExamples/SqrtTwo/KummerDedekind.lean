/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.PrimeSplitting
import Mathlib.NumberTheory.KummerDedekind

/-!
# Kummer-Dedekind viewpoint for `ℚ(√2)`

`PrimeSplitting.lean` is the source of concrete ideal computations.  This file
only records that those computations are exactly what Kummer-Dedekind predicts
from the factorization of `X^2 - 2` modulo rational primes.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open Polynomial

namespace NumberField.SqrtTwo

/-- The reduction of the minimal polynomial `X^2 - 2` modulo `p`. -/
abbrev sqrtTwoPolynomialMod (p : ℕ) : (ZMod p)[X] :=
  X ^ 2 - C (2 : ZMod p)

/-- Modulo `2`, Kummer-Dedekind sees the double root responsible for ramification. -/
theorem sqrtTwoPolynomialMod_two :
    sqrtTwoPolynomialMod 2 = X ^ 2 := by
  rw [sqrtTwoPolynomialMod]
  have h : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  rw [h]
  simp

/-- Modulo `7`, Kummer-Dedekind sees the two roots `±3`. -/
theorem sqrtTwoPolynomialMod_seven_factor :
    sqrtTwoPolynomialMod 7 =
      (X - C (3 : ZMod 7)) * (X + C (3 : ZMod 7)) := by
  rw [sqrtTwoPolynomialMod]
  ring_nf
  have hC : (C (2 : ZMod 7) : (ZMod 7)[X]) = C (3 : ZMod 7) ^ 2 := by
    rw [← map_pow]
    congr
  rw [hC]

/-- Modulo `3`, the polynomial is irreducible, matching the inert prime `(3)`. -/
theorem sqrtTwoPolynomialMod_three_irreducible :
    Irreducible (sqrtTwoPolynomialMod 3) := by
  rw [sqrtTwoPolynomialMod]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, natDegree_X_pow_sub_C]
    norm_num
  · intro x hx
    fin_cases x
    · change Polynomial.eval (0 : ZMod 3) (X ^ 2 - C 2) = 0 at hx
      norm_num at hx
      exact (by decide : (2 : ZMod 3) ≠ 0) hx
    · change Polynomial.eval (1 : ZMod 3) (X ^ 2 - C 2) = 0 at hx
      norm_num at hx
    · change Polynomial.eval (2 : ZMod 3) (X ^ 2 - C 2) = 0 at hx
      norm_num at hx
      exact (by decide : (2 : ZMod 3) ≠ 0) hx

/-- The Kummer-Dedekind root condition is the same as the existing norm-`p` prime condition. -/
theorem exists_root_mod_iff_exists_prime_norm
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ c : ZMod p, c ^ 2 = (2 : ZMod p)) ↔
      ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧
        Ideal.absNorm P = p := by
  calc
    (∃ c : ZMod p, c ^ 2 = (2 : ZMod p)) ↔ p % 8 = 1 ∨ p % 8 = 7 := by
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      simpa [isSquare_iff_exists_sq, eq_comm] using (ZMod.exists_sq_eq_two_iff (p := p) hp2)
    _ ↔ (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧
        Ideal.absNorm P = p) :=
      (exists_prime_norm_iff_pm_one_mod_eight p hp hp2).symm

/-- Kummer-Dedekind's splitting condition agrees with the existing `±1 mod 8` law. -/
theorem kummerDedekind_splits_iff_pm_one_mod_eight
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ c : ZMod p, c ^ 2 = (2 : ZMod p)) ↔ p % 8 = 1 ∨ p % 8 = 7 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  simpa [isSquare_iff_exists_sq, eq_comm] using (ZMod.exists_sq_eq_two_iff (p := p) hp2)

/-- The Kummer-Dedekind prediction at `2` matches the concrete factorization `(2)=(√2)^2`. -/
theorem kummerDedekind_two_matches_concrete_ramification :
    sqrtTwoPolynomialMod 2 = X ^ 2 ∧
      Ideal.span {(2 : 𝓞 K)} = Ideal.span {sqrtTwoInteger} ^ 2 := by
  exact ⟨sqrtTwoPolynomialMod_two, span_two_eq⟩

/-- The Kummer-Dedekind prediction at `7` matches the concrete split ideal factorization. -/
theorem kummerDedekind_seven_matches_concrete_factorization :
    sqrtTwoPolynomialMod 7 =
        (X - C (3 : ZMod 7)) * (X + C (3 : ZMod 7)) ∧
      Ideal.span {(7 : 𝓞 K)} =
        Ideal.span {3 + sqrtTwoInteger} * Ideal.span {3 - sqrtTwoInteger} := by
  exact ⟨sqrtTwoPolynomialMod_seven_factor, span_seven_eq⟩

end NumberField.SqrtTwo
