/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.PrimeSplitting
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

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

/-- The generator `√2` generates the full ring of integers, so Kummer-Dedekind has no
exceptional conductor primes for this integral primitive element. -/
theorem sqrtTwoInteger_exponent_eq_one :
    RingOfIntegers.exponent sqrtTwoInteger = 1 := by
  rw [RingOfIntegers.exponent_eq_one_iff]
  exact sqrtTwoInteger_adjoin_eq_top

/-- Every rational prime is coprime to the Kummer-Dedekind exponent of `√2`. -/
theorem sqrtTwoInteger_exponent_not_dvd (p : ℕ) [Fact p.Prime] :
    ¬ p ∣ RingOfIntegers.exponent sqrtTwoInteger := by
  rw [sqrtTwoInteger_exponent_eq_one]
  exact (Fact.out : p.Prime).not_dvd_one

/-- Kummer-Dedekind computes the residual degree from the degree of a mod-`p` factor. -/
theorem sqrtTwo_kummerDedekind_inertiaDeg
    {p : ℕ} [Fact p.Prime] {Q : (ZMod p)[X]}
    (hQ : Q ∈ RingOfIntegers.monicFactorsMod sqrtTwoInteger p) :
    Ideal.inertiaDeg (Ideal.span {(p : ℤ)})
        ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
          (θ := sqrtTwoInteger) (sqrtTwoInteger_exponent_not_dvd p)).symm ⟨Q, hQ⟩ :
          Ideal (𝓞 K)) = Q.natDegree := by
  exact NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (θ := sqrtTwoInteger) (sqrtTwoInteger_exponent_not_dvd p) hQ

/-- Kummer-Dedekind computes the ramification index from the multiplicity of a mod-`p` factor. -/
theorem sqrtTwo_kummerDedekind_ramificationIdx
    {p : ℕ} [Fact p.Prime] {Q : (ZMod p)[X]}
    (hQ : Q ∈ RingOfIntegers.monicFactorsMod sqrtTwoInteger p) :
    Ideal.ramificationIdx (Ideal.span {(p : ℤ)})
        ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
          (θ := sqrtTwoInteger) (sqrtTwoInteger_exponent_not_dvd p)).symm ⟨Q, hQ⟩ :
          Ideal (𝓞 K)) = multiplicity Q (sqrtTwoPolynomialMod p) := by
  rw [NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (θ := sqrtTwoInteger) (sqrtTwoInteger_exponent_not_dvd p) hQ]
  congr 1
  rw [sqrtTwoInteger_minpoly, sqrtTwoIntegerPolynomial, sqrtTwoPolynomialMod]
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  congr 2
  norm_num

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

/-- The inert cases are the complementary odd residue classes modulo `8`. -/
theorem kummerDedekind_inert_iff_three_or_five_mod_eight
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Irreducible (sqrtTwoPolynomialMod p) ↔ p % 8 = 3 ∨ p % 8 = 5 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hdeg : (sqrtTwoPolynomialMod p).natDegree = 2 := by
    rw [sqrtTwoPolynomialMod, natDegree_X_pow_sub_C]
  have hroot_iff (c : ZMod p) :
      (sqrtTwoPolynomialMod p).IsRoot c ↔ c ^ 2 = (2 : ZMod p) := by
    simpa [sqrtTwoPolynomialMod, pow_two] using
      (sub_eq_zero : c * c - (2 : ZMod p) = 0 ↔ c * c = (2 : ZMod p))
  have hirr_iff_not_sq : Irreducible (sqrtTwoPolynomialMod p) ↔
      ¬ ∃ c : ZMod p, c ^ 2 = (2 : ZMod p) := by
    constructor
    · intro hirr hs
      obtain ⟨c, hc⟩ := hs
      exact hirr.not_isRoot_of_natDegree_ne_one (by rw [hdeg]; norm_num)
        ((hroot_iff c).2 hc)
    · intro hnot
      apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      · rw [Finset.mem_Icc, hdeg]
        norm_num
      · intro c hc
        exact hnot ⟨c, (hroot_iff c).1 hc⟩
  have hsq_iff : (∃ c : ZMod p, c ^ 2 = (2 : ZMod p)) ↔
      p % 8 = 1 ∨ p % 8 = 7 := by
    simpa [isSquare_iff_exists_sq, eq_comm] using
      (ZMod.exists_sq_eq_two_iff (p := p) hp2)
  have hodd : p % 2 = 1 := by
    simpa [Nat.odd_iff] using hp.odd_of_ne_two hp2
  have hmod2 : p % 8 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 8), hodd]
  have hnot_pm_one_iff :
      ¬ (p % 8 = 1 ∨ p % 8 = 7) ↔ p % 8 = 3 ∨ p % 8 = 5 := by
    constructor
    · intro h
      have hlt : p % 8 < 8 := Nat.mod_lt p (by norm_num)
      interval_cases hcase : p % 8 <;> omega
    · intro h hpm
      omega
  calc
    Irreducible (sqrtTwoPolynomialMod p) ↔
        ¬ ∃ c : ZMod p, c ^ 2 = (2 : ZMod p) := hirr_iff_not_sq
    _ ↔ ¬ (p % 8 = 1 ∨ p % 8 = 7) := not_congr hsq_iff
    _ ↔ p % 8 = 3 ∨ p % 8 = 5 := hnot_pm_one_iff

/-- Complete Kummer-Dedekind splitting type for unramified rational primes in `ℚ(√2)`. -/
theorem kummerDedekind_splittingType_mod_eight
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ((∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
        Ideal.span {(p : 𝓞 K)} = P * Q) ↔ p % 8 = 1 ∨ p % 8 = 7) ∧
      (Irreducible (sqrtTwoPolynomialMod p) ↔ p % 8 = 3 ∨ p % 8 = 5) := by
  exact ⟨splits_iff_pm_one_mod_eight p hp hp2,
    kummerDedekind_inert_iff_three_or_five_mod_eight p hp hp2⟩

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
