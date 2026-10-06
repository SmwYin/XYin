/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The numerical lemmas for Janusz reciprocity

The first source subtree is Janusz V.5.2, printed159–160. It constructs a
prime at which a prescribed integer has prime-power order. The separate
two-adic calculation retains the source hypothesis that the exponent is at
least two. These contracts are proof obligations, not completed proofs.
-/

open Finset

namespace Cox.ClassFieldTheory

namespace ResidueUnits

/-- V.5.2, printed159: every term is at least one and the term of degree one is larger. -/
theorem geom_sum_gt_length (X q : ℕ) (hX : 2 ≤ X) (hq : 2 ≤ q) :
    q < ∑ i ∈ range q, X ^ i := by
  have h1 : ∀ i ∈ range q, 1 ≤ X ^ i := fun i _ => Nat.one_le_pow _ _ (by omega)
  have h2 : 1 < X ^ 1 := by simpa using hX
  calc q = ∑ _i ∈ range q, 1 := by simp
    _ < ∑ i ∈ range q, X ^ i :=
      Finset.sum_lt_sum h1 ⟨1, Finset.mem_range.mpr (by omega), h2⟩

/-- V.5.2, printed159: a prime dividing both the geometric sum and its denominator is q. -/
theorem prime_eq_of_dvd_geom_sum_of_dvd_sub (X q p : ℕ) (hX : 1 ≤ X)
    (hq : q.Prime) (hp : p.Prime) (hg : p ∣ ∑ i ∈ range q, X ^ i)
    (hsub : p ∣ X - 1) : p = q := by
  have hsubZ : (p : ℤ) ∣ (X : ℤ) - 1 := by
    have := Int.natCast_dvd_natCast.mpr hsub
    rwa [Nat.cast_sub hX, Nat.cast_one] at this
  have hgZ : (p : ℤ) ∣ ∑ i ∈ range q, (X : ℤ) ^ i * 1 ^ (q - 1 - i) := by
    have := Int.natCast_dvd_natCast.mpr hg
    simpa using this
  have hpq : (p : ℤ) ∣ (q : ℤ) * 1 ^ (q - 1) := (dvd_geom_sum₂_iff_of_dvd_sub hsubZ).mp hgZ
  rw [one_pow, mul_one] at hpq
  exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (Int.natCast_dvd_natCast.mp hpq)

/-- V.5.2, printed159: the odd-index geometric sum is q modulo q². -/
theorem odd_sq_not_dvd_geom_sum (X q : ℕ) (hX : 1 ≤ X) (hq : 1 < q)
    (hodd : Odd q) (hsub : q ∣ X - 1) : ¬ q ^ 2 ∣ ∑ i ∈ range q, X ^ i := by
  intro h
  obtain ⟨b, hb⟩ := hsub
  have hXeq : X = 1 + q * b := by omega
  have key := odd_sq_dvd_geom_sum₂_sub (R := ℤ) (a := 1) (b := (b : ℤ)) hodd
  simp only [one_pow, mul_one] at key
  have hg : ((q : ℤ)) ^ 2 ∣ ∑ i ∈ range q, ((1 : ℤ) + q * b) ^ i := by
    have := Int.natCast_dvd_natCast.mpr h
    rw [hXeq] at this
    push_cast at this
    exact this
  have hq2 : (q : ℤ) ^ 2 ∣ (q : ℤ) := by
    have := dvd_sub hg key
    simpa using this
  have hq2' : q ^ 2 ∣ q := by exact_mod_cast hq2
  have := Nat.le_of_dvd (by omega) hq2'
  nlinarith

/-- V.5.2, printed159–160: the square of an odd integer is one modulo four. -/
theorem odd_sq_add_one_mod_four (a : ℕ) (ha : Odd a) : (a ^ 2 + 1) % 4 = 2 := by
  obtain ⟨k, rfl⟩ := ha
  have h : (2 * k + 1) ^ 2 + 1 = 2 + 4 * (k ^ 2 + k) := by ring
  rw [h, Nat.add_mul_mod_self_left]

/-- V.5.2, printed159–160: positive depth makes the exponent 2^s even. -/
theorem two_sq_not_dvd_geom_sum_pow (a s : ℕ) (ha : Odd a) (hs : 1 ≤ s) :
    ¬ 2 ^ 2 ∣ ∑ i ∈ range 2, (a ^ (2 ^ s)) ^ i := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hb : Odd (a ^ (2 ^ t)) := ha.pow
  have heq : ∑ i ∈ range 2, (a ^ (2 ^ (t + 1))) ^ i = (a ^ (2 ^ t)) ^ 2 + 1 := by
    simp [Finset.sum_range_succ, pow_succ, pow_mul]
    ring
  rw [heq, Nat.dvd_iff_mod_eq_zero, show (2 : ℕ) ^ 2 = 4 by norm_num,
    odd_sq_add_one_mod_four _ hb]
  norm_num

/-- V.5.2, printed159: a number larger than q with no q² factor has another prime factor. -/
theorem exists_prime_ne_of_sq_not_dvd (n q : ℕ) (hq : 2 ≤ q) (hqn : q < n)
    (hsq : ¬ q ^ 2 ∣ n) : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p ≠ q := by
  by_cases hqd : q ∣ n
  · obtain ⟨k, rfl⟩ := hqd
    have hk : k ≠ 1 := by
      rintro rfl
      omega
    obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk
    refine ⟨p, hp, dvd_mul_of_dvd_right hpk q, ?_⟩
    rintro rfl
    exact hsq (by rw [pow_two]; exact mul_dvd_mul_left p hpk)
  · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    exact ⟨p, hp, hpn, fun h => hqd (h ▸ hpn)⟩

/-- V.5.2, printed159–160: a suitable prime divides the numerator factor but not its denominator. -/
theorem exists_prime_dvd_geom_sum_not_dvd_sub (a q r : ℕ) (ha : 2 ≤ a)
    (hq : q.Prime) (hr : 2 ≤ r) :
    ∃ p : ℕ, p.Prime ∧ p ∣ ∑ i ∈ range q, (a ^ (q ^ (r - 1))) ^ i ∧
      ¬ p ∣ a ^ (q ^ (r - 1)) - 1 := by
  set X := a ^ (q ^ (r - 1)) with hXdef
  have hX2 : 2 ≤ X := le_trans ha (Nat.le_self_pow (pow_pos hq.pos _).ne' a)
  have hgt := geom_sum_gt_length X q hX2 hq.two_le
  obtain ⟨p, hp, hpg⟩ :=
    Nat.exists_prime_and_dvd (show (∑ i ∈ range q, X ^ i) ≠ 1 by have := hq.two_le; omega)
  by_cases hpX : p ∣ X - 1
  · have hpq := prime_eq_of_dvd_geom_sum_of_dvd_sub X q p (by omega) hq hp hpg hpX
    subst hpq
    have hsq : ¬ p ^ 2 ∣ ∑ i ∈ range p, X ^ i := by
      rcases hp.eq_two_or_odd' with h2 | hodd
      · subst h2
        have hodd_a : Odd a := by
          by_contra hne
          have hev : Even a := Nat.not_odd_iff_even.mp hne
          have hXev : Even X := Nat.even_pow.mpr ⟨hev, (pow_pos (by norm_num) _).ne'⟩
          have h2X : 2 ∣ X := hXev.two_dvd
          have h21 : 2 ∣ X - (X - 1) := Nat.dvd_sub h2X hpX
          rw [show X - (X - 1) = 1 by omega] at h21
          omega
        exact two_sq_not_dvd_geom_sum_pow a (r - 1) hodd_a (by omega)
      · exact odd_sq_not_dvd_geom_sum X p (by omega) hp.one_lt hodd hpX
    obtain ⟨p', hp', hp'g, hp'ne⟩ := exists_prime_ne_of_sq_not_dvd _ p hp.two_le hgt hsq
    exact ⟨p', hp', hp'g,
      fun h => hp'ne (prime_eq_of_dvd_geom_sum_of_dvd_sub X p p' (by omega) hp hp' hp'g h)⟩
  · exact ⟨p, hp, hpg, hpX⟩

/-- V.5.2, equation(1): vanishing of a geometric sum gives the corresponding root of unity. -/
theorem pow_eq_one_of_dvd_geom_sum (X q m : ℕ)
    (hg : m ∣ ∑ i ∈ range q, X ^ i) : (X : ZMod m) ^ q = 1 := by
  have h0 : ((∑ i ∈ range q, X ^ i : ℕ) : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hg
  push_cast at h0
  have h := geom_sum_mul (X : ZMod m) q
  rw [h0, zero_mul] at h
  exact sub_eq_zero.mp h.symm

/-- V.5.2, the denominator condition: its nonvanishing rules out the preceding prime power. -/
theorem pow_ne_one_of_not_dvd_sub (a k m : ℕ) (ha : 1 ≤ a)
    (hsub : ¬ m ∣ a ^ k - 1) : (a : ZMod m) ^ k ≠ 1 := by
  intro h
  apply hsub
  have h1 : 1 ≤ a ^ k := Nat.one_le_pow _ _ (by omega)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_pow, h, Nat.cast_one, sub_self]

/-- V.5.2, residue-unit packaging: a positive power equal to one supplies an actual unit. -/
theorem exists_unit_eq_of_pow_eq_one {M : Type*} [Monoid M] (x : M) (n : ℕ)
    (hn : 0 < n) (hx : x ^ n = 1) : ∃ u : Mˣ, (u : M) = x := by
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hx⟩).isUnit

/-- V.5.2, minimal exponent: a prime-power annihilator and the preceding failure determine order. -/
theorem orderOf_eq_prime_pow {M : Type*} [Monoid M] (x : M) (q r : ℕ)
    (hq : q.Prime) (hr : 1 ≤ r) (hpow : x ^ (q ^ r) = 1)
    (hprev : x ^ (q ^ (r - 1)) ≠ 1) : orderOf x = q ^ r := by
  haveI := Fact.mk hq
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hprev
  exact _root_.orderOf_eq_prime_pow hprev hpow

end ResidueUnits

/-- Janusz V.5.2: elementary prime-power order construction; the r≥2 condition
avoids the exceptional first power cases. -/
theorem exists_prime_order_eq_primePower (a q r : ℕ) (ha : 2 ≤ a)
    (hq : q.Prime) (hr : 2 ≤ r) :
    ∃ p : ℕ, p.Prime ∧ ∃ u : (ZMod p)ˣ, (u : ZMod p) = a ∧ orderOf u = q ^ r := by
  obtain ⟨p, hp, hpg, hpX⟩ := ResidueUnits.exists_prime_dvd_geom_sum_not_dvd_sub a q r ha hq hr
  have hpow := ResidueUnits.pow_eq_one_of_dvd_geom_sum (a ^ (q ^ (r - 1))) q p hpg
  have hqr : q ^ (r - 1) * q = q ^ r := by
    rw [← pow_succ]
    congr 1
    omega
  have hpow' : (a : ZMod p) ^ (q ^ r) = 1 := by
    rw [← hqr, pow_mul]
    push_cast at hpow
    exact hpow
  obtain ⟨u, hu⟩ :=
    ResidueUnits.exists_unit_eq_of_pow_eq_one (a : ZMod p) (q ^ r) (pow_pos hq.pos _) hpow'
  have hprev : (a : ZMod p) ^ (q ^ (r - 1)) ≠ 1 :=
    ResidueUnits.pow_ne_one_of_not_dvd_sub a _ p (by omega) hpX
  refine ⟨p, hp, u, hu, ResidueUnits.orderOf_eq_prime_pow u q r hq (by omega) ?_ ?_⟩
  · ext
    rw [Units.val_pow_eq_pow_val, hu, Units.val_one]
    exact hpow'
  · intro h
    apply hprev
    rw [← hu, ← Units.val_pow_eq_pow_val, h, Units.val_one]

end Cox.ClassFieldTheory
