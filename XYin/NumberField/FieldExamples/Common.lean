/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Common lemmas for number field examples

This file contains shared algebraic helpers used by several number field examples.
-/

namespace NumberField.FieldExamples

/-- A divisor of `p²` for prime `p` is `p` once the cases `1` and `p²` are excluded. -/
theorem eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq {m p : ℕ} (hp : p.Prime)
    (hdvd : m ∣ p ^ 2) (h1 : m ≠ 1) (hp2 : m ≠ p ^ 2) : m = p := by
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases k
  · exact (h1 (by simpa using hkeq)).elim
  · simpa using hkeq
  · exact (hp2 hkeq).elim

/-- If two non-unit natural numbers multiply to `p²`, the left factor is `p`. -/
theorem left_eq_prime_of_mul_eq_prime_sq_of_ne_one {m n p : ℕ} (hp : p.Prime)
    (hmul : m * n = p ^ 2) (hm1 : m ≠ 1) (hn1 : n ≠ 1) : m = p :=
  eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq hp ⟨n, hmul.symm⟩ hm1 fun hm2 ↦
    hn1 <| Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by simpa [hm2] using hmul)

/-- A nonzero residue modulo a prime has a natural-number representative for an integer inverse. -/
theorem exists_int_inverse_mod_prime (p : ℕ) [Fact p.Prime] (a : ℤ)
    (ha : (a : ZMod p) ≠ 0) : ∃ m : ℕ, ∃ k : ℤ, (m : ℤ) * a - 1 = (p : ℤ) * k := by
  refine ⟨(((a : ZMod p)⁻¹).val), ?_⟩
  have hm : (((((a : ZMod p)⁻¹).val : ℕ) : ZMod p) * (a : ZMod p)) = 1 := by
    rw [ZMod.natCast_rightInverse]
    exact inv_mul_cancel₀ ha
  have hlift : (p : ℤ) ∣ (((((a : ZMod p)⁻¹).val : ℕ) : ℤ) * a - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination hm
  obtain ⟨k, hk⟩ := hlift
  exact ⟨k, hk⟩

/-- Nonzero ideals with equal absolute norms are equal when one is contained in the other. -/
theorem eq_of_le_of_absNorm_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] {I J : Ideal R} (hle : I ≤ J) {n : ℕ}
    (hI : Ideal.absNorm I = n) (hJ : Ideal.absNorm J = n) (hn : n ≠ 0) : I = J := by
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hmul := _root_.map_mul Ideal.absNorm J C
  rw [← hC, hI, hJ] at hmul
  have hC1 : Ideal.absNorm C = 1 :=
    (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn)
      (by rw [mul_one]; exact hmul)).symm
  rw [hC, Ideal.absNorm_eq_one_iff.mp hC1, Ideal.mul_top]

/-- Turn a strict rational absolute-value comparison between integers into a `natAbs`
comparison. -/
theorem natAbs_lt_of_abs_ratCast_lt {m n : ℤ} (h : |(m : ℚ)| < |(n : ℚ)|) :
    m.natAbs < n.natAbs := by
  have hltZ : |m| < |n| := by exact_mod_cast h
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hltZ
  exact_mod_cast hltZ

/-- The homomorphism from a finite cyclic additive index to powers of a torsion element. -/
def torsionPowerHom {G : Type*} [Group G] (n : ℕ) [NeZero n] (g : G) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* G :=
  MonoidHom.mk' (fun a => g ^ (Multiplicative.toAdd a).val) fun a b => by
    have hpow : ∀ k : ℕ, g ^ k = g ^ (k % n) := by
      intro k
      conv_lhs => rw [← Nat.div_add_mod k n]
      rw [pow_add, pow_mul, hg, one_pow, one_mul]
    calc g ^ (Multiplicative.toAdd (a * b)).val =
        g ^ ((Multiplicative.toAdd (a * b)).val % n) := hpow _
      _ = g ^ (((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) % n) := by
          rw [toAdd_mul, ZMod.val_add, Nat.mod_mod_of_dvd _ (dvd_refl n)]
      _ = g ^ ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) := (hpow _).symm
      _ = g ^ (Multiplicative.toAdd a).val * g ^ (Multiplicative.toAdd b).val :=
          pow_add _ _ _

/-- The homomorphism from the rank-one free coordinate to powers of a chosen unit. -/
def rankOnePowerHom {G : Type*} [Group G] (η : G) : Multiplicative (Fin 1 → ℤ) →* G :=
  MonoidHom.mk' (fun f => η ^ (Multiplicative.toAdd f 0)) fun f g => by
    change η ^ ((Multiplicative.toAdd f + Multiplicative.toAdd g) 0) = _
    rw [Pi.add_apply, zpow_add]

/-- A square containment of a mapped prime ideal forces ramification index at least two. -/
theorem two_le_ramificationIdx_of_map_le_sq_of_not_le_pow_succ {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] {p : Ideal R} {P : Ideal S} {n : ℕ}
    (hle2 : Ideal.map (algebraMap R S) p ≤ P ^ 2)
    (hnle : ¬ Ideal.map (algebraMap R S) p ≤ P ^ (n + 1)) :
    2 ≤ Ideal.ramificationIdx p P := by
  classical
  have hbounded : ∃ m, ∀ k, Ideal.map (algebraMap R S) p ≤ P ^ k → k ≤ m := by
    refine ⟨n, fun k hk ↦ le_of_not_gt fun hnk ↦ ?_⟩
    exact hnle (hk.trans (Ideal.pow_le_pow_right hnk))
  rw [Ideal.ramificationIdx_eq_find hbounded]
  exact Nat.find_spec hbounded 2 hle2

/-- A square containment of a mapped prime ideal makes the ramification index nontrivial. -/
theorem ramificationIdx_ne_one_of_map_le_sq_of_not_le_pow_succ {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] {p : Ideal R} {P : Ideal S} {n : ℕ}
    (hle2 : Ideal.map (algebraMap R S) p ≤ P ^ 2)
    (hnle : ¬ Ideal.map (algebraMap R S) p ≤ P ^ (n + 1)) :
    Ideal.ramificationIdx p P ≠ 1 := by
  have htwo := two_le_ramificationIdx_of_map_le_sq_of_not_le_pow_succ hle2 hnle
  omega

/-- A square containment over `(p)` makes the prime ramified. -/
theorem not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ {R : Type*}
    [CommRing R] [Algebra ℤ R] [IsDedekindDomain R] [Algebra.EssFiniteType ℤ R]
    [Algebra.IsIntegral ℤ R] {P : Ideal R} [P.IsPrime] {p n : ℕ} (hp : p.Prime)
    (hmem : ((p : ℕ) : R) ∈ P) (hPbot : P ≠ ⊥)
    (hle2 : Ideal.map (algebraMap ℤ R) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 2)
    (hnle : ¬ Ideal.map (algebraMap ℤ R) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ (n + 1)) :
    ¬ Algebra.IsUnramifiedAt ℤ P := by
  have hidx : Ideal.ramificationIdx (Ideal.span {((p : ℕ) : ℤ)}) P ≠ 1 :=
    ramificationIdx_ne_one_of_map_le_sq_of_not_le_pow_succ hle2 hnle
  have hpz : Prime (((p : ℕ) : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hmem' : algebraMap ℤ R ((p : ℕ) : ℤ) ∈ P := by
    convert hmem using 1
    norm_num
  have hund : Ideal.under ℤ P = Ideal.span {((p : ℕ) : ℤ)} :=
    ((Ideal.liesOver_span_iff (show P ≠ ⊤ from Ideal.IsPrime.ne_top inferInstance) hpz).mpr
      hmem').over.symm
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot, hund]
  exact hidx

/-- Norm comparison rules out containment in the next power of a prime ideal. -/
theorem not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow {R : Type*}
    [CommRing R] [Algebra ℤ R] [IsDedekindDomain R] [Module.Free ℤ R] {P : Ideal R}
    {p n k : ℕ} (hp : p.Prime)
    (habsp : Ideal.absNorm (Ideal.span {((p : ℕ) : R)}) = p ^ n)
    (habsP : Ideal.absNorm P = p ^ k) (hk0 : k ≠ 0) :
    ¬ Ideal.map (algebraMap ℤ R) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ (n + 1) := by
  intro hle
  have hle' : Ideal.span {((p : ℕ) : R)} ≤ P ^ (n + 1) := by
    simpa [Ideal.map_span, Set.image_singleton] using hle
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle'
  rw [map_pow, habsp, habsP, ← pow_mul] at hd
  rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  nlinarith

end NumberField.FieldExamples
