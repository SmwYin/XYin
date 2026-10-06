/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldConvergentSeries
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Int.GCD

/-! # The denominator estimates in Janusz V.3.5

The residue prime controls the norms of natural denominators. A polynomial
bound proves logarithmic convergence on the whole open unit ball; geometric
bounds suffice on the smaller exponential and substitution domains.
-/

open Filter
open scoped Topology
noncomputable section

namespace Cox.ClassFieldSeriesBounds

variable (F : Type*) [NormedField F] [IsUltrametricDist F]

/-- Bézout's identity forces a natural number prime to a small prime to have norm one. -/
theorem norm_natCast_eq_one_of_coprime (p n : ℕ)
    (hp : ‖(p : F)‖ < 1) (hn : p.Coprime n) : ‖(n : F)‖ = 1 := by
  have hle : ‖(n : F)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one F n
  refine le_antisymm hle (not_lt.mp fun hlt => ?_)
  have h := Nat.gcd_eq_gcd_ab p n
  rw [Nat.Coprime.gcd_eq_one hn] at h
  have h' : (1 : F) = (p : F) * (Nat.gcdA p n : F) + (n : F) * (Nat.gcdB p n : F) := by
    have := congrArg (Int.cast : ℤ → F) h
    push_cast at this
    exact this
  have h1 : ‖(p : F) * (Nat.gcdA p n : F)‖ < 1 := by
    rw [norm_mul]
    calc ‖(p : F)‖ * ‖(Nat.gcdA p n : F)‖ ≤ ‖(p : F)‖ * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one F _) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hp
  have h2 : ‖(n : F) * (Nat.gcdB p n : F)‖ < 1 := by
    rw [norm_mul]
    calc ‖(n : F)‖ * ‖(Nat.gcdB p n : F)‖ ≤ ‖(n : F)‖ * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one F _) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hlt
  have h3 := IsUltrametricDist.norm_add_le_max ((p : F) * (Nat.gcdA p n : F))
    ((n : F) * (Nat.gcdB p n : F))
  rw [← h', norm_one] at h3
  exact absurd h3 (not_le.mpr (max_lt h1 h2))

variable [CharZero F]

/-- Removing the prime-to-p factor computes the norm of a nonzero natural number. -/
theorem norm_natCast_eq_pow_padicValNat (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : F)‖ < 1) (n : ℕ) (hn : n ≠ 0) :
    ‖(n : F)‖ = ‖(p : F)‖ ^ padicValNat p n := by
  have hpp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := (pow_padicValNat_dvd : p ^ padicValNat p n ∣ n)
  have hpk : ¬p ∣ k := by
    rintro ⟨j, rfl⟩
    apply pow_succ_padicValNat_not_dvd (p := p) hn
    refine ⟨j, ?_⟩
    rw [pow_succ]
    nth_rewrite 1 [hk]
    ring
  have hcop : p.Coprime k := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hpk
  have hcast : (n : F) = (p : F) ^ padicValNat p n * (k : F) := by
    exact_mod_cast hk
  rw [hcast, norm_mul, norm_pow, norm_natCast_eq_one_of_coprime F p k hp hcop, mul_one]

/-- The logarithmic growth of p-adic exponents gives a polynomial denominator bound. -/
theorem exists_inv_natCast_norm_le_pow (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : F)‖ < 1) :
    ∃ d : ℕ, ∀ n : ℕ, n ≠ 0 → ‖(n : F)⁻¹‖ ≤ (n : ℝ) ^ d := by
  have hpp : p.Prime := Fact.out
  have hp0 : 0 < ‖(p : F)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hpp.ne_zero)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt (‖(p : F)‖⁻¹) hp1
  refine ⟨d, fun n hn => ?_⟩
  rw [norm_inv, norm_natCast_eq_pow_padicValNat F p hp n hn, ← inv_pow]
  have hpr : (p : ℝ) ^ padicValNat p n ≤ n := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd
  calc (‖(p : F)‖⁻¹) ^ padicValNat p n ≤ ((p : ℝ) ^ d) ^ padicValNat p n :=
        pow_le_pow_left₀ (inv_nonneg.mpr hp0.le) hd.le _
    _ = ((p : ℝ) ^ padicValNat p n) ^ d := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (n : ℝ) ^ d := pow_le_pow_left₀ (by positivity) hpr d

/-- The coarser linear valuation bound controls all positive natural denominators. -/
theorem inv_natCast_norm_le (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : F)‖ < 1) (n : ℕ) :
    ‖((n + 1 : ℕ) : F)⁻¹‖ ≤ (‖(p : F)‖⁻¹) ^ n := by
  have hpp : p.Prime := Fact.out
  have hp0 : 0 < ‖(p : F)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hpp.ne_zero)
  have hC : 1 ≤ ‖(p : F)‖⁻¹ := (one_le_inv₀ hp0).mpr hp.le
  rw [norm_inv, norm_natCast_eq_pow_padicValNat F p hp (n + 1) n.succ_ne_zero, ← inv_pow]
  apply pow_le_pow_right₀ hC
  have h1 : p ^ padicValNat p (n + 1) ≤ n + 1 := Nat.le_of_dvd n.succ_pos pow_padicValNat_dvd
  have h2 : padicValNat p (n + 1) < p ^ padicValNat p (n + 1) := Nat.lt_pow_self hpp.one_lt
  omega

/-- Legendre's inequality gives the same bound for the positive factorial denominators. -/
theorem inv_factorial_norm_le (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : F)‖ < 1) (n : ℕ) :
    ‖((n + 1).factorial : F)⁻¹‖ ≤ (‖(p : F)‖⁻¹) ^ n := by
  have hpp : p.Prime := Fact.out
  have hp0 : 0 < ‖(p : F)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hpp.ne_zero)
  have hC : 1 ≤ ‖(p : F)‖⁻¹ := (one_le_inv₀ hp0).mpr hp.le
  rw [norm_inv, norm_natCast_eq_pow_padicValNat F p hp _ (Nat.factorial_ne_zero _), ← inv_pow]
  apply pow_le_pow_right₀ hC
  have := padicValNat_factorial_lt_of_ne_zero p (n := n + 1) (by omega)
  omega

/-- The actual logarithmic formal coefficients have a common geometric bound. -/
theorem coeff_log_norm_le (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : F)‖ < 1) (n : ℕ) :
    ‖(PowerSeries.log F).coeff n‖ ≤ (‖(p : F)‖⁻¹) ^ n := by
  have hpp : p.Prime := Fact.out
  have hp0 : 0 < ‖(p : F)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hpp.ne_zero)
  have hC : 1 ≤ ‖(p : F)‖⁻¹ := (one_le_inv₀ hp0).mpr hp.le
  rw [PowerSeries.coeff_log]
  rcases n with _ | k
  · simp
  · rw [if_neg k.succ_ne_zero, map_div₀, map_pow, map_neg, map_one, map_natCast, norm_div,
      norm_pow, norm_neg, norm_one, one_pow, one_div, ← norm_inv]
    exact (inv_natCast_norm_le F p hp k).trans (pow_le_pow_right₀ hC k.le_succ)

/-- The actual exponential formal coefficients have the same geometric bound. -/
theorem coeff_exp_norm_le (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : F)‖ < 1) (n : ℕ) :
    ‖(PowerSeries.exp F).coeff n‖ ≤ (‖(p : F)‖⁻¹) ^ n := by
  have hpp : p.Prime := Fact.out
  have hp0 : 0 < ‖(p : F)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hpp.ne_zero)
  have hC : 1 ≤ ‖(p : F)‖⁻¹ := (one_le_inv₀ hp0).mpr hp.le
  rw [PowerSeries.coeff_exp]
  rcases n with _ | k
  · simp
  · rw [map_div₀, map_one, map_natCast, one_div]
    exact (inv_factorial_norm_le F p hp k).trans (pow_le_pow_right₀ hC k.le_succ)

/-- Removing the exponential's constant term preserves the geometric bound. -/
theorem coeff_exp_sub_one_norm_le (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : F)‖ < 1) (n : ℕ) :
    ‖(PowerSeries.exp F - 1).coeff n‖ ≤ (‖(p : F)‖⁻¹) ^ n := by
  rcases n with _ | k
  · simp
  · rw [map_sub, PowerSeries.coeff_one, if_neg k.succ_ne_zero, sub_zero]
    exact coeff_exp_norm_le F p hp (k + 1)

/-- Each logarithmic term has a geometric bound with the input norm as a factor. -/
theorem log_term_norm_le (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : F)‖ < 1) (x : F) (n : ℕ) :
    ‖(-1 : F) ^ n * x ^ (n + 1) / (n + 1 : ℕ)‖ ≤
      ‖x‖ * (‖(p : F)‖⁻¹ * ‖x‖) ^ n := by
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
    div_eq_mul_inv, ← norm_inv]
  calc ‖x‖ ^ (n + 1) * ‖((n + 1 : ℕ) : F)⁻¹‖ ≤ ‖x‖ ^ (n + 1) * (‖(p : F)‖⁻¹) ^ n :=
        mul_le_mul_of_nonneg_left (inv_natCast_norm_le F p hp n) (by positivity)
    _ = ‖x‖ * (‖(p : F)‖⁻¹ * ‖x‖) ^ n := by ring

/-- The nonconstant exponential terms obey the same input-scaled bound. -/
theorem exp_term_succ_norm_le (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : F)‖ < 1) (x : F) (n : ℕ) :
    ‖x ^ (n + 1) / ((n + 1).factorial : F)‖ ≤
      ‖x‖ * (‖(p : F)‖⁻¹ * ‖x‖) ^ n := by
  rw [norm_div, norm_pow, div_eq_mul_inv, ← norm_inv]
  calc ‖x‖ ^ (n + 1) * ‖((n + 1).factorial : F)⁻¹‖ ≤ ‖x‖ ^ (n + 1) * (‖(p : F)‖⁻¹) ^ n :=
        mul_le_mul_of_nonneg_left (inv_factorial_norm_le F p hp n) (by positivity)
    _ = ‖x‖ * (‖(p : F)‖⁻¹ * ‖x‖) ^ n := by ring

/-- Polynomial growth of denominators is dominated by every strict geometric decay. -/
theorem log_norm_summable_of_norm_lt_one (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : F)‖ < 1) (x : F) (hx : ‖x‖ < 1) :
    Summable (fun n : ℕ ↦ ‖(-1 : F) ^ n * x ^ (n + 1) / (n + 1 : ℕ)‖) := by
  obtain ⟨d, hd⟩ := exists_inv_natCast_norm_le_pow F p hp
  have hg : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ d * ‖x‖ ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_pow_mul_geometric_of_norm_lt_one d
      (by rwa [Real.norm_of_nonneg (norm_nonneg x)]))
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hg
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
    div_eq_mul_inv, ← norm_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right (hd (n + 1) n.succ_ne_zero) (by positivity)

variable [CompleteSpace F]

/-- Absolute summability gives the logarithm in the complete field itself. -/
theorem log_summable_of_norm_lt_one (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : F)‖ < 1) (x : F) (hx : ‖x‖ < 1) :
    Summable (fun n : ℕ ↦ (-1 : F) ^ n * x ^ (n + 1) / (n + 1 : ℕ)) := by
  exact (log_norm_summable_of_norm_lt_one F p hp x hx).of_norm

/-- The factorial bound makes the exponential summable on the explicit smaller ball. -/
theorem exp_summable_of_norm_lt (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : F)‖ < 1) (x : F) (hx : ‖(p : F)‖⁻¹ * ‖x‖ < 1) :
    Summable (fun n : ℕ ↦ x ^ n / (n.factorial : F)) := by
  refine (ClassFieldConvergentSeries.summable_term (PowerSeries.exp F) _
    (coeff_exp_norm_le F p hp) x hx).congr fun n => ?_
  rw [ClassFieldConvergentSeries.term, PowerSeries.coeff_exp, map_div₀, map_one, map_natCast,
    one_div, inv_mul_eq_div]

end Cox.ClassFieldSeriesBounds
