/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Algebra

import XYin.PhD.Cox.Kronecker

/-!
# The Frobenius calculation in Kronecker's congruence

At a prime level and after setting the cyclotomic phase to one, the first `p` Cox roots
coincide. The remaining root is their `p²`-th power. This file evaluates that product in
characteristic `p` and completes Cox Theorem 11.18(v).
-/

noncomputable section

namespace Cox

open Polynomial

/-- At phase one, every lower prime-level root is the unit-step reduction of `j`. -/
theorem transformedJSeries_one_primeLower_eq_jUnit
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (i : Fin (p : ℕ)) :
    transformedJSeries (1 : ZMod (p : ℕ)) (primeLowerCoxMatrix p i) =
      jUnitLaurentSeriesMod p := by
  ext k
  rw [transformedJSeries_coeff, jUnitLaurentSeriesMod_coeff]
  simp only [primeLowerCoxMatrix, Nat.cast_one, one_pow, one_dvd,
    Int.ediv_one, one_mul, one_zpow]
  by_cases hk : -(1 : ℤ) ≤ k
  · rw [if_pos ⟨trivial, hk⟩, mul_one]
  · rw [if_neg (fun h ↦ hk h.2), jIntCoeff_eq_zero_of_lt (lt_of_not_ge hk)]
    simp

/-- At prime level and phase one, the formal Cox product has one repeated lower factor and one
distinguished factor. -/
theorem formalCoxPolynomial_prime_one_factorization
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    formalCoxPolynomial p (1 : ZMod (p : ℕ)) =
      (X - C (jUnitLaurentSeriesMod p)) ^ (p : ℕ) *
        (X - C (transformedJSeries (1 : ZMod (p : ℕ)) (sigmaZero p))) := by
  let f : CoxMatrix p → Polynomial (LaurentSeries (ZMod (p : ℕ))) := fun σ ↦
    X - C (transformedJSeries (1 : ZMod (p : ℕ)) σ)
  rw [formalCoxPolynomial]
  calc
    ∏ σ : CoxMatrix p, f σ =
        ∏ i : Fin ((p : ℕ) + 1), f ((primeCoxMatrixEquiv p).symm i) := by
      exact ((primeCoxMatrixEquiv p).symm.prod_comp f).symm
    _ = (∏ i : Fin (p : ℕ),
          f ((primeCoxMatrixEquiv p).symm i.castSucc)) *
          f ((primeCoxMatrixEquiv p).symm (Fin.last (p : ℕ))) := by
      exact Fin.prod_univ_castSucc _
    _ = (∏ _i : Fin (p : ℕ), (X - C (jUnitLaurentSeriesMod p))) *
          (X - C (transformedJSeries (1 : ZMod (p : ℕ)) (sigmaZero p))) := by
      have hcast (i : Fin (p : ℕ)) :
          (primeCoxMatrixEquiv p).symm i.castSucc = primeLowerCoxMatrix p i := by
        simp [primeCoxMatrixEquiv_symm_apply_of_lt p i.castSucc i.isLt]
      simp only [hcast, primeCoxMatrixEquiv_symm_apply_last, f]
      simp_rw [transformedJSeries_one_primeLower_eq_jUnit]
    _ = _ := by rw [Fin.prod_const]

private noncomputable def unitJPowerSeries
    (K : Type*) [Ring K] : PowerSeries K :=
  PowerSeries.mk fun n ↦ (jIntCoeff ((n : ℤ) - 1) : K)

@[simp]
private theorem unitJPowerSeries_coeff
    {K : Type*} [Ring K] (n : ℕ) :
    PowerSeries.coeff n (unitJPowerSeries K) =
      (jIntCoeff ((n : ℤ) - 1) : K) := by
  simp [unitJPowerSeries]

private theorem jUnitLaurentSeriesMod_eq_unitJPowerSeries
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    jUnitLaurentSeriesMod p =
      HahnSeries.single (-1 : ℤ) 1 *
        (unitJPowerSeries (ZMod (p : ℕ)) :
          LaurentSeries (ZMod (p : ℕ))) := by
  ext k
  rw [jUnitLaurentSeriesMod_coeff, HahnSeries.coeff_single_mul]
  simp only [one_mul]
  by_cases hk : -1 ≤ k
  · rw [PowerSeries.coeff_coe]
    have hnonneg : 0 ≤ k - (-1 : ℤ) := by lia
    rw [if_neg hnonneg.not_gt, unitJPowerSeries_coeff,
      Int.natAbs_of_nonneg hnonneg]
    congr 2
    lia
  · rw [jIntCoeff_eq_zero_of_lt (lt_of_not_ge hk), Int.cast_zero,
      PowerSeries.coeff_coe]
    have hneg : k - (-1 : ℤ) < 0 := by lia
    rw [if_pos hneg]

private theorem prime_sq_dvd_iff_dvd_shift_natAbs
    (p : ℕ+) (k : ℤ) :
    ((p : ℤ) ^ 2 ∣ k) ↔
      (p : ℕ) ^ 2 ∣ (k - -((p : ℤ) ^ 2)).natAbs := by
  rw [← Int.natCast_dvd]
  simp only [Int.natCast_pow]
  constructor
  · intro h
    simpa only [sub_neg_eq_add, neg_neg] using
      h.add (dvd_refl ((p : ℤ) ^ 2))
  · intro h
    simpa only [sub_neg_eq_add, neg_neg, add_sub_cancel_right] using
      h.sub (dvd_refl ((p : ℤ) ^ 2))

private theorem transformedJSeries_one_sigmaZero_eq_expand
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    transformedJSeries (1 : ZMod (p : ℕ)) (sigmaZero p) =
      HahnSeries.single (-((p : ℤ) ^ 2)) 1 *
        ((unitJPowerSeries (ZMod (p : ℕ))).expand
          ((p : ℕ) ^ 2) (pow_ne_zero 2 (PNat.ne_zero p)) :
            LaurentSeries (ZMod (p : ℕ))) := by
  ext k
  rw [transformedJSeries_coeff, HahnSeries.coeff_single_mul]
  simp only [sigmaZero, Nat.cast_zero, mul_zero, zero_mul, one_zpow,
    mul_one]
  by_cases hlower : -((p : ℤ) ^ 2) ≤ k
  · rw [PowerSeries.coeff_coe]
    have hnonneg : 0 ≤ k - -((p : ℤ) ^ 2) := by lia
    rw [if_neg hnonneg.not_gt, PowerSeries.coeff_expand]
    by_cases hkdiv : (p : ℤ) ^ 2 ∣ k
    · rw [if_pos ⟨hkdiv, hlower⟩,
        if_pos ((prime_sq_dvd_iff_dvd_shift_natAbs p k).mp hkdiv),
        unitJPowerSeries_coeff]
      rw [Int.natCast_div, Int.natCast_natAbs, abs_of_nonneg hnonneg]
      obtain ⟨t, rfl⟩ := hkdiv
      have hp2ne : (p : ℤ) ^ 2 ≠ 0 := by
        exact pow_ne_zero 2 (by exact_mod_cast PNat.ne_zero p)
      rw [show (p : ℤ) ^ 2 * t - -((p : ℤ) ^ 2) =
          (p : ℤ) ^ 2 * (t + 1) by ring_nf]
      simp only [Int.natCast_pow]
      rw [Int.mul_ediv_cancel_left _ hp2ne,
        Int.mul_ediv_cancel_left _ hp2ne]
      ring_nf
    · rw [if_neg (fun h ↦ hkdiv h.1),
        if_neg (fun h ↦ hkdiv ((prime_sq_dvd_iff_dvd_shift_natAbs p k).mpr h))]
      simp
  · rw [if_neg (fun h ↦ hlower h.2), PowerSeries.coeff_coe]
    have hneg : k - -((p : ℤ) ^ 2) < 0 := by lia
    rw [if_pos hneg]
    simp

private theorem unitJPowerSeries_pow_prime_sq_eq_expand
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    unitJPowerSeries (ZMod (p : ℕ)) ^ ((p : ℕ) ^ 2) =
      (unitJPowerSeries (ZMod (p : ℕ))).expand ((p : ℕ) ^ 2)
        (pow_ne_zero 2 (PNat.ne_zero p)) := by
  have hiter :
      iterateFrobenius (ZMod (p : ℕ)) (p : ℕ) 2 = RingHom.id _ := by
    ext x
    change x ^ ((p : ℕ) ^ 2) = x
    exact ZMod.pow_card_pow x
  have h := MvPowerSeries.map_iterateFrobenius_expand
    (R := ZMod (p : ℕ)) (p : ℕ) (PNat.ne_zero p)
    (unitJPowerSeries (ZMod (p : ℕ))) 2
  rw [hiter, MvPowerSeries.map_id] at h
  exact h.symm

private theorem transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    transformedJSeries (1 : ZMod (p : ℕ)) (sigmaZero p) =
      jUnitLaurentSeriesMod p ^ ((p : ℕ) ^ 2) := by
  rw [transformedJSeries_one_sigmaZero_eq_expand,
    jUnitLaurentSeriesMod_eq_unitJPowerSeries,
    ← unitJPowerSeries_pow_prime_sq_eq_expand]
  rw [mul_pow, HahnSeries.single_pow, ← PowerSeries.coe_pow]
  simp

/-- The distinguished root is the `p²`-th power of each of the `p` equal lower roots. -/
theorem transformedJSeries_one_sigmaZero_eq_primeLower_pow
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (i : Fin (p : ℕ)) :
    transformedJSeries (1 : ZMod (p : ℕ)) (sigmaZero p) =
      transformedJSeries (1 : ZMod (p : ℕ)) (primeLowerCoxMatrix p i) ^
        ((p : ℕ) ^ 2) := by
  rw [transformedJSeries_one_primeLower_eq_jUnit]
  exact transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq p

/-- Equivalently, the distinguished root is the `p`-th power of the width-`p` `j`-series. -/
theorem transformedJSeries_one_sigmaZero_eq_jLaurent_pow
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    transformedJSeries (1 : ZMod (p : ℕ)) (sigmaZero p) =
      jLaurentSeriesMod p ^ (p : ℕ) := by
  rw [transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq]
  calc
    jUnitLaurentSeriesMod p ^ ((p : ℕ) ^ 2) =
        (jUnitLaurentSeriesMod p ^ (p : ℕ)) ^ (p : ℕ) := by
      rw [← pow_mul, pow_two]
    _ = jLaurentSeriesMod p ^ (p : ℕ) := by
      rw [jUnitLaurentSeriesMod_pow_prime]

/-- The prime-level formal Cox product in the Frobenius form used for Kronecker's congruence. -/
theorem formalCoxPolynomial_prime_one_frobenius
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    formalCoxPolynomial p (1 : ZMod (p : ℕ)) =
      (X ^ (p : ℕ) - C (jLaurentSeriesMod p)) *
        (X - C (jLaurentSeriesMod p ^ (p : ℕ))) := by
  letI : CharP (LaurentSeries (ZMod (p : ℕ))) (p : ℕ) :=
    charP_of_injective_ringHom
      (f := HahnSeries.C) HahnSeries.C_injective (p : ℕ)
  rw [formalCoxPolynomial_prime_one_factorization,
    transformedJSeries_one_sigmaZero_eq_jLaurent_pow]
  rw [sub_pow_char, ← C_pow, jUnitLaurentSeriesMod_pow_prime]

/-- After specializing the second variable at the width-`p` `j`-series, the modular polynomial
modulo `p` has the Kronecker factorization. -/
theorem kronecker_after_specializeJ
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    specializeJMod p
        (BivariatePolynomial.map (Int.castRingHom (ZMod (p : ℕ)))
          (modularPolynomial p)) =
      specializeJMod p
        ((BivariatePolynomial.varX : BivariatePolynomial (ZMod (p : ℕ))) ^
            (p : ℕ) - BivariatePolynomial.varY) *
        specializeJMod p
          (BivariatePolynomial.varX -
            (BivariatePolynomial.varY : BivariatePolynomial (ZMod (p : ℕ))) ^
              (p : ℕ)) := by
  rw [specializeJMod_modularPolynomial_eq_formal,
    formalCoxPolynomial_prime_one_frobenius]
  simp

/-- Cox Theorem 11.18(v), Kronecker's congruence. -/
theorem theorem_11_18_v
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    BivariatePolynomial.map (Int.castRingHom (ZMod (p : ℕ)))
        (modularPolynomial p) =
      ((BivariatePolynomial.varX : BivariatePolynomial (ZMod (p : ℕ))) ^
          (p : ℕ) - BivariatePolynomial.varY) *
        (BivariatePolynomial.varX -
          (BivariatePolynomial.varY : BivariatePolynomial (ZMod (p : ℕ))) ^
            (p : ℕ)) := by
  apply specializeJMod_injective p
  simpa only [map_mul] using kronecker_after_specializeJ p

end Cox
