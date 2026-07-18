/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

import XYin.PhD.IntegralPowerSeries.IntegralPowerSeries
import XYin.PhD.Modularforms.Eisenstein

/-!
# Integral q-expansions of the Eisenstein series and the discriminant

This file constructs integral q-expansions of `E4`, `E6`, and `Delta`, and proves the
divisibility needed to define the integral Ramanujan tau coefficients.

## Main definitions

* `integralE4`, `integralE6`: integral lifts of the Eisenstein-series q-expansions.
* `integralDelta`: the integral q-expansion of the modular discriminant.
* `ramanujanTau`: the coefficients of `integralDelta`.

## Main results

* `E4_isIntegralPowerSeries`, `E6_isIntegralPowerSeries`: integrality of Eisenstein q-expansions.
* `Delta_isIntegralPowerSeries`: integrality of the discriminant q-expansion.
-/

open Complex
open ModularForm hiding E₄ E₆
open ModularFormClass ArithmeticFunction UpperHalfPlane IntegralPowerSeries

noncomputable section

/-- The normalized weight-four Eisenstein series. -/
abbrev E4 := _root_.E₄

/-- The normalized weight-six Eisenstein series. -/
abbrev E6 := _root_.E₆

private lemma E4_qExpansion_coeff_aux (n : ℕ) :
    (qExpansion 1 E4).coeff n = if n = 0 then 1 else (240 : ℂ) * sigma 3 n := by
  have hE4 : (E4 : ℍ → ℂ) = (ModularForm.E₄ : ℍ → ℂ) := rfl
  rw [hE4, EisensteinSeries.E_qExpansion_coeff (k := 4) (by norm_num) ⟨2, rfl⟩ n]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false]
    norm_num [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_four]

private lemma E6_qExpansion_coeff_aux (n : ℕ) :
    (qExpansion 1 E6).coeff n = if n = 0 then 1 else -(504 : ℂ) * sigma 5 n := by
  have hE6 : (E6 : ℍ → ℂ) = (ModularForm.E₆ : ℍ → ℂ) := rfl
  rw [hE6, EisensteinSeries.E_qExpansion_coeff (k := 6) (by norm_num) ⟨3, rfl⟩ n]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false]
    norm_num [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_six]

/-- The q-expansion of the normalized weight-four Eisenstein series has integral coefficients. -/
lemma E4_isIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 E4) := by
  rw [int_iff]
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨1, by simp [E4_qExpansion_coeff_aux]⟩
  · exact ⟨240 * sigma 3 n, by simp [E4_qExpansion_coeff_aux, hn]⟩

/-- The q-expansion of the normalized weight-six Eisenstein series has integral coefficients. -/
lemma E6_isIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 E6) := by
  rw [int_iff]
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨1, by simp [E6_qExpansion_coeff_aux]⟩
  · exact ⟨-504 * sigma 5 n, by simp [E6_qExpansion_coeff_aux, hn]⟩

/-- The integral q-expansion of the normalized weight-four Eisenstein series. -/
def integralE4 : PowerSeries ℤ := toIntegralPowerSeries E4_isIntegralPowerSeries

/-- The integral q-expansion of the normalized weight-six Eisenstein series. -/
def integralE6 : PowerSeries ℤ := toIntegralPowerSeries E6_isIntegralPowerSeries

/-- The q-expansion of the cube of `E4` has integral coefficients. -/
lemma E4_pow_three_isIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 (E4 ^ 3)) := by
  have hq : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using E4.qExpansion_pow (h := (1 : ℝ)) one_pos (by simp) 3
  rw [hq]
  exact IntegralPowerSeriesSubring.pow_mem E4_isIntegralPowerSeries 3

private lemma three_dvd_weighted_powers_aux (d : ℕ) : 3 ∣ (5 * d ^ 3 + 7 * d ^ 5) := by
  rw [← Int.natCast_dvd_natCast]
  have h : ∀ x : ZMod 3, (5 * x ^ 3 + 7 * x ^ 5 : ZMod 3) = 0 := by decide
  have h2 : ((5 * d ^ 3 + 7 * d ^ 5 : ℤ) : ZMod 3) = 0 := by exact_mod_cast h d
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2

private lemma four_dvd_weighted_powers_aux (d : ℕ) : 4 ∣ (5 * d ^ 3 + 7 * d ^ 5) := by
  rw [← Int.natCast_dvd_natCast]
  have h : ∀ x : ZMod 4, (5 * x ^ 3 + 7 * x ^ 5 : ZMod 4) = 0 := by decide
  have h2 : ((5 * d ^ 3 + 7 * d ^ 5 : ℤ) : ZMod 4) = 0 := by exact_mod_cast h d
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2

private lemma twelve_dvd_weighted_powers_aux (d : ℕ) : 12 ∣ (5 * d ^ 3 + 7 * d ^ 5) := by
  have h : Nat.Coprime 3 4 := by decide
  simpa using h.mul_dvd_of_dvd_of_dvd (three_dvd_weighted_powers_aux d)
    (four_dvd_weighted_powers_aux d)

private lemma twelve_dvd_weighted_sigma_aux (n : ℕ) :
    12 ∣ 5 * sigma 3 n + 7 * sigma 5 n := by
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  have hsum : 12 ∣ Finset.sum n.divisors fun d ↦ 5 * d ^ 3 + 7 * d ^ 5 :=
    Finset.dvd_sum fun d _ ↦ twelve_dvd_weighted_powers_aux d
  simpa [Finset.mul_sum, Finset.sum_add_distrib, left_distrib, right_distrib, add_assoc, add_comm,
    add_left_comm] using hsum

private lemma toIntegralPowerSeries_coeff_eq {S : PowerSeries ℂ} (hS : IsIntegralPowerSeries S)
    {n : ℕ} {z : ℤ} (hz : S.coeff n = (z : ℂ)) : (toIntegralPowerSeries hS).coeff n = z := by
  have h := congrArg (PowerSeries.coeff n) (coeTo_of_toIntegralPowerSeries hS)
  change (((toIntegralPowerSeries hS).coeff n : ℤ) : ℂ) = S.coeff n at h
  exact_mod_cast h.trans hz

/-- The constant coefficient of `integralE4` is `1`. -/
lemma integralE4_coeff_zero : integralE4.coeff 0 = 1 :=
  toIntegralPowerSeries_coeff_eq E4_isIntegralPowerSeries (by simp [E4_qExpansion_coeff_aux])

/-- The constant coefficient of `integralE6` is `1`. -/
lemma integralE6_coeff_zero : integralE6.coeff 0 = 1 :=
  toIntegralPowerSeries_coeff_eq E6_isIntegralPowerSeries (by simp [E6_qExpansion_coeff_aux])

private lemma integralE4_constantCoeff_aux : PowerSeries.constantCoeff integralE4 = 1 := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using integralE4_coeff_zero

private lemma integralE6_constantCoeff_aux : PowerSeries.constantCoeff integralE6 = 1 := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using integralE6_coeff_zero

/-- For positive `n`, the `n`-th coefficient of `integralE4` is `240 * σ₃ n`. -/
lemma integralE4_coeff_of_pos (n : ℕ) (hn : 1 ≤ n) :
    integralE4.coeff n = (240 : ℤ) * sigma 3 n :=
  toIntegralPowerSeries_coeff_eq E4_isIntegralPowerSeries
    (by rw [E4_qExpansion_coeff_aux, if_neg (by omega)]; push_cast; ring)

/-- For positive `n`, the `n`-th coefficient of `integralE6` is `-(504 * σ₅ n)`. -/
lemma integralE6_coeff_of_pos (n : ℕ) (hn : 1 ≤ n) :
    integralE6.coeff n = -((504 : ℤ) * sigma 5 n) :=
  toIntegralPowerSeries_coeff_eq E6_isIntegralPowerSeries
    (by rw [E6_qExpansion_coeff_aux, if_neg (by omega)]; push_cast; ring)

private lemma integralE4_coeff_dvd_aux (n : ℕ) (hn : 1 ≤ n) : 240 ∣ integralE4.coeff n :=
  ⟨sigma 3 n, integralE4_coeff_of_pos n hn⟩

private lemma integralE6_coeff_dvd_aux (n : ℕ) (hn : 1 ≤ n) : 504 ∣ integralE6.coeff n :=
  ⟨-(sigma 5 n : ℤ), by rw [integralE6_coeff_of_pos n hn]; ring⟩

private def e4Bar : PowerSeries ℤ := integralE4 - 1

private def e6Bar : PowerSeries ℤ := integralE6 - 1

private lemma e4Bar_coeff_dvd_aux (m : ℕ) : 240 ∣ e4Bar.coeff m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [e4Bar, integralE4_constantCoeff_aux]
  · simpa [e4Bar, hm] using integralE4_coeff_dvd_aux m (Nat.one_le_iff_ne_zero.mpr hm)

private lemma e6Bar_coeff_dvd_aux (m : ℕ) : 504 ∣ e6Bar.coeff m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [e6Bar, integralE6_constantCoeff_aux]
  · simpa [e6Bar, hm] using integralE6_coeff_dvd_aux m (Nat.one_le_iff_ne_zero.mpr hm)

private lemma coeff_mul_dvd_aux (a b : ℤ) (f g : PowerSeries ℤ)
    (hf : ∀ m, a ∣ f.coeff m) (hg : ∀ m, b ∣ g.coeff m) :
    ∀ m, a * b ∣ (f * g).coeff m := by
  intro m
  rw [PowerSeries.coeff_mul]
  refine Finset.dvd_sum fun p _ ↦ ?_
  rcases hf p.1 with ⟨u, hu⟩
  rcases hg p.2 with ⟨v, hv⟩
  refine ⟨u * v, ?_⟩
  rw [hu, hv]
  ring

private lemma coeff_pow_dvd_aux (a : ℤ) (f : PowerSeries ℤ) (hf : ∀ m, a ∣ f.coeff m)
    (k : ℕ) : ∀ m, a ^ k ∣ (f ^ k).coeff m := by
  induction k with
  | zero => intro m; simp
  | succ k ih =>
    intro m
    simpa [pow_succ] using coeff_mul_dvd_aux (a ^ k) a (f ^ k) f ih hf m

private lemma remainder_coeff_dvd_aux (n : ℕ) : (1728 : ℤ) ∣
    (e4Bar ^ 3 + 3 * e4Bar ^ 2 - e6Bar ^ 2).coeff n := by
  have h1 : (1728 : ℤ) ∣ (e4Bar ^ 3).coeff n :=
    dvd_trans (by norm_num) (coeff_pow_dvd_aux 240 e4Bar e4Bar_coeff_dvd_aux 3 n)
  have h2 : (1728 : ℤ) ∣ (3 * e4Bar ^ 2).coeff n := by
    have hcoef : (3 * e4Bar ^ 2).coeff n = 3 * (e4Bar ^ 2).coeff n := by
      simpa using PowerSeries.coeff_C_mul n (e4Bar ^ 2) (3 : ℤ)
    rw [hcoef]
    exact dvd_trans (by norm_num : (1728 : ℤ) ∣ 3 * 240 ^ 2)
      (mul_dvd_mul_left 3 (coeff_pow_dvd_aux 240 e4Bar e4Bar_coeff_dvd_aux 2 n))
  have h3 : (1728 : ℤ) ∣ (e6Bar ^ 2).coeff n :=
    dvd_trans (by norm_num) (coeff_pow_dvd_aux 504 e6Bar e6Bar_coeff_dvd_aux 2 n)
  simpa using Int.dvd_sub (Int.dvd_add h1 h2) h3

private lemma eisenstein_difference_modEq_linear_aux (n : ℕ) : Int.ModEq 1728
    ((integralE4 ^ 3 - integralE6 ^ 2).coeff n) ((3 * e4Bar - 2 * e6Bar).coeff n) := by
  rw [Int.modEq_iff_dvd]
  have hid : 3 * e4Bar - 2 * e6Bar - (integralE4 ^ 3 - integralE6 ^ 2) =
      -(e4Bar ^ 3 + 3 * e4Bar ^ 2 - e6Bar ^ 2) := by
    have hEA : integralE4 = e4Bar + 1 := by simp [e4Bar]
    have hEB : integralE6 = e6Bar + 1 := by simp [e6Bar]
    rw [hEA, hEB]
    ring
  have hcoeff : (3 * e4Bar - 2 * e6Bar).coeff n - (integralE4 ^ 3 - integralE6 ^ 2).coeff n =
      -((e4Bar ^ 3 + 3 * e4Bar ^ 2 - e6Bar ^ 2).coeff n) := by
    simpa using congrArg (PowerSeries.coeff n) hid
  rw [hcoeff]
  exact Int.dvd_neg.mpr (remainder_coeff_dvd_aux n)

private lemma linear_coeff_eq_aux (n : ℕ) (hn0 : n ≠ 0) :
    ((3 * e4Bar - 2 * e6Bar).coeff n) = 144 * (5 * sigma 3 n + 7 * sigma 5 n) := by
  have hn1 : 1 ≤ n := by omega
  have hAcoeff : e4Bar.coeff n = integralE4.coeff n := by simp [e4Bar, hn0]
  have hBcoeff : e6Bar.coeff n = integralE6.coeff n := by simp [e6Bar, hn0]
  have h3A : (3 * e4Bar).coeff n = 3 * e4Bar.coeff n := by
    simpa using (PowerSeries.coeff_C_mul n e4Bar (3 : ℤ))
  have h2B : (2 * e6Bar).coeff n = 2 * e6Bar.coeff n := by
    simpa using (PowerSeries.coeff_C_mul n e6Bar (2 : ℤ))
  calc
  _ = (3 * e4Bar).coeff n - (2 * e6Bar).coeff n := by simp
  _ = 3 * e4Bar.coeff n - 2 * e6Bar.coeff n := by simp [h3A, h2B]
  _ = 3 * integralE4.coeff n - 2 * integralE6.coeff n := by simp [hAcoeff, hBcoeff]
  _ = 3 * ((240 : ℤ) * sigma 3 n) - 2 * (-((504 : ℤ) * sigma 5 n)) := by
    simp [integralE4_coeff_of_pos n hn1, integralE6_coeff_of_pos n hn1]
  _ = _ := by ring

private lemma eisenstein_difference_modEq_aux (n : ℕ) :
    Int.ModEq 1728 ((integralE4 ^ 3 - integralE6 ^ 2).coeff n)
    (144 * (5 * sigma 3 n + 7 * sigma 5 n)) := by
  by_cases hn0 : n = 0
  · subst hn0
    rw [Int.ModEq]
    simp [integralE4_constantCoeff_aux, integralE6_constantCoeff_aux]
  · simpa [linear_coeff_eq_aux n hn0] using eisenstein_difference_modEq_linear_aux n

private lemma eisenstein_difference_coeff_dvd_aux (n : ℕ) :
    1728 ∣ (integralE4 ^ 3 - integralE6 ^ 2).coeff n := by
  have h12 : (12 : ℤ) ∣ (5 * sigma 3 n + 7 * sigma 5 n : ℤ) := by
    exact_mod_cast twelve_dvd_weighted_sigma_aux n
  have h1728 : (1728 : ℤ) ∣ (144 * (5 * sigma 3 n + 7 * sigma 5 n) : ℤ) := by
    obtain ⟨t, ht⟩ := h12
    exact ⟨t, by rw [ht]; ring⟩
  exact Int.modEq_zero_iff_dvd.1
    ((eisenstein_difference_modEq_aux n).trans (Int.modEq_zero_iff_dvd.2 h1728))

/-- Complexifying `integralE4 ^ 3 - integralE6 ^ 2` recovers the q-expansion of the modular
form `E4 ^ 3 - E6 ^ 2`. -/
lemma map_integralE4_pow_three_sub_integralE6_pow_two :
    (coeToComplexPowerSeries.ringHom ℤ) (integralE4 ^ 3 - integralE6 ^ 2) =
      qExpansion 1 (E4 ^ 3 - E6 ^ 2) := by
  have hE4 := coeTo_of_toIntegralPowerSeries E4_isIntegralPowerSeries
  have hE6 := coeTo_of_toIntegralPowerSeries E6_isIntegralPowerSeries
  have hpow4 : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using E4.qExpansion_pow (h := (1 : ℝ)) one_pos (by simp) 3
  have hpow6 : qExpansion 1 (E6 ^ 2) = (qExpansion 1 E6) ^ 2 := by
    simpa [DirectSum.ofPow] using E6.qExpansion_pow (h := (1 : ℝ)) one_pos (by simp) 2
  have hf : (⇑E4 * (⇑E4 * ⇑E4)) = ⇑(E4.mul (E4.mul E4)) := rfl
  have hg : (⇑E6 * ⇑E6) = ⇑(E6.mul E6) := rfl
  calc
  _ = ((coeToComplexPowerSeries.ringHom ℤ) integralE4) ^ 3
      - ((coeToComplexPowerSeries.ringHom ℤ) integralE6) ^ 2 := by simp [map_sub, map_pow]
  _ = (qExpansion 1 E4) ^ 3 - (qExpansion 1 E6) ^ 2 := by
    rw [integralE4, integralE6, hE4, hE6]
  _ = qExpansion 1 (E4 ^ 3) - qExpansion 1 (E6 ^ 2) := by rw [← hpow4, ← hpow6]
  _ = qExpansion 1 (E4.mul (E4.mul E4)) - qExpansion 1 (E6.mul E6) := by
    simp [pow_three, pow_two, hf, hg]
  _ = qExpansion 1 ((E4.mul (E4.mul E4)) - (E6.mul E6)) := by
    rw [ModularForm.qExpansion_sub (hh := by norm_num) (hΓ := by simp)]
  _ = _ := by simp [pow_three, pow_two, hf, hg]

private lemma eisenstein_difference_isIntegralPowerSeries_aux :
    IsIntegralPowerSeries (qExpansion 1 (E4 ^ 3 - E6 ^ 2)) :=
  ⟨integralE4 ^ 3 - integralE6 ^ 2, map_integralE4_pow_three_sub_integralE6_pow_two⟩

private lemma toIntegralPowerSeries_eisenstein_difference_aux :
    toIntegralPowerSeries eisenstein_difference_isIntegralPowerSeries_aux =
      integralE4 ^ 3 - integralE6 ^ 2 := by
  apply (PowerSeries.map_injective (algebraMap ℤ ℂ) Int.cast_injective)
  change
    (coeToComplexPowerSeries.ringHom ℤ)
        (toIntegralPowerSeries eisenstein_difference_isIntegralPowerSeries_aux) =
      (coeToComplexPowerSeries.ringHom ℤ) (integralE4 ^ 3 - integralE6 ^ 2)
  rw [coeTo_of_toIntegralPowerSeries]
  exact map_integralE4_pow_three_sub_integralE6_pow_two.symm

/-- Every coefficient of `integralE4 ^ 3 - integralE6 ^ 2` vanishes modulo `1728`. -/
lemma eisenstein_difference_coeff_modEq_zero (n : ℕ) :
    Int.ModEq 1728 ((integralE4 ^ 3 - integralE6 ^ 2).coeff n) 0 :=
  (Int.modEq_zero_iff_dvd).2 (eisenstein_difference_coeff_dvd_aux n)

/-- The identity `Δ = (E₄³ - E₆²) / 1728` at the level of q-expansions. -/
lemma Delta_qExpansion_eq_smul_eisenstein_difference :
    qExpansion 1 Delta = (1 / 1728 : ℂ) • qExpansion 1 (E4 ^ 3 - E6 ^ 2) := by
  let H : ModularForm (CongruenceSubgroup.Gamma 1) 12 :=
    ModularForm.mcast (by decide) (E4.pow 3) -
      ModularForm.mcast (by decide) (E6.pow 2)
  have hHfun : (⇑H : ℍ → ℂ) = (⇑E4 ^ 3 - ⇑E6 ^ 2) := by
    funext z
    simp only [H, ModularForm.coe_mcast, ModularForm.coe_pow, ModularForm.sub_apply,
      Pi.pow_apply, Pi.sub_apply]
  have hDeltaPointwise (z : ℍ) : Delta z = (E4 z ^ 3 - E6 z ^ 2) / 1728 := by
    rw [Delta_apply, Delta_eq_eta_pow]
    simpa [ModularForm.discriminant] using
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
  have hDeltaFun : (⇑Delta : ℍ → ℂ) = (1 / 1728 : ℂ) • (⇑H : ℍ → ℂ) := by
    funext z
    change Delta z = (1 / 1728 : ℂ) * H z
    rw [hDeltaPointwise, show H z = E4 z ^ 3 - E6 z ^ 2 from congrFun hHfun z]
    ring
  have hHan : AnalyticAt ℂ (cuspFunction 1 (⇑H : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero H (by norm_num) (by simp)
  calc
    _ = qExpansion 1 ((1 / 1728 : ℂ) • (⇑H : ℍ → ℂ)) := by rw [hDeltaFun]
    _ = (1 / 1728 : ℂ) • qExpansion 1 (⇑H : ℍ → ℂ) :=
      UpperHalfPlane.qExpansion_smul hHan _
    _ = _ := by rw [hHfun]

/-- The q-expansion of the modular discriminant has integral coefficients. -/
lemma Delta_isIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 Delta) := by
  rw [Delta_qExpansion_eq_smul_eisenstein_difference]
  apply IsIntegralPowerSeriesmod
  · decide
  · intro n
    rw [toIntegralPowerSeries_eisenstein_difference_aux]
    exact eisenstein_difference_coeff_modEq_zero n

/-- The integral q-expansion of the modular discriminant. -/
def integralDelta : PowerSeries ℤ := toIntegralPowerSeries Delta_isIntegralPowerSeries

/-- The Ramanujan tau coefficients of the integral discriminant q-expansion. -/
def ramanujanTau : ℕ → ℤ := fun n ↦ integralDelta.coeff n

end
