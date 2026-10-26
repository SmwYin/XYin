/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

import XYin.PhD.IntegralPowerSeries.IntegralPowerSeries
import XYin.PhD.Modularforms.Eisenstein

/-!
# Integral q-expansions of the Eisenstein series and the discriminant

This file constructs integral q-expansions of mathlib's level-one Eisenstein series
`ModularForm.E₄`, `ModularForm.E₆` and of the modular discriminant `ModularForm.discriminant`, and
proves the divisibility needed to define the integral Ramanujan tau coefficients.

## Main definitions

* `integralE4`, `integralE6`: integral lifts of the Eisenstein-series q-expansions.
* `integralDelta`: the integral q-expansion of the modular discriminant.
* `ramanujanTau`: the coefficients of `integralDelta`.

## Main results

* `ModularForm.qExpansion_coe_pow`, `E₄_pow_three_qExpansion`, `E₆_pow_two_qExpansion`: the
  q-expansion of a power of a modular form is the power of its q-expansion.
* `E₄_isIntegralPowerSeries`, `E₆_isIntegralPowerSeries`: integrality of Eisenstein q-expansions.
* `discriminant_isIntegralPowerSeries`: integrality of the discriminant q-expansion.
-/

open Complex ModularForm ModularFormClass ArithmeticFunction UpperHalfPlane IntegralPowerSeries
open scoped MatrixGroups

noncomputable section

/-- The q-expansion of a power of a modular form is the power of its q-expansion. -/
lemma ModularForm.qExpansion_coe_pow {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne]
    {k : ℤ} {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : ModularForm Γ k) (n : ℕ) :
    qExpansion h (⇑f ^ n) = qExpansion h f ^ n := by
  simpa using f.qExpansion_pow hh hΓ n

/-- The q-expansion of `E₄ ^ 3` is the cube of the q-expansion of `E₄`. -/
lemma E₄_pow_three_qExpansion : qExpansion 1 (E₄ ^ 3) = qExpansion 1 E₄ ^ 3 :=
  ModularForm.qExpansion_coe_pow one_pos one_mem_strictPeriods_SL E₄ 3

/-- The q-expansion of `E₆ ^ 2` is the square of the q-expansion of `E₆`. -/
lemma E₆_pow_two_qExpansion : qExpansion 1 (E₆ ^ 2) = qExpansion 1 E₆ ^ 2 :=
  ModularForm.qExpansion_coe_pow one_pos one_mem_strictPeriods_SL E₆ 2

private lemma E₄_qExpansion_coeff (n : ℕ) :
    (qExpansion 1 E₄).coeff n = ((if n = 0 then 1 else 240 * (sigma 3 n : ℤ) : ℤ) : ℂ) := by
  simpa using congr_fun E₄_q_exp n

private lemma E₆_qExpansion_coeff (n : ℕ) :
    (qExpansion 1 E₆).coeff n = ((if n = 0 then 1 else -504 * (sigma 5 n : ℤ) : ℤ) : ℂ) := by
  simpa using congr_fun E₆_q_exp n

/-- The q-expansion of the normalized weight-four Eisenstein series has integral coefficients. -/
lemma E₄_isIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 E₄) :=
  (int_iff _).2 fun n ↦ ⟨_, E₄_qExpansion_coeff n⟩

/-- The q-expansion of the normalized weight-six Eisenstein series has integral coefficients. -/
lemma E₆_isIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 E₆) :=
  (int_iff _).2 fun n ↦ ⟨_, E₆_qExpansion_coeff n⟩

/-- The integral q-expansion of the normalized weight-four Eisenstein series. -/
def integralE4 : PowerSeries ℤ := toIntegralPowerSeries E₄_isIntegralPowerSeries

/-- The integral q-expansion of the normalized weight-six Eisenstein series. -/
def integralE6 : PowerSeries ℤ := toIntegralPowerSeries E₆_isIntegralPowerSeries

/-- The coefficients of `integralE4`: `E₄ = 1 + 240 ∑ σ₃(n) qⁿ`. -/
lemma integralE4_coeff (n : ℕ) :
    integralE4.coeff n = if n = 0 then 1 else 240 * (sigma 3 n : ℤ) := by
  exact_mod_cast (coeff_toIntegralPowerSeries_cast _ n).trans (E₄_qExpansion_coeff n)

/-- The coefficients of `integralE6`: `E₆ = 1 - 504 ∑ σ₅(n) qⁿ`. -/
lemma integralE6_coeff (n : ℕ) :
    integralE6.coeff n = if n = 0 then 1 else -504 * (sigma 5 n : ℤ) := by
  exact_mod_cast (coeff_toIntegralPowerSeries_cast _ n).trans (E₆_qExpansion_coeff n)

/-- The constant coefficient of `integralE4` is `1`. -/
lemma integralE4_coeff_zero : integralE4.coeff 0 = 1 := by
  rw [integralE4_coeff, if_pos rfl]

/-- The constant coefficient of `integralE6` is `1`. -/
lemma integralE6_coeff_zero : integralE6.coeff 0 = 1 := by
  rw [integralE6_coeff, if_pos rfl]

/-- For positive `n`, the `n`-th coefficient of `integralE4` is `240 * σ₃ n`. -/
lemma integralE4_coeff_of_pos (n : ℕ) (hn : 1 ≤ n) :
    integralE4.coeff n = (240 : ℤ) * sigma 3 n := by
  simp [integralE4_coeff, Nat.one_le_iff_ne_zero.1 hn]

/-- For positive `n`, the `n`-th coefficient of `integralE6` is `-(504 * σ₅ n)`. -/
lemma integralE6_coeff_of_pos (n : ℕ) (hn : 1 ≤ n) :
    integralE6.coeff n = -((504 : ℤ) * sigma 5 n) := by
  simp [integralE6_coeff, Nat.one_le_iff_ne_zero.1 hn]

/-- The q-expansion of the cube of `E₄` has integral coefficients. -/
lemma E₄_pow_three_isIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 (E₄ ^ 3)) :=
  E₄_pow_three_qExpansion ▸ hasCoeffsIn_pow ℤ ℂ E₄_isIntegralPowerSeries 3

private lemma twelve_dvd_weighted_sigma_aux (n : ℕ) :
    12 ∣ 5 * sigma 3 n + 7 * sigma 5 n := by
  have h (d : ℕ) : 12 ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    generalize (d : ZMod 12) = x
    revert x
    decide
  simpa [sigma_apply, Finset.mul_sum, Finset.sum_add_distrib] using
    Finset.dvd_sum fun d (_ : d ∈ n.divisors) ↦ h d

private def e4Bar : PowerSeries ℤ := integralE4 - 1

private def e6Bar : PowerSeries ℤ := integralE6 - 1

private lemma e4Bar_coeff_dvd_aux (m : ℕ) : 240 ∣ e4Bar.coeff m := by
  rw [e4Bar, map_sub, integralE4_coeff, PowerSeries.coeff_one]
  split_ifs <;> simp

private lemma e6Bar_coeff_dvd_aux (m : ℕ) : 504 ∣ e6Bar.coeff m := by
  rw [e6Bar, map_sub, integralE6_coeff, PowerSeries.coeff_one]
  split_ifs <;> simp

private lemma coeff_mul_dvd_aux (a b : ℤ) (f g : PowerSeries ℤ)
    (hf : ∀ m, a ∣ f.coeff m) (hg : ∀ m, b ∣ g.coeff m) :
    ∀ m, a * b ∣ (f * g).coeff m := by
  intro m
  rw [PowerSeries.coeff_mul]
  exact Finset.dvd_sum fun p _ ↦ mul_dvd_mul (hf p.1) (hg p.2)

private lemma coeff_pow_dvd_aux (a : ℤ) (f : PowerSeries ℤ) (hf : ∀ m, a ∣ f.coeff m)
    (k : ℕ) : ∀ m, a ^ k ∣ (f ^ k).coeff m := by
  induction k with
  | zero => intro m; simp
  | succ k ih =>
    intro m
    simpa [pow_succ] using coeff_mul_dvd_aux (a ^ k) a (f ^ k) f ih hf m

/- Writing `E₄ = 1 + e₄` and `E₆ = 1 + e₆`, where `240 ∣ e₄` and `504 ∣ e₆` coefficientwise,
`E₄³ - E₆² = (e₄³ + 3e₄² - e₆²) + (3e₄ - 2e₆)`; the first part is divisible by `1728` term by term
and the linear part has coefficients `144 (5σ₃(n) + 7σ₅(n))`. -/
private lemma eisenstein_difference_coeff_dvd_aux (n : ℕ) :
    1728 ∣ (integralE4 ^ 3 - integralE6 ^ 2).coeff n := by
  have hid : integralE4 ^ 3 - integralE6 ^ 2 = e4Bar ^ 3 + PowerSeries.C 3 * e4Bar ^ 2 -
      e6Bar ^ 2 + (PowerSeries.C 3 * e4Bar - PowerSeries.C 2 * e6Bar) := by
    simp only [e4Bar, e6Bar, map_ofNat]
    ring
  rw [hid, map_add, map_sub, map_add, PowerSeries.coeff_C_mul]
  refine dvd_add (dvd_sub (dvd_add ?_ ?_) ?_) ?_
  · exact dvd_trans (by norm_num) (coeff_pow_dvd_aux 240 e4Bar e4Bar_coeff_dvd_aux 3 n)
  · exact dvd_trans (by norm_num : (1728 : ℤ) ∣ 3 * 240 ^ 2)
      (mul_dvd_mul_left 3 (coeff_pow_dvd_aux 240 e4Bar e4Bar_coeff_dvd_aux 2 n))
  · exact dvd_trans (by norm_num) (coeff_pow_dvd_aux 504 e6Bar e6Bar_coeff_dvd_aux 2 n)
  simp only [map_sub, PowerSeries.coeff_C_mul, e4Bar, e6Bar, integralE4_coeff, integralE6_coeff,
    PowerSeries.coeff_one]
  split_ifs
  · simp
  · obtain ⟨c, hc⟩ := twelve_dvd_weighted_sigma_aux n
    have hc' := congrArg (Nat.cast : ℕ → ℤ) hc
    push_cast at hc'
    exact ⟨c, by linear_combination 144 * hc'⟩

/-- Complexifying `integralE4 ^ 3 - integralE6 ^ 2` recovers the q-expansion of the modular
form `E₄ ^ 3 - E₆ ^ 2`. -/
lemma map_integralE4_pow_three_sub_integralE6_pow_two :
    (coeToComplexPowerSeries.ringHom ℤ) (integralE4 ^ 3 - integralE6 ^ 2) =
      qExpansion 1 (E₄ ^ 3 - E₆ ^ 2) := by
  rw [map_sub, map_pow, map_pow, integralE4, integralE6,
    coeTo_of_toIntegralPowerSeries, coeTo_of_toIntegralPowerSeries, ← E₄_pow_three_qExpansion,
    ← E₆_pow_two_qExpansion]
  symm
  simpa only [pow_three, pow_two, ModularForm.coe_mul] using
    ModularForm.qExpansion_sub (hh := one_pos) (hΓ := one_mem_strictPeriods_SL)
      (E₄.mul (E₄.mul E₄)) (E₆.mul E₆)

/-- Every coefficient of `integralE4 ^ 3 - integralE6 ^ 2` vanishes modulo `1728`. -/
lemma eisenstein_difference_coeff_modEq_zero (n : ℕ) :
    Int.ModEq 1728 ((integralE4 ^ 3 - integralE6 ^ 2).coeff n) 0 :=
  (Int.modEq_zero_iff_dvd).2 (eisenstein_difference_coeff_dvd_aux n)

/-- The identity `Δ = (E₄³ - E₆²) / 1728` at the level of q-expansions. -/
lemma discriminant_qExpansion_eq_smul_eisenstein_difference :
    qExpansion 1 discriminant = (1 / 1728 : ℂ) • qExpansion 1 (E₄ ^ 3 - E₆ ^ 2) := by
  let H : ModularForm 𝒮ℒ 12 :=
    ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)
  have hH : ⇑H = ⇑E₄ ^ 3 - ⇑E₆ ^ 2 := by
    ext z
    simp only [H, coe_mcast, coe_pow, sub_apply, Pi.pow_apply, Pi.sub_apply]
  have hΔ : discriminant = (1 / 1728 : ℂ) • ⇑H := by
    ext z
    rw [discriminant_eq_E₄_cube_sub_E₆_sq z, hH, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul,
      one_div]
    rfl
  rw [hΔ, qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero H one_pos
    one_mem_strictPeriods_SL), hH]

/-- The q-expansion of the modular discriminant has integral coefficients. -/
lemma discriminant_isIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 discriminant) := by
  rw [discriminant_qExpansion_eq_smul_eisenstein_difference]
  have hIntegral : IsIntegralPowerSeries (qExpansion 1 (E₄ ^ 3 - E₆ ^ 2)) :=
    ⟨_, map_integralE4_pow_three_sub_integralE6_pow_two⟩
  apply IsIntegralPowerSeriesmod (by decide) hIntegral
  intro n
  rw [toIntegralPowerSeries_eq_of_map_eq _ map_integralE4_pow_three_sub_integralE6_pow_two]
  exact eisenstein_difference_coeff_modEq_zero n

/-- The integral q-expansion of the modular discriminant. -/
def integralDelta : PowerSeries ℤ := toIntegralPowerSeries discriminant_isIntegralPowerSeries

/-- The Ramanujan tau coefficients of the integral discriminant q-expansion. -/
def ramanujanTau : ℕ → ℤ := fun n ↦ integralDelta.coeff n

/-- The Ramanujan tau values are the q-expansion coefficients of `Δ`. -/
lemma ramanujanTau_cast (n : ℕ) :
    ((ramanujanTau n : ℤ) : ℂ) = (qExpansion 1 discriminant).coeff n :=
  coeff_toIntegralPowerSeries_cast discriminant_isIntegralPowerSeries n

end
