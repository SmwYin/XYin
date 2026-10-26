/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalSeries
import XYin.PhD.Cox.Theorem11_1.ClassFieldSeriesAlgebra

/-! # The actual small logarithm and exponential identities

Janusz V.3.5, printed151/PDF162. Every statement uses the source series values,
with the common convergence radius explicitly retained.
-/
open NumberField IsDedekindDomain
noncomputable section
namespace Cox.ClassFieldTheory.LocalCyclic
variable (K : Type*) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

/-- The actual convergent exponential sends addition of small inputs to multiplication. -/
theorem expValue_add_small (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : v.adicCompletion K)‖ < 1) (x y : v.adicCompletion K)
    (hx : ‖(p : v.adicCompletion K)‖⁻¹ * ‖x‖ < 1)
    (hy : ‖(p : v.adicCompletion K)‖⁻¹ * ‖y‖ < 1) :
    expValue K v (x + y) = expValue K v x * expValue K v y := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  rw [expValue_eq_powerSeries_value, expValue_eq_powerSeries_value, expValue_eq_powerSeries_value]
  convert Cox.ClassFieldConvergentSeries.value_exp_add p hp x y hx hy
  all_goals exact Subsingleton.elim _ _

/-- Evaluated formal substitution gives the first actual inverse identity. -/
theorem log_exp_inverse_small (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : v.adicCompletion K)‖ < 1) (x : v.adicCompletion K)
    (hx : (‖(p : v.adicCompletion K)‖⁻¹) ^ 2 * ‖x‖ < 1) :
    logValue K v (expValue K v x - 1) = x := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have hp0 : 0 < ‖(p : v.adicCompletion K)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hC1 : 1 ≤ ‖(p : v.adicCompletion K)‖⁻¹ := (one_le_inv₀ hp0).mpr hp.le
  have hCx : ‖(p : v.adicCompletion K)‖⁻¹ * ‖x‖ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_self_pow₀ hC1 two_ne_zero) (norm_nonneg x)) hx
  have hx1 : ‖x‖ < 1 := lt_of_le_of_lt (le_mul_of_one_le_left (norm_nonneg x) hC1) hCx
  have hle := expValue_sub_one_norm_le K v p hp x hCx
  have hsum : Summable (logTerm K v (expValue K v x - 1)) :=
    Cox.ClassFieldSeriesBounds.log_summable_of_norm_lt_one (v.adicCompletion K) p hp _
      (lt_of_le_of_lt hle hx1)
  rw [logValue_eq_powerSeries_value K v _ hsum, expValue_eq_powerSeries_value]
  convert Cox.ClassFieldConvergentSeries.value_log_exp_sub_one p hp x hx
  all_goals exact Subsingleton.elim _ _

/-- The second actual inverse identity uses the same common radius. -/
theorem exp_log_inverse_small (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : v.adicCompletion K)‖ < 1) (x : v.adicCompletion K)
    (hx : (‖(p : v.adicCompletion K)‖⁻¹) ^ 2 * ‖x‖ < 1) :
    expValue K v (logValue K v x) = 1 + x := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have hp0 : 0 < ‖(p : v.adicCompletion K)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hC1 : 1 ≤ ‖(p : v.adicCompletion K)‖⁻¹ := (one_le_inv₀ hp0).mpr hp.le
  have hCx : ‖(p : v.adicCompletion K)‖⁻¹ * ‖x‖ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_self_pow₀ hC1 two_ne_zero) (norm_nonneg x)) hx
  have hx1 : ‖x‖ < 1 := lt_of_le_of_lt (le_mul_of_one_le_left (norm_nonneg x) hC1) hCx
  have hsum : Summable (logTerm K v x) :=
    Cox.ClassFieldSeriesBounds.log_summable_of_norm_lt_one (v.adicCompletion K) p hp x hx1
  rw [logValue_eq_powerSeries_value K v x hsum, expValue_eq_powerSeries_value]
  convert Cox.ClassFieldConvergentSeries.value_exp_log p hp x hx
  all_goals exact Subsingleton.elim _ _

/-- The inverse and addition identities turn the product of two small principal units into a sum. -/
theorem log_mul_small (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : v.adicCompletion K)‖ < 1) (x y : v.adicCompletion K)
    (hx : (‖(p : v.adicCompletion K)‖⁻¹) ^ 2 * ‖x‖ < 1)
    (hy : (‖(p : v.adicCompletion K)‖⁻¹) ^ 2 * ‖y‖ < 1) :
    logValue K v (x + y + x * y) = logValue K v x + logValue K v y := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have hp0 : 0 < ‖(p : v.adicCompletion K)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hC1 : 1 ≤ ‖(p : v.adicCompletion K)‖⁻¹ := (one_le_inv₀ hp0).mpr hp.le
  have hCx : ‖(p : v.adicCompletion K)‖⁻¹ * ‖x‖ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_self_pow₀ hC1 two_ne_zero) (norm_nonneg x)) hx
  have hCy : ‖(p : v.adicCompletion K)‖⁻¹ * ‖y‖ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_self_pow₀ hC1 two_ne_zero) (norm_nonneg y)) hy
  have hax := logValue_norm_le K v p hp x hCx
  have hby := logValue_norm_le K v p hp y hCy
  have hC0 : 0 ≤ ‖(p : v.adicCompletion K)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have ha : ‖(p : v.adicCompletion K)‖⁻¹ * ‖logValue K v x‖ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hax hC0) hCx
  have hb : ‖(p : v.adicCompletion K)‖⁻¹ * ‖logValue K v y‖ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hby hC0) hCy
  have hab : (‖(p : v.adicCompletion K)‖⁻¹) ^ 2 * ‖logValue K v x + logValue K v y‖ < 1 := by
    have hsum := IsUltrametricDist.norm_add_le_max (logValue K v x) (logValue K v y)
    rcases le_total ‖logValue K v x‖ ‖logValue K v y‖ with h | h
    · rw [max_eq_right h] at hsum
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hsum.trans hby) (pow_nonneg hC0 2)) hy
    · rw [max_eq_left h] at hsum
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hsum.trans hax) (pow_nonneg hC0 2)) hx
  have key := log_exp_inverse_small K v p hp (logValue K v x + logValue K v y) hab
  rw [expValue_add_small K v p hp _ _ ha hb, exp_log_inverse_small K v p hp x hx,
    exp_log_inverse_small K v p hp y hy] at key
  rw [← key]
  congr 1
  ring

end Cox.ClassFieldTheory.LocalCyclic
