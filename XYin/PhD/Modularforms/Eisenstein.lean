/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import XYin.PhD.Modularforms.Delta
public import XYin.PhD.Modularforms.E2

/-!
# The Eisenstein series `E₄`, `E₆` at level `Γ(1)`

This file defines the normalized Eisenstein series `E₄`, `E₆` as modular forms for `Γ(1)` (their
underlying functions are mathlib's `ModularForm.E₄`, `ModularForm.E₆`), computes their
`q`-expansions, and proves reality and boundedness properties of Eisenstein series on the
imaginary axis.

## Main results

* `E4_q_exp`, `E6_q_exp`: the `q`-expansion coefficients `240 σ₃(m)` and `-504 σ₅(m)`.
* `Delta_eq_E4_E6`: `Δ = (E₄³ - E₆²) / 1728`.
* `E_even_imag_axis_real`, `E₂_imag_axis_real`: `E_k(it)` (`k ≥ 4` even) and `E₂(it)` are real.
* `E₂_isBoundedAtImInfty`: `E₂` is bounded at `i∞`.
-/

@[expose] public section

open ModularForm hiding E₄ E₆
open EisensteinSeries UpperHalfPlane Filter Complex ArithmeticFunction

open scoped Real ArithmeticFunction.sigma

noncomputable section

/-- The normalized Eisenstein series of weight 4 for `Γ(1)`. The factor `1/2` normalizes the
constant term to `1`, since `eisensteinSeriesMF` sums over coprime pairs. -/
def E₄ : ModularForm (CongruenceSubgroup.Gamma ↑1) 4 :=
  (1/2 : ℂ) • eisensteinSeriesMF (by norm_num) 0

/-- The normalized Eisenstein series of weight 6 for `Γ(1)`. -/
def E₆ : ModularForm (CongruenceSubgroup.Gamma ↑1) 6 :=
  (1/2 : ℂ) • eisensteinSeriesMF (by norm_num) 0

/-- The `q`-expansion of `E₄`: `E₄ = 1 + 240 ∑ σ₃(m) qᵐ`. -/
lemma E4_q_exp : (fun m ↦ (qExpansion 1 E₄).coeff m) =
    fun m ↦ if m = 0 then 1 else (240 : ℂ) * (σ 3 m) := by
  funext m
  convert E_qExpansion_coeff (show 3 ≤ 4 by decide) (show Even 4 from ⟨2, rfl⟩) m using 1
  norm_num [E₄, ModularForm.E, show bernoulli 4 = -1 / 30 by
    norm_num [bernoulli_eq_bernoulli'_of_ne_one], div_eq_mul_inv]

/-- The Bernoulli number `B'₆ = 1/42` (mathlib stops at `bernoulli'_four`). -/
@[simp]
theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd (show Odd 5 by decide),
    show Nat.choose 6 2 = 15 by decide, show Nat.choose 6 4 = 15 by decide]

/-- The `q`-expansion of `E₆`: `E₆ = 1 - 504 ∑ σ₅(m) qᵐ`. -/
lemma E6_q_exp : (fun m ↦ (qExpansion 1 E₆).coeff m) =
    fun m ↦ if m = 0 then 1 else -(504 : ℂ) * (σ 5 m) := by
  funext m
  convert E_qExpansion_coeff (show 3 ≤ 6 by decide) (show Even 6 from ⟨3, rfl⟩) m using 1
  norm_num [E₆, ModularForm.E, show bernoulli 6 = 1 / 42 by
    norm_num [bernoulli_eq_bernoulli'_of_ne_one], div_eq_mul_inv]

/-- The first `q`-expansion coefficient of `Δ` is `1`. -/
lemma Delta_q_one_term : (qExpansion 1 Delta).coeff 1 = 1 := by
  rw [coe_Delta]
  exact discriminant_qExpansion_coeff_one

/-- The discriminant equals `(E₄³ - E₆²) / 1728` pointwise. -/
theorem Delta_eq_E4_E6 (τ : ℍ) : Delta τ = (E₄ τ ^ 3 - E₆ τ ^ 2) / 1728 :=
  (congrFun coe_Delta τ).trans (ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ)

/-! ## Eisenstein series on the imaginary axis -/

/-- `E_k(it)` is real for all `t > 0` when `k ≥ 3` is even. -/
theorem E_even_imag_axis_real (k : ℕ) (hk : 3 ≤ k) (hk2 : Even k) :
    ResToImagAxis.Real (ModularForm.E hk) := by
  intro t ht
  have hterm (n : ℕ+) : ((σ (k - 1) n : ℂ) * (Real.exp (-2 * π * t) : ℂ) ^ (n : ℤ)).im = 0 := by
    rw [← ofReal_zpow, ← ofReal_natCast, ← ofReal_mul, ofReal_im]
  have hc : (2 * (k : ℂ) / (bernoulli k : ℂ)).im = 0 := by
    rw [show 2 * (k : ℂ) / (bernoulli k : ℂ) = ((2 * k / bernoulli k : ℚ) : ℂ) by push_cast; ring,
      ratCast_im]
  rw [Function.resToImagAxis_of_pos _ ht, q_expansion_bernoulli hk hk2, coe_mk,
    cexp_two_pi_I_mul_I_mul, sub_im, one_im, mul_im, hc,
    Complex.im_tsum_eq_zero_of_im_eq_zero _ hterm]
  ring

/-- `E₄(it)` is real for all `t > 0`. -/
@[fun_prop]
theorem E₄_imag_axis_real : ResToImagAxis.Real E₄.toFun :=
  E_even_imag_axis_real 4 (by norm_num) (by decide)

/-- `E₆(it)` is real for all `t > 0`. -/
@[fun_prop]
theorem E₆_imag_axis_real : ResToImagAxis.Real E₆.toFun :=
  E_even_imag_axis_real 6 (by norm_num) (by decide)

/-- `E₂(it)` is real for all `t > 0`. -/
@[fun_prop]
theorem E₂_imag_axis_real : ResToImagAxis.Real E2 := by
  intro t ht
  have hterm (n : ℕ+) : ((σ 1 n : ℂ) * (Real.exp (-2 * π * t) : ℂ) ^ (n : ℕ)).im = 0 := by
    rw [← ofReal_pow, ← ofReal_natCast, ← ofReal_mul, ofReal_im]
  rw [Function.resToImagAxis_of_pos _ ht, E2_eq_tsum_cexp, coe_mk, cexp_two_pi_I_mul_I_mul,
    sub_im, one_im, mul_im, Complex.im_tsum_eq_zero_of_im_eq_zero _ hterm]
  simp

/-! ## Boundedness of `E₂` -/

/-- For `im z ≥ 1`, `‖exp(2πiz)‖ ≤ exp(-2π)`. -/
lemma norm_exp_two_pi_I_le_exp_neg_two_pi (z : ℍ) (hz : 1 ≤ z.im) :
    ‖cexp (2 * π * Complex.I * z)‖ ≤ Real.exp (-2 * π) := by
  have h : (2 * ↑π * Complex.I * (z : ℂ)).re = -2 * π * z.im := by
    rw [show (2 : ℂ) * ↑π * Complex.I * z = Complex.I * (2 * π * z) by ring]
    simp [Complex.I_re, Complex.I_im, mul_comm]
  rw [Complex.norm_exp, h, Real.exp_le_exp]
  nlinarith [Real.pi_pos]

/-- Bound on the `q`-series `∑ n qⁿ/(1 - qⁿ)` that appears in `E₂`: for `‖q‖ < 1`,
`‖∑_{n ≥ 1} n qⁿ/(1 - qⁿ)‖ ≤ ‖q‖/(1 - ‖q‖)³`.

The key estimates are `|1 - qⁿ| ≥ 1 - |q|` for `n ≥ 1`, hence
`|n qⁿ/(1 - qⁿ)| ≤ n |q|ⁿ/(1 - |q|)`, and `∑ n rⁿ = r/(1 - r)²`. -/
lemma norm_tsum_logDeriv_expo_le {q : ℂ} (hq : ‖q‖ < 1) :
    ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤ ‖q‖ / (1 - ‖q‖) ^ 3 := by
  set r : ℝ := ‖q‖
  have hr_norm_lt_one : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg (norm_nonneg q)]
  have hsumm_nat : Summable (fun n : ℕ ↦ (n : ℝ) * r ^ n) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr_norm_lt_one
  have hsumm_majorant : Summable (fun n : ℕ+ ↦ (n : ℝ) * r ^ (n : ℕ) / (1 - r)) := by
    simpa [div_eq_mul_inv] using (hsumm_nat.subtype _).mul_right (1 - r)⁻¹
  have hterm_bound : ∀ n : ℕ+, ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤
      n * r ^ (n : ℕ) / (1 - r) := fun n ↦ by
    rw [norm_div, norm_mul, Complex.norm_natCast]
    have hdenom_lower : 1 - r ≤ ‖1 - q ^ (n : ℕ)‖ := calc
      1 - r ≤ 1 - r ^ (n : ℕ) := by
        have : r ^ (n : ℕ) ≤ r := pow_le_of_le_one (norm_nonneg _) hq.le n.ne_zero
        linarith
      _ = 1 - ‖q ^ (n : ℕ)‖ := by rw [norm_pow]
      _ ≤ ‖1 - q ^ (n : ℕ)‖ := by
        have := norm_sub_norm_le (1 : ℂ) (q ^ (n : ℕ)); simp only [norm_one] at this; linarith
    calc ↑n * ‖q ^ (n : ℕ)‖ / ‖1 - q ^ (n : ℕ)‖ ≤ ↑n * ‖q ^ (n : ℕ)‖ / (1 - r) := by
          exact div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
            (sub_pos.mpr hq) hdenom_lower
      _ = ↑n * r ^ (n : ℕ) / (1 - r) := by rw [norm_pow]
  have hsumm_norms : Summable (fun n : ℕ+ ↦ ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖) :=
    .of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm_bound hsumm_majorant
  have htsum : ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) = r / (1 - r) ^ 2 := by
    rw [← tsum_coe_mul_geometric_of_norm_lt_one hr_norm_lt_one,
      ← tsum_zero_pnat_eq_tsum_nat hsumm_nat, Nat.cast_zero, zero_mul, zero_add]
  calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
      ≤ ∑' n : ℕ+, ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ := norm_tsum_le_tsum_norm hsumm_norms
    _ ≤ ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) :=
        hsumm_norms.tsum_le_tsum hterm_bound hsumm_majorant
    _ = r / (1 - r) ^ 3 := by
        rw [tsum_div_const, htsum]
        field_simp

/-- Monotone version of `norm_tsum_logDeriv_expo_le`: if `‖q‖ ≤ r < 1`, then
`‖∑ n qⁿ/(1 - qⁿ)‖ ≤ r/(1 - r)³`. -/
lemma norm_tsum_logDeriv_expo_le_of_norm_le {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (hr : r < 1) :
    ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤ r / (1 - r) ^ 3 := by
  have hq : ‖q‖ < 1 := lt_of_le_of_lt hqr hr
  have hr_nonneg : 0 ≤ r := le_trans (norm_nonneg _) hqr
  calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
      ≤ ‖q‖ / (1 - ‖q‖) ^ 3 := norm_tsum_logDeriv_expo_le hq
    _ ≤ r / (1 - r) ^ 3 := by
        have := sub_pos.mpr hr
        have := sub_pos.mpr hq
        gcongr

/-- `E₂` is bounded at `i∞`: by `E₂_eq`, `E₂(z) = 1 - 24 ∑ n qⁿ/(1 - qⁿ)`, and for `im z ≥ 1` we
have `|q| ≤ exp(-2π)`, so `|E₂(z)| ≤ 1 + 24 exp(-2π)/(1 - exp(-2π))³`. -/
lemma E₂_isBoundedAtImInfty : IsBoundedAtImInfty E2 := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  set r₀ : ℝ := Real.exp (-2 * π)
  have hr₀_lt_one : r₀ < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  refine ⟨1 + 24 * (r₀ / (1 - r₀) ^ 3), 1, fun z hz ↦ ?_⟩
  rw [E₂_eq]
  set q : ℂ := cexp (2 * π * Complex.I * z)
  have hq_bound : ‖q‖ ≤ r₀ := norm_exp_two_pi_I_le_exp_neg_two_pi z hz
  set S := ∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))
  have hS_eq : ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
      (1 - cexp (2 * π * Complex.I * ↑n * ↑z)) = S := by
    congr 1; ext n
    have : cexp (2 * π * Complex.I * n * z) = q ^ (n : ℕ) := by
      change _ = (cexp (2 * π * Complex.I * z)) ^ (n : ℕ)
      rw [← Complex.exp_nat_mul]; ring_nf
    simp [this]
  calc ‖1 - 24 * ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
          (1 - cexp (2 * π * Complex.I * ↑n * ↑z))‖
      = ‖1 - 24 * S‖ := by rw [hS_eq]
    _ ≤ 1 + 24 * ‖S‖ := by
        calc _ ≤ ‖(1 : ℂ)‖ + ‖24 * S‖ := norm_sub_le _ _
          _ = _ := by simp
    _ ≤ 1 + 24 * (r₀ / (1 - r₀) ^ 3) := by
        gcongr; exact norm_tsum_logDeriv_expo_le_of_norm_le hq_bound hr₀_lt_one
