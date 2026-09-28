/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import XYin.PhD.Modularforms.ResToImagAxis

/-!
# The modular discriminant on the imaginary axis

Mathlib's modular discriminant `ModularForm.discriminant`, `Δ(z) = η(z)²⁴ = q ∏_{n ≥ 1} (1 - qⁿ)²⁴`
with `q = e^{2πiz}` (bundled as the cusp form `CuspForm.discriminant` of weight 12 for `𝒮ℒ`), is
real and positive on the positive imaginary axis.

## Main results

* `discriminant_imag_axis_real`, `discriminant_imag_axis_pos`: `Δ(it)` is real and positive for
  `t > 0`.
-/

@[expose] public section

open ModularForm UpperHalfPlane Filter Complex

open scoped Real Topology

local notation "Δ" => ModularForm.discriminant

noncomputable section

/-- On the positive imaginary axis, `Δ(it) = e^{-2πt} ∏_{n ≥ 0} (1 - e^{-2π(n+1)t})²⁴` is the
image of a real number. -/
lemma discriminant_resToImagAxis {t : ℝ} (ht : 0 < t) : Function.resToImagAxis Δ t =
    ↑(Real.exp (-2 * π * t) * ∏' n : ℕ, (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24) := by
  have h (n : ℕ) : cexp (2 * π * Complex.I * (n + 1) * (Complex.I * t)) =
      Real.exp (-(2 * π * ((n + 1) : ℝ) * t)) := by
    rw [ofReal_exp]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  simp only [Function.resToImagAxis_of_pos _ ht, discriminant_eq_q_prod, eta_q_eq_cexp,
    Function.Periodic.qParam, ofReal_one, div_one, h, cexp_two_pi_I_mul_I_mul, ofReal_mul,
    Complex.ofReal_tprod, ofReal_pow, ofReal_sub]

/-- `Δ(it)` is real on the (positive) imaginary axis. -/
lemma discriminant_imag_axis_real : ResToImagAxis.Real Δ := fun t ht ↦ by
  rw [discriminant_resToImagAxis ht, ofReal_im]

/-- The real part of `Δ(it)`, as an explicit real infinite product. -/
lemma re_ResToImagAxis_discriminant_eq_real_prod (t : ℝ) (ht : 0 < t) :
    (Function.resToImagAxis Δ t).re = Real.exp (-2 * π * t) *
      ∏' (n : ℕ), (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24 := by
  rw [discriminant_resToImagAxis ht, ofReal_re]

/-- The product `∏ (1 - e^{-2π(n+1)t})²⁴` is positive for `t > 0`. -/
lemma tprod_pos_nat_im {t : ℝ} (ht : 0 < t) :
    0 < ∏' (n : ℕ), (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24 := by
  have hpos : ∀ n : ℕ, 0 < (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24 := fun n ↦
    pow_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by
      simpa using mul_pos (mul_pos Real.two_pi_pos n.cast_add_one_pos) ht))) _
  have hsum : Summable fun n : ℕ ↦ Real.exp (-(2 * π * ((n + 1) : ℝ) * t)) := by
    have h0 := Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr (by positivity : 0 < 2 * π * t))
    simpa [mul_comm, mul_left_comm, mul_assoc] using (summable_nat_add_iff 1).mpr h0
  rw [← Real.rexp_tsum_eq_tprod hpos]
  · exact Real.exp_pos _
  · simp_rw [Real.log_pow]
    simpa [sub_eq_add_neg] using (Real.summable_log_one_add_of_summable hsum.neg).mul_left 24

/-- `Δ(it)` is positive on the (positive) imaginary axis. -/
lemma discriminant_imag_axis_pos : ResToImagAxis.Pos Δ :=
  ⟨discriminant_imag_axis_real, fun t ht ↦ by
    rw [re_ResToImagAxis_discriminant_eq_real_prod t ht]
    exact mul_pos (Real.exp_pos _) (tprod_pos_nat_im ht)⟩
