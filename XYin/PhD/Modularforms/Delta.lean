/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import XYin.PhD.Modularforms.ResToImagAxis

/-!
# The modular discriminant at level `Γ(1)`

The discriminant `Δ(z) = q ∏_{n ≥ 1} (1 - qⁿ)²⁴`, `q = e^{2πiz}`, as a function (`Δ`) and as a
cusp form of weight 12 for `Γ(1)` (`Delta`). Both agree with mathlib's
`ModularForm.discriminant` / `CuspForm.discriminant` (which are stated for `𝒮ℒ`); `Delta` is a
`CuspForm.copy` of the latter along `CongruenceSubgroup.Gamma_one_coe_eq_SL`.

## Main results

* `Δ_eq_discriminant`, `coe_Delta`: `Δ` and `⇑Delta` are mathlib's `ModularForm.discriminant`.
* `Delta_imag_axis_real`, `Delta_imag_axis_pos`: `Δ(it)` is real and positive for `t > 0`.
-/

@[expose] public section

open ModularForm UpperHalfPlane Filter Complex

open scoped Real Topology

noncomputable section

/-- The discriminant `Δ(z) = e^{2πiz} ∏_{n ≥ 0} (1 - e^{2πi(n+1)z})²⁴`. -/
def Δ (z : UpperHalfPlane) := cexp (2 * π * Complex.I * z) * ∏' (n : ℕ),
    (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24

/-- `Δ = η²⁴`. -/
lemma Delta_eq_eta_pow (z : ℍ) : Δ z = (η z) ^ 24 := by
  simpa [Δ, ModularForm.discriminant, Function.Periodic.qParam, ModularForm.eta_q_eq_cexp]
    using (ModularForm.discriminant_eq_q_prod z).symm

/-- The discriminant `Δ` is mathlib's `ModularForm.discriminant`. -/
lemma Δ_eq_discriminant : Δ = ModularForm.discriminant :=
  funext Delta_eq_eta_pow

/-- `Δ` does not vanish on the upper half-plane. -/
lemma Δ_ne_zero (z : UpperHalfPlane) : Δ z ≠ 0 := by
  rw [Δ_eq_discriminant]
  exact discriminant_ne_zero z

/-- The discriminant as a cusp form of weight 12 for `Γ(1)`: a copy of mathlib's
`CuspForm.discriminant` (a cusp form for `𝒮ℒ`) with underlying function `Δ`. -/
def Delta : CuspForm (CongruenceSubgroup.Gamma 1) 12 :=
  CuspForm.discriminant.copy Δ Δ_eq_discriminant CongruenceSubgroup.Gamma_one_coe_eq_SL

lemma Delta_apply (z : ℍ) : Delta z = Δ z := rfl

/-- The underlying function of `Delta` is mathlib's `ModularForm.discriminant`. -/
lemma coe_Delta : ⇑Delta = ModularForm.discriminant :=
  Δ_eq_discriminant

/-- The product factor `∏ (1 - qⁿ⁺¹)²⁴ = Δ/q` tends to `1` at `i∞`. -/
theorem Delta_boundedfactor :
    Tendsto (fun x : ℍ ↦ ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑x)) ^ 24)
      atImInfty (𝓝 1) := by
  simpa [ModularForm.eta_q_eq_cexp] using ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow

/-! ## `Δ` on the positive imaginary axis -/

/-- On the positive imaginary axis, `Δ(it) = e^{-2πt} ∏_{n ≥ 0} (1 - e^{-2π(n+1)t})²⁴` is the
image of a real number. -/
lemma Δ_resToImagAxis {t : ℝ} (ht : 0 < t) : Δ.resToImagAxis t =
    ↑(Real.exp (-2 * π * t) * ∏' n : ℕ, (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24) := by
  have h (n : ℕ) : cexp (2 * π * Complex.I * (n + 1) * (Complex.I * t)) =
      Real.exp (-(2 * π * ((n + 1) : ℝ) * t)) := by
    rw [ofReal_exp]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  simp only [Function.resToImagAxis_of_pos _ ht, Δ, h, cexp_two_pi_I_mul_I_mul,
    ofReal_mul, Complex.ofReal_tprod, ofReal_pow, ofReal_sub, ofReal_one]

/-- `Δ(it)` is real on the (positive) imaginary axis. -/
lemma Delta_imag_axis_real : ResToImagAxis.Real Δ := fun t ht ↦ by
  rw [Δ_resToImagAxis ht, ofReal_im]

/-- The real part of `Δ(it)`, as an explicit real infinite product. -/
lemma re_ResToImagAxis_Delta_eq_real_prod (t : ℝ) (ht : 0 < t) :
    (Δ.resToImagAxis t).re = Real.exp (-2 * π * t) *
      ∏' (n : ℕ), (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24 := by
  rw [Δ_resToImagAxis ht, ofReal_re]

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
lemma Delta_imag_axis_pos : ResToImagAxis.Pos Δ :=
  ⟨Delta_imag_axis_real, fun t ht ↦ by
    rw [re_ResToImagAxis_Delta_eq_real_prod t ht]
    exact mul_pos (Real.exp_pos _) (tprod_pos_nat_im ht)⟩
