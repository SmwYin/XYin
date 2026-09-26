/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# The quasi-modular Eisenstein series `E₂`

Complements to mathlib's `EisensteinSeries.E2`: its periodicity, its transformation under
`S : z ↦ -1/z` in pointwise form, and its Lambert-series expansion.
-/

@[expose] public section

open EisensteinSeries ModularForm UpperHalfPlane Complex

open scoped Real

/-- `E₂` is 1-periodic: `E₂(z + 1) = E₂(z)`. -/
lemma E₂_periodic (z : ℍ) : E2 ((1 : ℝ) +ᵥ z) = E2 z := by
  have h := congrFun (E2_slash_action ModularGroup.T) z
  rw [D2_T, smul_zero, sub_zero, SL_slash_apply, modular_T_smul] at h
  simpa [ModularGroup.T, denom] using h

/-- `E₂` transforms under `S` as `E₂(-1/z) = z² (E₂(z) + 6/(π i z))`. -/
lemma E₂_S_transform (z : ℍ) :
    E2 (ModularGroup.S • z) = z ^ 2 * (E2 z + 6 / (π * Complex.I * z)) := by
  have h := congrFun (E2_slash_action ModularGroup.S) z
  rw [SL_slash_apply, ModularGroup.denom_S] at h
  simp only [zpow_neg, zpow_ofNat, Pi.sub_apply, Pi.smul_apply, D2_S, riemannZeta_two,
    smul_eq_mul] at h
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  rw [(mul_inv_eq_iff_eq_mul₀ (pow_ne_zero 2 hz)).mp h]
  field_simp
  ring_nf
  simp [I_sq]
  ring

/-- The Lambert-series form `E₂(z) = 1 - 24 ∑_{n ≥ 1} n qⁿ / (1 - qⁿ)`, `q = e^{2πiz}`. -/
lemma E₂_eq (z : UpperHalfPlane) : E2 z =
    1 - 24 * ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * n * z) /
                        (1 - cexp (2 * π * Complex.I * n * z)) := by
  rw [E2_eq_tsum_cexp,
    ← tsum_pow_div_one_sub_eq_tsum_sigma (UpperHalfPlane.norm_exp_two_pi_I_lt_one z) 1]
  simp [← Complex.exp_nat_mul, mul_assoc, mul_comm, mul_left_comm]
