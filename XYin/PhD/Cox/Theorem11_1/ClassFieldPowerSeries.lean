/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Evaluation

/-! # The formal identities in Janusz V.3.5

These identities are formal. Evaluating them at a local-field element requires the
separate convergence and rearrangement arguments in the local analytic layer.
-/

noncomputable section

namespace Cox.ClassFieldPowerSeries

/-- The linear coefficient of substitution by a zero-constant series. -/
theorem coeff_one_subst_of_constantCoeff_eq_zero
    {R : Type*} [CommRing R] (f h : PowerSeries R) (hh : h.constantCoeff = 0) :
    PowerSeries.coeff 1 (f.subst h) = f.coeff 1 * h.coeff 1 := by
  have hs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' hh
  rw [PowerSeries.coeff_subst' hs, finsum_eq_single _ 1]
  · simp [smul_eq_mul]
  · intro d hd
    rcases Nat.lt_or_gt_of_ne hd with h0 | h2
    · obtain rfl : d = 0 := by omega
      simp
    · obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hh
      rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), smul_zero]

/-- A zero-constant formal right substitution inverse is also a left inverse. -/
theorem substitution_right_inverse_commutes
    (R : Type*) [CommRing R] (f h : PowerSeries R)
    (hh : h.constantCoeff = 0) (hfh : f.subst h = PowerSeries.X) :
    h.subst f = PowerSeries.X := by
  have hs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' hh
  have hf0 : f.constantCoeff = 0 := by
    have h0 := congrArg (PowerSeries.coeff 0) hfh
    rw [PowerSeries.coeff_subst' hs, finsum_eq_single _ 0] at h0
    · simpa using h0
    · intro d hd
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hh, zero_pow hd, smul_zero]
  have h1 := coeff_one_subst_of_constantCoeff_eq_zero f h hh
  rw [hfh, PowerSeries.coeff_one_X] at h1
  have hunit : IsUnit (f.coeff 1) := IsUnit.of_mul_eq_one _ h1.symm
  have hk : (f.substInvOfIsUnit hunit).subst f = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_left f hf0 hunit
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hkh : f.substInvOfIsUnit hunit = h := by
    calc f.substInvOfIsUnit hunit
        = PowerSeries.subst (PowerSeries.X : PowerSeries R) (f.substInvOfIsUnit hunit) :=
          (PowerSeries.X_subst _).symm
      _ = PowerSeries.subst (PowerSeries.subst h f) (f.substInvOfIsUnit hunit) := by rw [hfh]
      _ = PowerSeries.subst h (PowerSeries.subst f (f.substInvOfIsUnit hunit)) :=
          (PowerSeries.subst_comp_subst_apply hfs hs _).symm
      _ = PowerSeries.subst h (PowerSeries.X : PowerSeries R) := by rw [hk]
      _ = h := PowerSeries.subst_X hs
  rw [← hkh]
  exact hk

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The geometric derivative of log(1+X) is the inverse of 1+X. -/
theorem derivative_log_mul_one_add_X :
    PowerSeries.derivative R (PowerSeries.log R) * (1 + PowerSeries.X) = 1 := by
  rw [PowerSeries.deriv_log]
  ext n
  rw [mul_add, mul_one, map_add]
  cases n with
  | zero => simp
  | succ n =>
    rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), ← map_add, pow_succ]
    simp

/-- The formal chain rule gives derivative one for log(exp X). -/
theorem derivative_log_exp_sub_one :
    PowerSeries.derivative R
      ((PowerSeries.log R).subst (PowerSeries.exp R - 1)) = 1 := by
  have hg : PowerSeries.HasSubst (PowerSeries.exp R - 1) := PowerSeries.HasSubst.exp_sub_one
  rw [PowerSeries.derivative_subst R hg, map_sub, PowerSeries.derivative_exp,
    Derivation.map_one_eq_zero, sub_zero]
  have h := congrArg (PowerSeries.subst (PowerSeries.exp R - 1)) (derivative_log_mul_one_add_X R)
  rw [PowerSeries.subst_mul hg, PowerSeries.subst_add hg, PowerSeries.subst_X hg,
    ← PowerSeries.coe_substAlgHom hg, map_one, add_sub_cancel] at h
  rwa [← PowerSeries.coe_substAlgHom hg]

/-- Janusz's first formal identity, before any analytic evaluation. -/
theorem log_exp_sub_one :
    (PowerSeries.log R).subst (PowerSeries.exp R - 1) = PowerSeries.X := by
  haveI : IsAddTorsionFree R := IsAddTorsionFree.of_module_rat R
  apply PowerSeries.derivative.ext
  · rw [derivative_log_exp_sub_one, PowerSeries.derivative_X]
  · rw [PowerSeries.constantCoeff_X]
    exact PowerSeries.constantCoeff_subst_eq_zero
      (by rw [map_sub, map_one, ← PowerSeries.constantCoeff_eq, PowerSeries.constantCoeff_exp,
        sub_self]) _
      PowerSeries.constantCoeff_log

/-- The inverse formal identity for exp(X)-1 and log(1+X). -/
theorem exp_sub_one_log :
    (PowerSeries.exp R - 1).subst (PowerSeries.log R) = PowerSeries.X := by
  exact substitution_right_inverse_commutes R (PowerSeries.log R) (PowerSeries.exp R - 1)
    (by simp [PowerSeries.constantCoeff_exp]) (log_exp_sub_one R)

/-- Janusz's second formal identity, still without a convergence claim. -/
theorem exp_log :
    (PowerSeries.exp R).subst (PowerSeries.log R) = 1 + PowerSeries.X := by
  have h := exp_sub_one_log R
  have h1 : PowerSeries.subst (PowerSeries.log R) (1 : PowerSeries R) = 1 := by
    rw [← PowerSeries.coe_substAlgHom PowerSeries.HasSubst.log, map_one]
  rw [PowerSeries.subst_sub PowerSeries.HasSubst.log, h1] at h
  exact sub_eq_iff_eq_add'.mp h

end Cox.ClassFieldPowerSeries
