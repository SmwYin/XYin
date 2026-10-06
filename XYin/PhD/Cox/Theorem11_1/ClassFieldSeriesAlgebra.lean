/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldSeriesBounds

/-! # Evaluating the formal identities in Janusz V.3.5

All rearrangements use the explicit convergence layer. Rescaling the formal
exponential reduces its addition identity to the checked Cauchy product.
-/

noncomputable section
namespace Cox.ClassFieldConvergentSeries

/-- A continuous division-ring homomorphism transports the literal logarithm series. -/
theorem hasSum_logSeries_map
    {F G : Type*} [DivisionRing F] [DivisionRing G]
    [TopologicalSpace F] [TopologicalSpace G]
    (σ : F →+* G) (hσ : Continuous σ) (x y : F)
    (h : HasSum (fun n : ℕ ↦ (-1 : F) ^ n * x ^ (n + 1) / (n + 1 : ℕ)) y) :
    HasSum (fun n : ℕ ↦ (-1 : G) ^ n * (σ x) ^ (n + 1) / (n + 1 : ℕ)) (σ y) := by
  have h2 := h.map σ hσ
  convert h2 using 1
  funext n
  simp only [Function.comp_apply, map_div₀, map_mul, map_pow, map_neg, map_one, map_natCast]

variable {F : Type*} [NormedField F]

/-- At zero, only the actual constant coefficient contributes. -/
theorem value_at_zero (f : PowerSeries F) : value f 0 = f.constantCoeff := by
  rw [value, tsum_eq_single 0]
  · simp [term, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · intro n hn
    simp [term, zero_pow hn]

/-- Evaluation of the constant-one series is one. -/
theorem value_one (x : F) : value (1 : PowerSeries F) x = 1 := by
  rw [value, tsum_eq_single 0]
  · simp [term]
  · intro m hm
    simp [term, PowerSeries.coeff_one, hm]

/-- Evaluation of the formal variable is the given point. -/
theorem value_X (x : F) : value (PowerSeries.X : PowerSeries F) x = x := by
  rw [value, tsum_eq_single 1]
  · simp [term]
  · intro m hm
    simp [term, PowerSeries.coeff_X, hm]

/-- Equality of the monomials identifies rescaled evaluation at every point. -/
theorem value_rescale (f : PowerSeries F) (a x : F) :
    value (PowerSeries.rescale a f) x = value f (a * x) := by
  unfold value
  refine tsum_congr fun n => ?_
  rw [term, term, PowerSeries.coeff_rescale, mul_pow]
  ring

/-- Scalars of norm at most one preserve the common coefficient bound. -/
theorem coeff_rescale_norm_le (f : PowerSeries F) (C : ℝ)
    (hf : ∀ n, ‖f.coeff n‖ ≤ C ^ n) (a : F) (ha : ‖a‖ ≤ 1) (n : ℕ) :
    ‖(PowerSeries.rescale a f).coeff n‖ ≤ C ^ n := by
  rw [PowerSeries.coeff_rescale, norm_mul, norm_pow]
  calc ‖a‖ ^ n * ‖f.coeff n‖ ≤ 1 * ‖f.coeff n‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) ha) (norm_nonneg _)
    _ ≤ C ^ n := by rw [one_mul]; exact hf n

/-- Summable coefficient families permit addition under evaluation. -/
theorem value_add (f g : PowerSeries F) (x : F)
    (hf : Summable (term f x)) (hg : Summable (term g x)) :
    value (f + g) x = value f x + value g x := by
  calc value (f + g) x = ∑' n, (term f x n + term g x n) :=
        tsum_congr fun n => by rw [term, term, term, map_add, add_mul]
    _ = value f x + value g x := hf.tsum_add hg

/-- Subtracting the constant-one series subtracts one from a convergent value. -/
theorem value_sub_one (f : PowerSeries F) (x : F)
    (hf : Summable (term f x)) :
    value (f - 1) x = value f x - 1 := by
  have h1 : Summable (term (1 : PowerSeries F) x) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by
      rw [Finset.mem_singleton] at hn
      simp [term, PowerSeries.coeff_one, hn]
  calc value (f - 1) x = ∑' n, (term f x n - term 1 x n) :=
        tsum_congr fun n => by rw [term, term, term, map_sub, sub_mul]
    _ = value f x - value 1 x := hf.tsum_sub h1
    _ = value f x - 1 := by rw [value_one]

variable [CharZero F] [hUltra : IsUltrametricDist F] [hComplete : CompleteSpace F]
include hUltra hComplete

/-- The convergent formal exponential converts addition of small elements to multiplication. -/
theorem value_exp_add (p : ℕ) [Fact p.Prime] (hp : ‖(p : F)‖ < 1)
    (x y : F) (hx : ‖(p : F)‖⁻¹ * ‖x‖ < 1)
    (hy : ‖(p : F)‖⁻¹ * ‖y‖ < 1) :
    value (PowerSeries.exp F) (x + y) =
      value (PowerSeries.exp F) x * value (PowerSeries.exp F) y := by
  have hexp := ClassFieldSeriesBounds.coeff_exp_norm_le F p hp
  wlog hxy : ‖y‖ ≤ ‖x‖ generalizing x y
  · rw [add_comm, this y x hy hx (le_of_lt (not_le.mp hxy)), mul_comm]
  rcases eq_or_ne x 0 with rfl | hx0
  · have hy0 : y = 0 := by simpa using hxy
    subst hy0
    simp [value_at_zero, PowerSeries.constantCoeff_exp]
  · have ha1 : ‖y / x‖ ≤ 1 := by
      rw [norm_div]
      exact div_le_one_of_le₀ hxy (norm_nonneg _)
    have h1 := value_mul (PowerSeries.exp F) (PowerSeries.rescale (y / x) (PowerSeries.exp F)) _
      hexp (coeff_rescale_norm_le _ _ hexp _ ha1) x hx
    have h2 : PowerSeries.exp F * PowerSeries.rescale (y / x) (PowerSeries.exp F) =
        PowerSeries.rescale (1 + y / x) (PowerSeries.exp F) := by
      rw [← PowerSeries.exp_mul_exp_eq_exp_add, PowerSeries.rescale_one, RingHom.id_apply]
    rw [h2, value_rescale, value_rescale, add_mul, one_mul, div_mul_cancel₀ y hx0] at h1
    exact h1

/-- Double summability justifies evaluating log(exp X)=X on the common smaller ball. -/
theorem value_log_exp_sub_one (p : ℕ) [Fact p.Prime] (hp : ‖(p : F)‖ < 1)
    (x : F) (hx : (‖(p : F)‖⁻¹) ^ 2 * ‖x‖ < 1) :
    value (PowerSeries.log F) (value (PowerSeries.exp F) x - 1) = x := by
  have hpp : p.Prime := Fact.out
  have hp0 : 0 < ‖(p : F)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hpp.ne_zero)
  have hC : 1 ≤ ‖(p : F)‖⁻¹ := (one_le_inv₀ hp0).mpr hp.le
  have hCx : ‖(p : F)‖⁻¹ * ‖x‖ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)) hx
  have hg₀ : (PowerSeries.exp F - 1).constantCoeff = 0 := by
    simp [PowerSeries.constantCoeff_exp]
  have h := value_subst (PowerSeries.log F) (PowerSeries.exp F - 1) _ hC
    (ClassFieldSeriesBounds.coeff_log_norm_le F p hp)
    (ClassFieldSeriesBounds.coeff_exp_sub_one_norm_le F p hp) hg₀ x hx
  rw [ClassFieldPowerSeries.log_exp_sub_one, value_X,
    value_sub_one _ x (summable_term _ _ (ClassFieldSeriesBounds.coeff_exp_norm_le F p hp) x hCx)]
    at h
  exact h.symm

/-- Evaluating the other formal inverse gives exp(log(1+x))=1+x. -/
theorem value_exp_log (p : ℕ) [Fact p.Prime] (hp : ‖(p : F)‖ < 1)
    (x : F) (hx : (‖(p : F)‖⁻¹) ^ 2 * ‖x‖ < 1) :
    value (PowerSeries.exp F) (value (PowerSeries.log F) x) = 1 + x := by
  have hpp : p.Prime := Fact.out
  have hp0 : 0 < ‖(p : F)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hpp.ne_zero)
  have hC : 1 ≤ ‖(p : F)‖⁻¹ := (one_le_inv₀ hp0).mpr hp.le
  have h := value_subst (PowerSeries.exp F) (PowerSeries.log F) _ hC
    (ClassFieldSeriesBounds.coeff_exp_norm_le F p hp)
    (ClassFieldSeriesBounds.coeff_log_norm_le F p hp) PowerSeries.constantCoeff_log x hx
  have h1 : Summable (term (1 : PowerSeries F) x) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by
      rw [Finset.mem_singleton] at hn
      simp [term, PowerSeries.coeff_one, hn]
  have hX : Summable (term (PowerSeries.X : PowerSeries F) x) :=
    summable_of_ne_finset_zero (s := {1}) fun n hn => by
      rw [Finset.mem_singleton] at hn
      simp [term, PowerSeries.coeff_X, hn]
  rw [ClassFieldPowerSeries.exp_log, value_add _ _ x h1 hX, value_one, value_X] at h
  exact h.symm

end Cox.ClassFieldConvergentSeries
