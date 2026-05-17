/- /-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import XYin.Modularforms.uniformcts

/-!
# Cotangent

This file contains lemmas about the cotangent function, including useful series expansions.
-/

open Real Complex

open scoped UpperHalfPlane

lemma Complex.cot_eq_exp_ratio (z : ℂ) :
    cot z = (Complex.exp (2 * I * z) + 1) / (I * (1 - Complex.exp (2 * I * z))) := by
  rw [Complex.cot, Complex.sin, Complex.cos]
  field_simp
  have h1 : exp (z * I) + exp (-(z * I)) = exp (-(z * I)) * (exp (2 * I * z) + 1) := by
    rw [mul_add, ← Complex.exp_add]
    simp only [mul_one, add_left_inj]
    ring_nf
  have h2 : (exp (-(z * I)) - exp (z * I)) * I = exp (-(z * I)) * (I * (1 - exp (2 * I * z))) := by
    ring_nf
    rw [mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [h1, h2, mul_div_mul_left _ _ (Complex.exp_ne_zero _)]

/- The version one probably wants to use more. -/
lemma Complex.cot_pi_eq_exp_ratio (z : ℂ) :
    cot (π * z) = (Complex.exp (2 * π * I * z) + 1) / (I * (1 - Complex.exp (2 * π * I * z))) := by
  rw [cot_eq_exp_ratio (π * z)]
  ring_nf

/- This is the version one probably wants, which is why the pi's are there. -/
theorem pi_mul_cot_pi_q_exp (z : ℍ) :
    π * cot (π * z) = π * I - 2 * π * I * ∑' n : ℕ, Complex.exp (2 * π * I * z) ^ n := by
  have h1 : π * ((exp (2 * π * I * z) + 1) / (I * (1 - exp (2 * π * I * z)))) =
      -π * I * ((exp (2 * π * I * z) + 1) * (1 / (1 - exp (2 * π * I * z)))) := by
    simp only [div_mul_eq_div_mul_one_div, div_I, one_div, neg_mul, mul_neg, neg_inj]
    ring
  rw [cot_pi_eq_exp_ratio, h1, one_div, (tsum_geometric_of_norm_lt_one
    (UpperHalfPlane.norm_exp_two_pi_I_lt_one z)).symm, add_comm, geom_series_mul_one_add
      (Complex.exp (2 * π * I * (z : ℂ))) (UpperHalfPlane.norm_exp_two_pi_I_lt_one _)]
  ring

section MittagLeffler

open Filter Function Complex Real

open scoped Interval Topology BigOperators Nat Classical Complex

local notation "ℂ_ℤ " => integerComplement

/-- The term in the infinite product for sine. -/
noncomputable def sinTerm (x : ℂ) (n : ℕ) : ℂ := 1 + -x ^ 2 / (n + 1) ^ 2

lemma sinTerm_ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) (n : ℕ) : sinTerm x n ≠ 0 := by
  simp only [sinTerm, ne_eq]
  intro h
  rw [add_eq_zero_iff_eq_neg, neg_div', eq_div_iff] at h
  · simp only [one_mul, neg_neg, sq_eq_sq_iff_eq_or_eq_neg] at h
    rcases h with h1| h2
    · have := not_exists.mp hx (n + 1)
      aesop
    · have := not_exists.mp hx (-(n + 1))
      rw [← neg_eq_iff_eq_neg ] at h2
      rw [← h2] at this
      simp only [neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one,
        Int.cast_natCast, not_true_eq_false] at *
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    exact Nat.cast_add_one_ne_zero n

theorem tendsto_euler_sin_prod' (x : ℂ) (h0 : x ≠ 0) :
    Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, sinTerm x i) atTop
    (𝓝 (sin (π * x) / (π * x))) := by
  rw [show (sin (π * x) / (π * x)) = sin (↑π * x) * (1 / (↑π * x)) by ring]
  apply (Filter.Tendsto.mul_const (b := 1 / (π * x)) (tendsto_euler_sin_prod x)).congr
  intro n
  have : (1 / (π * x)) * (π * x) = 1 := by
    apply div_mul_cancel₀
    have := Real.pi_ne_zero
    aesop
  rw [mul_comm, ← mul_assoc, this, one_mul]
  congr
  ext y
  rw [sub_eq_add_neg, ←neg_div]
  rfl

theorem multipliable_sinTerm (x : ℂ) :
    Multipliable fun i => sinTerm x i := by
  apply Complex.multipliable_one_add_of_summable
  · rw [← summable_norm_iff]
    have := (summable_pow_div_add (x^2) 2 1 (by omega))
    simpa only [norm_div, norm_neg, norm_pow,  Nat.cast_one]


lemma euler_sin_tprod (x : ℂ) (hx : x ∈ ℂ_ℤ) :
    ∏' i : ℕ, sinTerm x i = Complex.sin (π * x) / (π * x) := by
  rw [← Multipliable.hasProd_iff, Multipliable.hasProd_iff_tendsto_nat]
  · apply tendsto_euler_sin_prod' x (by apply integerComplement.ne_zero hx)
  · exact multipliable_sinTerm x
  · exact multipliable_sinTerm x

private lemma sinTerm_bound_aux (Z : Set ℂ_ℤ) (hZ : IsCompact Z) : ∃ u : ℕ → ℝ, Summable u ∧
    ∀ (j : ℕ) z, z ∈ Z → (‖-z.1 ^ 2 / (j + 1) ^ 2‖) ≤ u j := by
  have hf : ContinuousOn (fun x : ℂ_ℤ => ‖(-x.1 ^ 2)‖) Z := by
    apply ContinuousOn.comp
    let g := fun x : ℂ_ℤ => -x.1 ^ 2
    apply Continuous.continuousOn continuous_norm (s := ((g '' Z)))
    apply (ContinuousOn.neg (ContinuousOn.pow (Continuous.continuousOn continuous_subtype_val) 2))
    exact Set.mapsTo_image (fun x ↦ -x.1 ^ 2) Z
  have := IsCompact.bddAbove_image hZ hf
  simp only [bddAbove_def, Set.mem_image, Subtype.exists, exists_and_right, forall_exists_index,
    and_imp] at this
  obtain ⟨s, hs⟩ := this
  use (fun n : ℕ => ‖((s / (n + 1) ^ 2) : ℂ)‖ )
  constructor
  · simpa using summable_pow_div_add (s : ℂ) 2 1 (by omega)
  · intro n x hx
    simp only [norm_div, norm_neg, norm_pow, Complex.norm_real]
    gcongr
    apply le_trans (hs _ x x.2 (by simp [hx]) (by simp)) (le_abs_self s)

theorem tendstoUniformlyOn_compact_euler_sin_prod (Z : Set ℂ_ℤ) (hZ : IsCompact Z) :
    TendstoUniformlyOn
      (fun n : ℕ => fun z : ℂ_ℤ => ∏ j ∈ Finset.range n, sinTerm z j)
        (fun x => (Complex.sin (↑π * x) / (↑π * x))) atTop Z := by
  conv =>
    enter [2]
    ext y
    rw [← euler_sin_tprod y y.2]
  obtain ⟨u, hu, hu2⟩ := sinTerm_bound_aux Z hZ
  apply tendstoUniformlyOn_tprod' hZ hu hu2
  · intro n
    apply ContinuousOn.div_const
    apply (ContinuousOn.neg (ContinuousOn.pow (Continuous.continuousOn continuous_subtype_val) 2))

open Finset

theorem sin_pi_z_ne_zero {z : ℂ} (hz : z ∈ ℂ_ℤ) : Complex.sin (π * z) ≠ 0 := by
  apply Complex.sin_ne_zero_iff.2
  intro k
  rw [mul_comm]
  by_contra h
  simp only [mul_eq_mul_right_iff, ofReal_eq_zero] at h
  cases' h with h h
  · aesop
  · exact Real.pi_ne_zero h

theorem tendsto_logDeriv_euler_sin_div (x : ℂ) (hx : x ∈ ℂ_ℤ) :
    Tendsto (fun n : ℕ =>
      logDeriv (fun z => ∏ j ∈ Finset.range n, sinTerm z j) x)
        atTop (𝓝 <| logDeriv (fun t => (Complex.sin (π * t) / (π * t))) x) := by
  apply logDeriv_tendsto
      (f:= fun n : ℕ => fun z => ∏ j ∈ Finset.range n, sinTerm z j) (s := ℂ_ℤ)
         (by apply isOpen_compl_range_intCast) ⟨x, hx⟩
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact (by apply isOpen_compl_range_intCast)]
    · intro K hK hK2
      have hZ := IsCompact.image (isCompact_iff_isCompact_univ.mp hK2) (continuous_inclusion hK)
      have := tendstoUniformlyOn_compact_euler_sin_prod ((Set.inclusion hK)'' ⊤) hZ
      rw [Metric.tendstoUniformlyOn_iff] at *
      simp only [Set.mem_setOf_eq, Set.image_univ, Set.range_inclusion, gt_iff_lt,
        Set.top_eq_univ, Subtype.forall, eventually_atTop, ge_iff_le] at *
      intro ε hε
      obtain ⟨N, hN⟩ := this ε hε
      refine ⟨N, fun n hn y hy => hN n hn y (by simpa using hK hy) (by aesop)⟩
  · simp only [ eventually_atTop, ge_iff_le]
    refine ⟨1, fun b _ => by simpa using (by simp only [sinTerm]; fun_prop)⟩
  · simp only [ne_eq, div_eq_zero_iff, mul_eq_zero, ofReal_eq_zero, not_or]
    refine ⟨sin_pi_z_ne_zero hx, Real.pi_ne_zero , integerComplement.ne_zero hx⟩

theorem logDeriv_sin_div (z : ℂ) (hz : z ∈ ℂ_ℤ) :
    logDeriv (fun t => (Complex.sin (π * t) / (π * t))) z = π * cot (π * z) - 1 / z := by
  have : (fun t => (Complex.sin (π * t)/ (π * t))) = fun z =>
    (Complex.sin ∘ fun t => π * t) z / (π * z) := by
    ext1
    simp only [Function.comp_apply]
  rw [this, logDeriv_div _ (by apply sin_pi_z_ne_zero hz) ?_
    (DifferentiableAt.comp _ (Complex.differentiableAt_sin) (by fun_prop)) (by fun_prop),
    logDeriv_comp (Complex.differentiableAt_sin) (by fun_prop), Complex.logDeriv_sin,
    deriv_const_mul _ (by fun_prop), deriv_id'', logDeriv_const_mul, logDeriv_id']
  · field_simp [mul_comm]
  · simpa only [ne_eq, ofReal_eq_zero] using Real.pi_ne_zero
  · simp only [ne_eq, mul_eq_zero, ofReal_eq_zero, not_or]
    refine ⟨Real.pi_ne_zero, integerComplement.ne_zero hz⟩

/--The term in the infinite series expansion of cot. -/
noncomputable def cotTerm (x : ℂ) (n : ℕ) : ℂ := 1 / (x - (n + 1)) + 1 / (x + (n + 1))

theorem logDeriv_sinTerm_eq_cotTerm (x : ℂ) (hx: x ∈ ℂ_ℤ) (i : ℕ) :
    logDeriv (fun (z : ℂ) ↦ sinTerm z i) x = cotTerm x i := by
  simp only [sinTerm, logDeriv_apply, deriv_const_add', deriv_div_const, deriv.fun_neg',
    differentiableAt_fun_id, deriv_fun_pow'', Nat.cast_ofNat, Nat.add_one_sub_one, pow_one,
    deriv_id'', mul_one, cotTerm, one_div]
  rw [div_div]
  conv =>
    enter [1,2]
    rw [mul_add, mul_div]
  have : (↑i + 1) ^ 2 * -x ^ 2 / (↑i + 1) ^ 2 =  -x ^ 2 := by
    apply IsUnit.mul_div_cancel_left
    simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    exact Nat.cast_add_one_ne_zero i
  rw [this]
  simp_rw [div_eq_mul_inv]
  have h1 : ((x : ℂ) + (i + 1)) ≠ 0:= by
    simpa using integerComplement_add_ne_zero hx (i + 1)
  have h2 : ((x : ℂ) - (i + 1)) ≠ 0 := by
    rw [sub_eq_add_neg]
    simpa using integerComplement_add_ne_zero hx (-(i + 1))
  field_simp
  have hr : (x - (↑i + 1)) * (↑x + (↑i + 1)) = ↑x ^ 2 - (↑i + 1) ^ 2 := by
    ring
  rw [hr]
  have h4 : (((i + 1 : ℂ)^2) + -x^2) ≠ 0 := by
    rw [show  (((i + 1 : ℂ)^2) + -x^2) = -(((x - (i + 1 : ℂ))) * (x +(((i + 1 : ℂ))))) by ring,
      neg_ne_zero]
    simp only [ne_eq, mul_eq_zero, not_or]
    refine ⟨h2, h1⟩
  field_simp
  ring

lemma logDeriv_of_prod {x : ℂ} (hx : x ∈ ℂ_ℤ) (n : ℕ) :
    logDeriv (fun (z : ℂ) => ∏ j ∈ Finset.range n, sinTerm z j) x =
    ∑ j ∈ Finset.range n, cotTerm x j := by
  rw [logDeriv_prod]
  · congr
    ext i
    apply logDeriv_sinTerm_eq_cotTerm x hx i
  · exact fun i _ ↦ sinTerm_ne_zero hx i
  · intro i _
    simp only [sinTerm, differentiableAt_const, differentiableAt_const_add_iff,
      differentiableAt_fun_neg_iff, differentiableAt_fun_id, DifferentiableAt.fun_pow,
      DifferentiableAt.div_const]

theorem tendsto_logDeriv_euler_cot_sub (x : ℂ) (hx : x ∈ ℂ_ℤ) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, cotTerm x j)
      atTop (𝓝 <| π * cot (π * x)- 1 / x) := by
  simp_rw [← logDeriv_sin_div x hx, ← logDeriv_of_prod hx]
  simpa using tendsto_logDeriv_euler_sin_div x hx

lemma cotTerm_identity (z : ℂ) (hz : z ∈ ℂ_ℤ) (n : ℕ) :
    cotTerm z n = 2 * z * (1 / (z ^ 2 - (n + 1) ^ 2)) := by
  simp only [cotTerm]
  rw [one_div_add_one_div]
  · ring
  · simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hz (-(n + 1) : ℤ)
  · simpa using (integerComplement_add_ne_zero hz ((n : ℤ) + 1))

theorem Summable_cotTerm {z : ℂ} (hz : z ∈ ℂ_ℤ) : Summable fun n : ℕ => cotTerm z n := by
  rw [funext fun n ↦ cotTerm_identity z hz n]
  apply Summable.mul_left
  apply summable_norm_iff.mp
  have := (tendsto_const_div_pow (‖z^2‖) 2 (by omega))
  simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le, dist_zero_right, norm_div, norm_pow,
    Real.norm_eq_abs, _root_.sq_abs, RCLike.norm_natCast] at this
  obtain ⟨B, hB⟩ := this (1/2) (one_half_pos)
  have hB2 : ∀ (n : ℕ), B ≤ n → 1/2 ≤ |‖z‖^2 / n^2 -1| := fun n hn => by
    rw [le_abs']
    left
    linarith [hB n hn]
  apply Summable.comp_nat_add (k := B)
  have hs : Summable fun n : ℕ => (1 / (2 : ℝ) * (n + B + 1) ^ 2)⁻¹ := by
    simp_rw [mul_inv, inv_eq_one_div, add_assoc]
    apply Summable.mul_left
    have := summable_nat_add_iff (f := fun x => 1 / ((x^2) : ℝ)) (B + 1)
    simpa using this
  apply Summable.of_nonneg_of_le (by simp) _ hs
  simp only [ one_div, norm_inv]
  intro b
  have HT := abs_norm_sub_norm_le ((z / (b + B + 1))^2) 1
  have H2 : 2⁻¹ ≤ ‖(z /(b + B + 1))^2 - 1‖ := by
    apply le_trans _ HT
    simp only [ one_div, mul_inv_rev, inv_inv, div_pow, norm_div, norm_pow,
      norm_one] at *
    convert (hB2 (b + B + 1) (by omega))
    norm_cast
  have : z^2 - (((b + B) : ℕ) + 1)^2 = ((z / ((b + B) + 1))^2 - 1) * ((b + B) + 1)^2 := by
      have H3 : ((b : ℂ) + (B : ℂ) + 1)^2 ≠ 0 := by
        norm_cast
        norm_num
      field_simp [H3]
  rw [inv_le_inv₀, this, norm_mul]
  · gcongr
    · norm_cast
  · rw [this, norm_mul]
    apply mul_pos (by linarith)
    simp only [norm_pow]
    apply pow_pos
    refine norm_pos_iff.mpr ?_
    norm_cast
  · simp only [inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    apply pow_pos
    norm_cast
    exact Nat.zero_lt_succ (b + B)

theorem cot_series_rep' {z : ℂ} (hz : z ∈ ℂ_ℤ) : π * Complex.cot (π * z) - 1 / z =
    ∑' n : ℕ, (1 / ((z : ℂ) - (n + 1)) + 1 / (z + (n + 1))) := by
  rw [HasSum.tsum_eq]
  apply (Summable.hasSum_iff_tendsto_nat (Summable_cotTerm hz)).mpr
    (tendsto_logDeriv_euler_cot_sub z hz)

theorem cot_series_rep {z : ℂ} (hz : z ∈ ℂ_ℤ) :
    π * Complex.cot (π * z) = 1 / z + ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) := by
  have := tsum_pnat_eq_tsum_succ fun n => 1 / ((z : ℂ) - n) + 1 / (z + n)
  have h1 := cot_series_rep' hz
  simp only [one_div, Nat.cast_add, Nat.cast_one] at *
  rw [this, ← h1]
  ring

end MittagLeffler
 -/
