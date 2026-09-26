/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Exponential growth and meromorphy at a cusp

Exponential growth is a condition on the upper half plane, independent of a choice of period.
For periodic functions holomorphic sufficiently high in the upper half plane, it is equivalent
to meromorphy of the cusp function at zero.

## Main results

* `UpperHalfPlane.isOfExponentialGrowth_iff_isBigO`: the growth condition as a big-O condition.
* `UpperHalfPlane.IsOfExponentialGrowth.add`, `.mul`, `.neg`, `.sub`, `.smul`, `.pow`, `.const`,
  `.congr`, `.of_isBoundedAtImInfty`: closure properties of the growth condition.
* `UpperHalfPlane.isOfExponentialGrowth_iff_meromorphicAt_cuspFunction`: for periodic functions
  holomorphic near infinity, exponential growth is meromorphy of the cusp function at zero.
-/

open Complex Filter Function Set Asymptotics
open scoped Real Topology UpperHalfPlane Manifold

noncomputable section

namespace UpperHalfPlane

/-- A function has exponential growth at infinity if some nonnegative exponential weight makes
it bounded there. This condition does not involve a choice of period. -/
def IsOfExponentialGrowth (f : ℍ → ℂ) : Prop :=
  ∃ ρ : ℝ, 0 ≤ ρ ∧
    IsBoundedAtImInfty (fun τ ↦ (Real.exp (-ρ * τ.im) : ℂ) * f τ)

/-- Boundedness after multiplication by the weight `exp (-ρ * im τ)` is the big-O condition
`f = O(exp (ρ * im τ))`. -/
theorem isBoundedAtImInfty_exp_mul_iff_isBigO (ρ : ℝ) (f : ℍ → ℂ) :
    IsBoundedAtImInfty (fun τ ↦ (Real.exp (-ρ * τ.im) : ℂ) * f τ) ↔
      f =O[atImInfty] fun τ ↦ Real.exp (ρ * τ.im) := by
  simp only [IsBoundedAtImInfty, BoundedAtFilter, isBigO_iff, Pi.one_apply, norm_one, mul_one,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), neg_mul,
    Real.exp_neg, abs_inv]
  refine exists_congr fun c ↦ eventually_congr (Eventually.of_forall fun τ ↦ ?_)
  rw [inv_mul_le_iff₀ (Real.exp_pos _), mul_comm]

/-- Exponential growth as a big-O condition. -/
theorem isOfExponentialGrowth_iff_isBigO {f : ℍ → ℂ} :
    IsOfExponentialGrowth f ↔ ∃ ρ : ℝ, 0 ≤ ρ ∧ f =O[atImInfty] fun τ ↦ Real.exp (ρ * τ.im) :=
  exists_congr fun ρ ↦ and_congr_right fun _ ↦ isBoundedAtImInfty_exp_mul_iff_isBigO ρ f

/-- Exponential weights on the upper half plane are monotone in the exponent. -/
theorem exp_mul_im_isBigO_exp_mul_im {ρ₁ ρ₂ : ℝ} (h : ρ₁ ≤ ρ₂) :
    (fun τ : ℍ ↦ Real.exp (ρ₁ * τ.im)) =O[atImInfty] fun τ ↦ Real.exp (ρ₂ * τ.im) :=
  IsBigO.of_bound' (Eventually.of_forall fun τ ↦ by
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h τ.im_pos.le))

namespace IsOfExponentialGrowth

variable {f g : ℍ → ℂ}

/-- A big-O bound by any exponential weight gives exponential growth. -/
theorem of_isBigO_exp {ρ : ℝ} (h : f =O[atImInfty] fun τ ↦ Real.exp (ρ * τ.im)) :
    IsOfExponentialGrowth f :=
  isOfExponentialGrowth_iff_isBigO.2
    ⟨max ρ 0, le_max_right _ _, h.trans (exp_mul_im_isBigO_exp_mul_im (le_max_left _ _))⟩

/-- Exponential growth passes to functions which are big-O at infinity. -/
theorem of_isBigO (hf : IsOfExponentialGrowth f) (h : g =O[atImInfty] f) :
    IsOfExponentialGrowth g := by
  obtain ⟨ρ, -, hρ⟩ := isOfExponentialGrowth_iff_isBigO.1 hf
  exact of_isBigO_exp (h.trans hρ)

/-- Exponential growth passes to functions which are eventually dominated in norm. -/
theorem mono (hf : IsOfExponentialGrowth f) (h : ∀ᶠ τ in atImInfty, ‖g τ‖ ≤ ‖f τ‖) :
    IsOfExponentialGrowth g :=
  hf.of_isBigO (IsBigO.of_bound' h)

/-- Exponential growth only depends on the values near infinity. -/
theorem congr (hf : IsOfExponentialGrowth f) (h : f =ᶠ[atImInfty] g) :
    IsOfExponentialGrowth g :=
  hf.of_isBigO (h.symm.isBigO.trans (isBigO_refl _ _))

/-- Bounded functions have exponential growth. -/
theorem of_isBoundedAtImInfty (hf : IsBoundedAtImInfty f) : IsOfExponentialGrowth f :=
  ⟨0, le_rfl, by simpa using hf⟩

theorem const (c : ℂ) : IsOfExponentialGrowth fun _ ↦ c :=
  of_isBoundedAtImInfty (const_boundedAtFilter _ c)

theorem zero : IsOfExponentialGrowth 0 :=
  const 0

theorem one : IsOfExponentialGrowth 1 :=
  const 1

theorem add (hf : IsOfExponentialGrowth f) (hg : IsOfExponentialGrowth g) :
    IsOfExponentialGrowth (f + g) := by
  obtain ⟨ρ₁, -, h₁⟩ := isOfExponentialGrowth_iff_isBigO.1 hf
  obtain ⟨ρ₂, -, h₂⟩ := isOfExponentialGrowth_iff_isBigO.1 hg
  exact of_isBigO_exp ((h₁.trans (exp_mul_im_isBigO_exp_mul_im (le_max_left ρ₁ ρ₂))).add
    (h₂.trans (exp_mul_im_isBigO_exp_mul_im (le_max_right ρ₁ ρ₂))))

theorem neg (hf : IsOfExponentialGrowth f) : IsOfExponentialGrowth (-f) :=
  hf.of_isBigO (isBigO_refl _ _).neg_left

theorem sub (hf : IsOfExponentialGrowth f) (hg : IsOfExponentialGrowth g) :
    IsOfExponentialGrowth (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : IsOfExponentialGrowth f) (hg : IsOfExponentialGrowth g) :
    IsOfExponentialGrowth (f * g) := by
  obtain ⟨ρ₁, -, h₁⟩ := isOfExponentialGrowth_iff_isBigO.1 hf
  obtain ⟨ρ₂, -, h₂⟩ := isOfExponentialGrowth_iff_isBigO.1 hg
  refine of_isBigO_exp (ρ := ρ₁ + ρ₂) ((h₁.mul h₂).congr_right fun τ ↦ ?_)
  rw [← Real.exp_add, add_mul]

theorem smul {R : Type*} [SeminormedRing R] [Module R ℂ] [IsBoundedSMul R ℂ] (c : R)
    (hf : IsOfExponentialGrowth f) : IsOfExponentialGrowth (c • f) :=
  hf.of_isBigO ((isBigO_refl _ _).const_smul_left c)

theorem const_mul (c : ℂ) (hf : IsOfExponentialGrowth f) :
    IsOfExponentialGrowth fun τ ↦ c * f τ :=
  hf.smul c

theorem pow (hf : IsOfExponentialGrowth f) (n : ℕ) : IsOfExponentialGrowth (f ^ n) := by
  induction n with
  | zero => simpa using one
  | succ n ih => simpa only [pow_succ] using ih.mul hf

end IsOfExponentialGrowth

private lemma norm_qParam_pow (h : ℝ) (n : ℕ) (τ : ℍ) :
    ‖Periodic.qParam h τ ^ n‖ = Real.exp (-(2 * Real.pi * n / h) * τ.im) := by
  rw [norm_pow, Periodic.norm_qParam, ← Real.exp_nat_mul]
  change Real.exp ((n : ℝ) * (-2 * Real.pi * τ.im / h)) = _
  congr 1
  ring

private lemma weighted_bound_iff (h : ℝ) (n : ℕ) (f : ℍ → ℂ) :
    IsBoundedAtImInfty (fun τ ↦ (Real.exp (-(2 * Real.pi * n / h) * τ.im) : ℂ) * f τ) ↔
      IsBoundedAtImInfty (fun τ ↦ Periodic.qParam h τ ^ n * f τ) := by
  simp only [isBoundedAtImInfty_iff, norm_mul, norm_qParam_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

private lemma meromorphicAt_zero_of_bounded_pow {g : ℂ → ℂ} (n : ℕ)
    (hd : ∀ᶠ q in 𝓝[≠] 0, DifferentiableAt ℂ g q)
    (hb : BoundedAtFilter (𝓝[≠] 0) (fun q ↦ q ^ n * g q)) :
    MeromorphicAt g 0 := by
  have hz : ZeroAtFilter (𝓝[≠] (0 : ℂ)) (fun q ↦ q) := nhdsWithin_le_nhds
  have ht : Tendsto (fun q ↦ q ^ (n + 1) * g q) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [Pi.mul_apply, pow_succ', mul_assoc] using hz.mul_boundedAtFilter hb
  refine ⟨n + 1, ?_⟩
  simp only [sub_zero, smul_eq_mul]
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [hd] with q hq
    exact (differentiableAt_id.pow (n + 1)).mul hq
  · rw [continuousAt_iff_punctured_nhds]
    simpa using ht

private lemma bounded_pow_cuspFunction {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (n : ℕ)
    (hb : IsBoundedAtImInfty (fun τ ↦ Periodic.qParam h τ ^ n * f τ)) :
    BoundedAtFilter (𝓝[≠] 0) (fun q ↦ q ^ n * cuspFunction h f q) := by
  have ht := tendsto_comap_im_ofComplex.comp (Periodic.invQParam_tendsto hh)
  have hb' := hb.comp_tendsto ht
  refine hb'.congr' ?_ (by simp)
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with q hq hq1
  have hq0 : q ≠ 0 := hq
  have hpos := Periodic.im_invQParam_pos_of_norm_lt_one hh
    (mem_ball_zero_iff.mp hq1) hq0
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hpos, cuspFunction,
    Periodic.cuspFunction_eq_of_nonzero _ _ hq0, Periodic.qParam_right_inv hh.ne' hq0]

/-- Meromorphy of the cusp function gives a period-independent exponential growth bound. -/
theorem isOfExponentialGrowth_of_meromorphicAt_cuspFunction {h : ℝ} (hh : 0 < h)
    {f : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) h)
    (hf : MeromorphicAt (cuspFunction h f) 0) : IsOfExponentialGrowth f := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨2 * Real.pi * n / h, by positivity, (weighted_bound_iff h n f).mpr ?_⟩
  have ht := hn.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)
  have hb := ht.isBigO_one ℝ
  simpa only [Function.comp_def, sub_zero, smul_eq_mul, eq_cuspFunction _ hh.ne' hfper]
    using hb

/-- A periodic function holomorphic sufficiently high in the upper half plane has exponential
growth if and only if its cusp function is meromorphic at zero. -/
theorem isOfExponentialGrowth_iff_meromorphicAt_cuspFunction {h : ℝ} (hh : 0 < h)
    {f : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : ∀ᶠ τ in atImInfty, MDiffAt f τ) :
    IsOfExponentialGrowth f ↔ MeromorphicAt (cuspFunction h f) 0 := by
  refine ⟨fun hf ↦ ?_, isOfExponentialGrowth_of_meromorphicAt_cuspFunction hh hfper⟩
  obtain ⟨ρ, -, hb⟩ := isOfExponentialGrowth_iff_isBigO.1 hf
  obtain ⟨n, hn⟩ := exists_nat_gt (ρ * h / (2 * Real.pi))
  have hρn : ρ ≤ 2 * Real.pi * n / h := by
    apply (le_div_iff₀ hh).mpr
    have := (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hn
    nlinarith
  have hbn : IsBoundedAtImInfty (fun τ ↦ Periodic.qParam h τ ^ n * f τ) :=
    (weighted_bound_iff h n f).1 ((isBoundedAtImInfty_exp_mul_iff_isBigO _ f).2
      (hb.trans (exp_mul_im_isBigO_exp_mul_im hρn)))
  have hd : ∀ᶠ z in comap Complex.im atTop, DifferentiableAt ℂ (f ∘ ofComplex) z := by
    filter_upwards [tendsto_comap_im_ofComplex.eventually hfhol,
      preimage_mem_comap (Ioi_mem_atTop 0)] with z hz hzi
    have := mdifferentiableAt_iff.mp hz
    simpa only [ofComplex_apply_of_im_pos hzi] using this
  exact meromorphicAt_zero_of_bounded_pow n
    (hfper.eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hd)
    (bounded_pow_cuspFunction hh n hbn)

end UpperHalfPlane
