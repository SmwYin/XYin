import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import XYin.Modularforms.qExpansion_lems

open Complex Filter ModularFormClass UpperHalfPlane SlashInvariantFormClass Real Function
open scoped CongruenceSubgroup

variable {h : ℝ} {f : ℍ → ℂ}

-- Question: {F : Type*} [FunLike F ℍ ℂ] (f : F)

local notation "I∞" => comap Complex.im atTop
local notation "𝕢" => Periodic.qParam

noncomputable section

/-- This proof is similar to the Mathlib version. -/
theorem eq_cuspFunction' (τ : ℍ) (hh : h ≠ 0) (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    cuspFunction h f (𝕢 h τ) = f τ := by
  simpa [cuspFunction] using (Periodic.eq_cuspFunction hh hfper τ)

/-- This proof is different from the Mathlib version. -/
theorem differentiableAt_comp_ofComplex'
    (hfhol : ∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z)
    {z : ℂ} (hz : 0 < im z) :
    DifferentiableAt ℂ (f ∘ ofComplex) z :=
  by simpa using hfhol z hz

/-- This proof is similar to the Mathlib version. -/
theorem differentiableAt_cuspFunction' (hh : 0 < h)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hfhol : ∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z)
    (hfbdd : IsBoundedAtImInfty f) {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (cuspFunction h f) q := by
  rcases eq_or_ne q 0 with rfl | hq'
  · exact hfper.differentiableAt_cuspFunction_zero hh
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        (fun z hz ↦ differentiableAt_comp_ofComplex' hfhol hz))
      (hfbdd.comp_tendsto tendsto_comap_im_ofComplex)
  · exact Periodic.qParam_right_inv hh.ne' hq' ▸
      hfper.differentiableAt_cuspFunction hh.ne' <|
        hfhol _ (Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq')

/-- This proof is similar to the Mathlib version. -/
lemma differentiableOn_cuspFunction_ball' (hh : 0 < h)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hfhol : ∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z)
    (hfbdd : IsBoundedAtImInfty f) : DifferentiableOn ℂ (cuspFunction h f) (Metric.ball 0 1) :=
  fun _ hz ↦ (differentiableAt_cuspFunction' hh hfper hfhol hfbdd <| mem_ball_zero_iff.mp hz)
  |>.differentiableWithinAt

/-- This proof is similar to the Mathlib version. -/
lemma hasSum_qExpansion_of_norm_lt' (hh : 0 < h) (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hfhol : ∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z)
    (hfbdd : IsBoundedAtImInfty f) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ ↦ (qExpansion h f).coeff m • q ^ m) (cuspFunction h f q) := by
  convert hasSum_taylorSeries_on_ball (differentiableOn_cuspFunction_ball' hh hfper hfhol hfbdd)
      (by simpa using hq) using 2 with m
  grind [qExpansion_coeff, sub_zero, smul_eq_mul]

/-- This proof is similar to the Mathlib version. -/
lemma hasSum_qExpansion' (hh : 0 < h) (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hfhol : ∀ z : ℂ, 0 < Complex.im z → DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z)
    (hfbdd : IsBoundedAtImInfty f) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion h f).coeff m • 𝕢 h τ ^ m) (f τ) := by
  have : 0 < 2 * π * τ.im / h := by positivity
  have : ‖𝕢 h τ‖ < 1 := by simpa [Periodic.qParam, Complex.norm_exp, neg_div]
  simpa [eq_cuspFunction' τ hh.ne' hfper] using
      hasSum_qExpansion_of_norm_lt' hh hfper hfhol hfbdd this

/-- This proof is different to the Mathlib version. -/
lemma hasSum_cuspFunction_of_hasSum_punctured'
    (hh : 0 < h) {c : ℕ → ℂ}
    (hf : ∀ (τ : ℍ), HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) {q : ℂ} (hq : ‖q‖ < 1)
    (hq1 : q ≠ 0) : HasSum (fun m ↦ c m • q ^ m) (cuspFunction h f q) := by
  have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
  let τ : ℍ := ⟨Periodic.invQParam h q, h1⟩
  have h2 := (Periodic.cuspFunction_eq_of_nonzero h (f ∘ UpperHalfPlane.ofComplex) hq1)
  have : cuspFunction h f q = f τ := by simpa [UpperHalfPlane.ofComplex_apply_of_im_pos h1] using h2
  grind [hf τ, Periodic.qParam_right_inv]

/-- This proof is similar to the Mathlib version. -/
lemma hasFPowerSeriesOnBall_update' (hh : 0 < h) {c : ℕ → ℂ}
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (c m) • 𝕢 h τ ^ m) (f τ)) :
    HasFPowerSeriesOnBall (update (cuspFunction h f) 0 (c 0)) (.ofScalars ℂ c) 0 1 := by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
    rcases eq_or_ne r 0 with rfl | hr'
    · simp
    · lift r to NNReal using hr.ne_top
      apply FormalMultilinearSeries.le_radius_of_summable
      simpa [norm_smul] using (hasSum_cuspFunction_of_hasSum_punctured' hh hf (q := r)
        (by simpa using hr) (mod_cast hr')).summable.norm
  · simp
  · intro y hy
    rw [zero_add]
    -- note the `simp`s below do not automatically apply this lemma to the argument of
    -- `Function.update`, because of limitations in `simp`'s support for dependent function types,
    -- see lean4 issue #12478.
    rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hy
    rcases eq_or_ne y 0 with rfl | hy'
    · simpa +contextual [zero_pow_eq] using hasSum_ite_eq 0 (c 0)
    · simpa [update_of_ne hy', mul_comm]
        using hasSum_cuspFunction_of_hasSum_punctured' hh hf hy hy'

/-- This proof is similar to the Mathlib version. -/
lemma hasFPowerSeriesOnBall_cuspFunction' {c : ℕ → ℂ} (hh : 0 < h)
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) :
    HasFPowerSeriesOnBall (cuspFunction h f) (.ofScalars ℂ c) 0 1 := by
  -- previous lemma gives result after updating at 0
  have H1 : HasFPowerSeriesOnBall (update (cuspFunction h f) 0 (c 0)) (.ofScalars ℂ c) 0 1 :=
    hasFPowerSeriesOnBall_update' hh hf
  -- now just need to check values at 0 match
  -- use continuity of both functions & we know it everywhere else
  have H2 : c 0 = cuspFunction h f 0 := by
    have L1 := H1.hasFPowerSeriesAt.continuousAt
    have L2 := hfanalytic.continuousAt
    have := (L1.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE L2).mp <|
      by filter_upwards [self_mem_nhdsWithin] with a ha using update_of_ne ha ..
    simpa [update_self] using this.eq_of_nhds
  rwa [update_eq_self_iff.mpr H2] at H1

/-- This proof is different to the Mathlib version. -/
lemma hasFPowerSeries_cuspFunction' {c : ℕ → ℂ}
    (hh : 0 < h) (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) :
    HasFPowerSeriesOnBall (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 1 := by
  have h1 : HasFPowerSeriesAt (cuspFunction h f) (.ofScalars ℂ c) 0 :=
    (hasFPowerSeriesOnBall_cuspFunction' hh hfanalytic hf).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 := by
    simpa [qExpansionFormalMultilinearSeries, qExpansion_coeff, div_eq_mul_inv, mul_comm]
      using hfanalytic.hasFPowerSeriesAt
  simpa [h1.eq_formalMultilinearSeries h2]
    using hasFPowerSeriesOnBall_cuspFunction' hh hfanalytic hf

/-- This proof is similar to the Mathlib version. -/
lemma qExpansion_coeff_unique' {c : ℕ → ℂ} (hh : 0 < h)
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) (m : ℕ) :
    c m = (qExpansion h f).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction' hh hfanalytic hf).hasFPowerSeriesAt
  have h2 := (hasFPowerSeries_cuspFunction' hh hfanalytic hf).hasFPowerSeriesAt
  simpa using congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

end

section

variable {k : ℤ} {F G : Type*} [FunLike F ℍ ℂ] [FunLike G ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ}
  (f : F) (g : G)

lemma ModularForm.qExpansion_coeff_unique {c : ℕ → ℂ} (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {f : F} [ModularFormClass F Γ k]
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) (m : ℕ) :
    c m = (qExpansion h f).coeff m := by
  exact qExpansion_coeff_unique' (h := h) (f := f) hh
    (analyticAt_cuspFunction_zero f hh hΓ) hf m

lemma qExpansion_add' {f g : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    qExpansion h (f + g) = qExpansion h f + qExpansion h g := by
  ext m
  simp [qExpansion_coeff, cuspFunction_add hf.continuousAt hg.continuousAt,
    iteratedDeriv_add hf.contDiffAt hg.contDiffAt, mul_add]

lemma ModularForm.qExpansion_add
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {a b : ℤ}
    [ModularFormClass F Γ a] [ModularFormClass G Γ b] :
    qExpansion h (f + g) = qExpansion h f + qExpansion h g :=
    qExpansion_add' (analyticAt_cuspFunction_zero f hh hΓ) (analyticAt_cuspFunction_zero g hh hΓ)

lemma qExpansion_smul' {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0)
    (a : ℂ) :
    qExpansion h (a • f) = a • qExpansion h f := by
  ext m
  simp [qExpansion_coeff, cuspFunction_smul hf.continuousAt, iteratedDeriv_const_smul_field,
    mul_left_comm]

lemma ModularForm.qExpansion_smul
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (a : ℂ)
    (f : F) [ModularFormClass F Γ k] :
    qExpansion h (a • f) = a • qExpansion h f :=
    qExpansion_smul' (analyticAt_cuspFunction_zero f hh hΓ) a

lemma qExpansion_neg' {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    qExpansion h (-f) = -qExpansion h f := by
  simpa using qExpansion_smul' hf (-1 : ℂ)

lemma ModularForm.qExpansion_neg
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : F) [ModularFormClass F Γ k] :
    qExpansion h (-f) = -qExpansion h f :=
  qExpansion_neg' (analyticAt_cuspFunction_zero f hh hΓ)

lemma qExpansion_sub' {f g : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    qExpansion h (f - g) = qExpansion h f - qExpansion h g := by
  have hg' : AnalyticAt ℂ (cuspFunction h (-g)) 0 := by
    simpa [cuspFunction_neg hg.continuousAt] using hg.neg
  simpa [sub_eq_add_neg, qExpansion_neg' hg] using
    (qExpansion_add' hf hg')

lemma ModularForm.qExpansion_sub (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {a b : ℤ}
    (f : ModularForm Γ a) (g : ModularForm Γ b) :
    qExpansion h (f - g) = qExpansion h f - qExpansion h g :=
  qExpansion_sub' (analyticAt_cuspFunction_zero f hh hΓ) (analyticAt_cuspFunction_zero g hh hΓ)

end

#min_imports
