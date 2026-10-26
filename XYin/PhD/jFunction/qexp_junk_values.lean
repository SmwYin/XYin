/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.SqrtDeriv
import XYin.PhD.jFunction.jfunction

/-!
# Values of q-expansions outside their analytic hypotheses

The definition of `qExpansion` is total. At a nonpositive period its coefficients come from
the fallback point of `UpperHalfPlane.ofComplex`, rather than from the cusp at infinity.
At a meromorphic pole, all positive iterated derivatives are totalized to zero, so the ordinary
q-expansion retains only the fallback constant chosen by `limUnder`.

At period `1 / 2`, the cusp function of `Δ` is its genuine cusp function composed with the
principal square root. It tends to zero but is not differentiable on the nearby nonpositive
real axis. The resulting ordinary q-expansion is the zero series.

The four examples are `qExpansion_zero_discriminant`, `qExpansion_neg_one_discriminant`,
`qExpansion_half_discriminant`, and `qExpansion_one_j`.

The fallback point in `ℍ` and the fallback value in `ℂ` are classical choices; neither is
identified with an inhabited default such as `I` or `0`.
-/

open Complex Filter Function ModularForm UpperHalfPlane
open scoped Topology

noncomputable section

namespace UpperHalfPlane

/-- For a nonpositive period, the cusp function is locally the value at the fallback point. -/
lemma cuspFunction_eventuallyEq_const_of_nonpos {h : ℝ} (hh : h ≤ 0) (f : ℍ → ℂ) :
    cuspFunction h f =ᶠ[𝓝 (0 : ℂ)] fun _ ↦ f (ofComplex 0) := by
  have hEq : cuspFunction h f =ᶠ[𝓝[≠] (0 : ℂ)] fun _ ↦ f (ofComplex 0) := by
    filter_upwards [eventually_ne_zero_and_norm_lt_one] with q hq
    have him : (Periodic.invQParam h q).im ≤ 0 := by
      rw [Periodic.im_invQParam]
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (neg_nonneg.mpr hh) (by positivity))
        (Real.log_nonpos (norm_nonneg _) hq.2.le)
    rw [cuspFunction_apply_of_ne_zero h f hq.1,
      ofComplex_apply_eq_of_im_nonpos (w' := (0 : ℂ)) him (by simp)]
  exact eventuallyEq_nhds_of_eventuallyEq_nhdsNE hEq
    (cuspFunction_apply_zero_eq hEq continuousAt_const)

/-- At a nonpositive period, a q-expansion is a constant series at the fallback point. -/
theorem qExpansion_of_nonpos {h : ℝ} (hh : h ≤ 0) (f : ℍ → ℂ) :
    qExpansion h f = PowerSeries.C (f (ofComplex 0)) := by
  ext n
  rw [qExpansion_coeff,
    (cuspFunction_eventuallyEq_const_of_nonpos hh f).iteratedDeriv_eq n]
  rcases eq_or_ne n 0 with rfl | hn <;>
    simp [iteratedDeriv_const, PowerSeries.coeff_C, *]

end UpperHalfPlane

/-- The zero-period q-expansion of `Δ` is the fallback constant series. -/
theorem qExpansion_zero_discriminant :
    qExpansion 0 discriminant = PowerSeries.C (discriminant (ofComplex 0)) :=
  qExpansion_of_nonpos le_rfl _

/-- The negative-one-period q-expansion of `Δ` is the same fallback constant series. -/
theorem qExpansion_neg_one_discriminant :
    qExpansion (-1) discriminant = PowerSeries.C (discriminant (ofComplex 0)) :=
  qExpansion_of_nonpos (by norm_num) _

/-- Differentiating a meromorphic pole at zero lowers its order by one. -/
lemma meromorphicOrderAt_deriv_at_zero_of_neg {f : ℂ → ℂ} {m : ℤ}
    (hf : MeromorphicAt f 0) (hm : m < 0)
    (ho : meromorphicOrderAt f 0 = (m : WithTop ℤ)) :
    meromorphicOrderAt (deriv f) 0 = ((m - 1 : ℤ) : WithTop ℤ) := by
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp ho
  have hfg' : f =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦ z ^ m * g z := by
    filter_upwards [hfg] with z hz
    simpa only [sub_zero, smul_eq_mul] using hz
  refine (meromorphicOrderAt_eq_int_iff hf.deriv).mpr
    ⟨fun z ↦ (m : ℂ) * g z + z * deriv g z, ?_, ?_, ?_⟩
  · exact (analyticAt_const.mul hg).add (analyticAt_id.mul hg.deriv)
  · simpa using mul_ne_zero (Int.cast_ne_zero.mpr hm.ne) hg0
  · filter_upwards [hfg'.nhdsNE_deriv,
      eventually_nhdsWithin_of_eventually_nhds hg.eventually_analyticAt,
      self_mem_nhdsWithin] with z hz hgz (hz0 : z ≠ 0)
    rw [hz, deriv_fun_mul (c := fun z : ℂ ↦ z ^ m)
      (differentiableAt_zpow.mpr (Or.inl hz0))
      hgz.differentiableAt, deriv_zpow]
    simp only [sub_zero, smul_eq_mul]
    have hzpow : z ^ m = z ^ (m - 1) * z := by
      simpa only [sub_add_cancel, zpow_one] using zpow_add₀ hz0 (m - 1) 1
    rw [hzpow]
    ring

/-- Every positive iterated derivative is totalized to zero at a meromorphic pole. -/
lemma iteratedDeriv_eq_zero_at_pole {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (ho : meromorphicOrderAt f 0 < 0) (n : ℕ) : iteratedDeriv (n + 1) f 0 = 0 := by
  have horders : ∀ n : ℕ, MeromorphicAt (iteratedDeriv n f) 0 ∧
      meromorphicOrderAt (iteratedDeriv n f) 0 < 0 := by
    intro k
    induction k with
    | zero => simpa using And.intro hf ho
    | succ k ih =>
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ih.2.ne_top
      have hmneg : m < 0 := by simpa [← hm] using ih.2
      rw [iteratedDeriv_succ]
      refine ⟨ih.1.deriv, ?_⟩
      rw [meromorphicOrderAt_deriv_at_zero_of_neg ih.1 hmneg hm.symm]
      exact_mod_cast (show m - 1 < 0 by omega)
  rw [iteratedDeriv_succ]
  apply deriv_zero_of_not_differentiableAt
  intro hd
  exact (not_le.mpr (horders n).2)
    ((tendsto_nhds_iff_meromorphicOrderAt_nonneg (horders n).1).mp
      ⟨iteratedDeriv n f 0, hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩)

/-- At a pole, the ordinary q-expansion keeps only the assigned value at zero. -/
lemma qExpansion_eq_C_of_pole {h : ℝ} {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (ho : meromorphicOrderAt (cuspFunction h f) 0 < 0) :
    qExpansion h f = PowerSeries.C (cuspFunction h f 0) := by
  ext n
  cases n with
  | zero => simp [qExpansion_coeff]
  | succ n => simp [qExpansion_coeff, iteratedDeriv_eq_zero_at_pole hf ho n]

/-- The ordinary q-expansion of `j` is constant, despite its genuine Laurent leading term. -/
theorem qExpansion_one_j_eq_C_cuspFunction :
    qExpansion 1 j = PowerSeries.C (cuspFunction 1 j 0) := by
  apply qExpansion_eq_C_of_pole j_cuspFunction_meromorphicAt
  rw [meromorphicOrderAt_cuspFunction_eq_neg_poleOrder (by simp [j_poleOrder]),
    j_poleOrder]
  exact_mod_cast (show (-1 : ℤ) < 0 by norm_num)

/-- At a pole there is no finite limit, so the value at zero is the fallback classical choice. -/
lemma cuspFunction_zero_eq_choice_of_pole {h : ℝ} {f : ℍ → ℂ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (ho : meromorphicOrderAt (cuspFunction h f) 0 < 0) :
    cuspFunction h f 0 = Classical.choice (inferInstance : Nonempty ℂ) := by
  change Periodic.cuspFunction h (f ∘ ofComplex) 0 = _
  rw [Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
  apply limUnder_of_not_tendsto
  change ¬ ∃ c, Tendsto (cuspFunction h f) (𝓝[≠] (0 : ℂ)) (𝓝 c)
  rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg hf]
  exact not_le.mpr ho

/-- The ordinary width-one q-expansion of `j` is the arbitrary fallback constant series. -/
theorem qExpansion_one_j :
    qExpansion 1 j = PowerSeries.C (Classical.choice (inferInstance : Nonempty ℂ)) := by
  rw [qExpansion_one_j_eq_C_cuspFunction,
    cuspFunction_zero_eq_choice_of_pole j_cuspFunction_meromorphicAt]
  rw [meromorphicOrderAt_cuspFunction_eq_neg_poleOrder (by simp [j_poleOrder]),
    j_poleOrder]
  exact_mod_cast (show (-1 : ℤ) < 0 by norm_num)

open Set

/-- Squaring the principal complex square root recovers its argument. -/
private lemma sqrt_sq_eq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  simp [Complex.sqrt]

/-- The principal square root lies in the closed right half-plane. -/
private lemma re_sqrt_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  rw [Complex.sqrt_eq_real_add_ite]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero, Complex.I_re, Complex.I_im,
    zero_sub]
  split_ifs <;> simpa using Real.sqrt_nonneg ((‖z‖ + z.re) / 2)

/-- The principal complex square root is not differentiable on the nonpositive real axis. -/
lemma not_differentiableAt_sqrt_ofReal {x : ℝ} (hx : x ≤ 0) :
    ¬ DifferentiableAt ℂ Complex.sqrt (x : ℂ) := by
  intro h
  have hre : (Complex.sqrt (x : ℂ)).re = 0 := by
    rw [Complex.re_sqrt_ofReal, Real.sqrt_eq_zero_of_nonpos hx]
  have hmin : IsLocalMin (fun t : ℝ ↦ (Complex.sqrt ((x : ℂ) + (t : ℂ) * Complex.I)).re) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, hre] using
      re_sqrt_nonneg ((x : ℂ) + (t : ℂ) * Complex.I)
  have hd := h.hasDerivAt.comp_of_eq 0
    (((hasDerivAt_id (0 : ℂ)).mul_const Complex.I).const_add (x : ℂ)) (by simp)
  have him : (deriv Complex.sqrt (x : ℂ)).im = 0 := by
    have hzero := hmin.hasDerivAt_eq_zero (by simpa using hd.real_of_complex)
    simpa using hzero
  have hsquare := h.hasDerivAt.fun_pow 2
  have hid : HasDerivAt (fun z : ℂ ↦ z)
      (2 * Complex.sqrt (x : ℂ) * deriv Complex.sqrt (x : ℂ)) (x : ℂ) := by
    simpa [Pi.pow_apply, sqrt_sq_eq] using hsquare
  have heq := hid.unique (hasDerivAt_id (x : ℂ))
  have := congrArg Complex.re heq
  simp [mul_re, hre, him] at this

/-- The half-period cusp function is the genuine discriminant cusp function at `sqrt q`. -/
lemma cusp_discriminant_half_eq_sqrt {q : ℂ} (hq : ‖q‖ < 1) :
    cuspFunction (1 / 2 : ℝ) ModularForm.discriminant q =
      cuspFunction 1 ModularForm.discriminant (Complex.sqrt q) := by
  by_cases hq0 : q = 0
  · subst q
    simp only [Complex.sqrt_zero,
      ModularForm.discriminant_isZeroAtImInfty.cuspFunction_apply_zero
        (by norm_num : (0 : ℝ) < 1 / 2),
      ModularForm.discriminant_isZeroAtImInfty.cuspFunction_apply_zero zero_lt_one]
  have him := Function.Periodic.im_invQParam_pos_of_norm_lt_one
    (by norm_num : (0 : ℝ) < 1 / 2) hq hq0
  let τ : ℍ := ⟨Function.Periodic.invQParam (1 / 2 : ℝ) q, him⟩
  have hqτ : Function.Periodic.qParam 1 τ = Complex.sqrt q := by
    rw [sqrt_eq_exp hq0]
    apply congrArg Complex.exp
    dsimp [Function.Periodic.qParam, τ, Function.Periodic.invQParam]
    push_cast
    field_simp [Complex.I_ne_zero, Real.pi_ne_zero]
  rw [← hqτ]
  have heq := SlashInvariantFormClass.eq_cuspFunction CuspForm.discriminant τ
    one_mem_strictPeriods_SL one_ne_zero
  change cuspFunction 1 ModularForm.discriminant _ = _ at heq
  rw [heq]
  simp only [UpperHalfPlane.cuspFunction,
    Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0, Function.comp_apply,
    ofComplex_apply_of_im_pos him]
  rfl

/-- The genuine cusp function of the discriminant is analytic at zero. -/
lemma analyticAt_discriminant_cusp_one :
    AnalyticAt ℂ (cuspFunction 1 ModularForm.discriminant) 0 := by
  simpa only [CuspForm.coe_discriminant] using
    ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
      one_mem_strictPeriods_SL

/-- The first coefficient of the genuine discriminant expansion is one. -/
lemma deriv_discriminant_cusp_one :
    deriv (cuspFunction 1 ModularForm.discriminant) 0 = 1 := by
  simpa [qExpansion_coeff] using ModularForm.discriminant_qExpansion_coeff_one

/-- The square-root identity also holds as an ordinary germ, including the value at zero. -/
lemma cusp_discriminant_half_eventuallyEq_sqrt :
    cuspFunction (1 / 2 : ℝ) ModularForm.discriminant =ᶠ[𝓝 0]
      fun q ↦ cuspFunction 1 ModularForm.discriminant (Complex.sqrt q) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
  exact cusp_discriminant_half_eq_sqrt (by simpa using hq)

/-- An analytic outer function with nonzero derivative cannot hide a failure of differentiability
of the inner function near zero. Only continuity of the inner function at zero is needed. -/
lemma eventually_differentiableAt_of_analytic_comp {A g F : ℂ → ℂ}
    (hA : AnalyticAt ℂ A 0) (hA' : deriv A 0 ≠ 0)
    (hg : ContinuousAt g 0) (hg0 : g 0 = 0)
    (hF : F =ᶠ[𝓝 0] fun q ↦ A (g q)) :
    ∀ᶠ q in 𝓝 0, DifferentiableAt ℂ F q → DifferentiableAt ℂ g q := by
  let B := hA.hasStrictDerivAt.localInverse A (deriv A 0) 0 hA'
  have hB : AnalyticAt ℂ B (A 0) := hA.analyticAt_localInverse hA'
  have hgt : Tendsto g (𝓝 0) (𝓝 0) := by simpa only [hg0] using hg.tendsto
  have hBg : (fun q ↦ B (F q)) =ᶠ[𝓝 0] g := by
    filter_upwards [hF, hgt.eventually (hA.hasStrictDerivAt.eventually_left_inverse hA')]
      with q hFq hBq
    simpa only [hFq, B, Function.comp_def] using hBq
  have hBa : ∀ᶠ q in 𝓝 0, AnalyticAt ℂ B (A (g q)) :=
    (hA.continuousAt.tendsto.comp hgt).eventually hB.eventually_analyticAt
  filter_upwards [hBg.eventually_nhds, hBa, hF] with q hBgq hBq hFq hFd
  have hBgq' : (fun z ↦ B (F z)) =ᶠ[𝓝 q] g := hBgq
  rw [← hFq] at hBq
  exact (hBq.differentiableAt.comp q hFd).congr_of_eventuallyEq hBgq'.symm

/-- Vanishing on a real interval forces the totalized complex derivative to vanish there. -/
lemma deriv_eq_zero_of_eqOn_real_Ioc {f : ℂ → ℂ} {a b x : ℝ}
    (hf : ∀ y ∈ Ioc a b, f (y : ℂ) = 0) (hx : x ∈ Ioc a b) :
    deriv f (x : ℂ) = 0 := by
  apply deriv_zero_of_frequently_const (c := (0 : ℂ))
  have ht : Tendsto (fun y : ℝ ↦ (y : ℂ)) (𝓝[<] x) (𝓝[≠] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj] using ne_of_lt hy
  apply ht.frequently
  apply Filter.Eventually.frequently
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds hx.1)] with y hy hya
  exact hf y ⟨hya, le_trans (le_of_lt hy) hx.2⟩

/-- Vanishing on a real interval propagates to every totalized complex derivative. -/
lemma iteratedDeriv_eq_zero_of_eqOn_real_Ioc {f : ℂ → ℂ} {a b : ℝ}
    (hf : ∀ y ∈ Ioc a b, f (y : ℂ) = 0) (n : ℕ) :
    ∀ x ∈ Ioc a b, iteratedDeriv n f (x : ℂ) = 0 := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact fun x hx ↦ deriv_eq_zero_of_eqOn_real_Ioc ih hx

/-- The half-period q-expansion of `Δ` is zero: its cusp function tends to zero, and its
nondifferentiability on the nearby nonpositive real axis kills every positive coefficient. -/
theorem qExpansion_half_discriminant :
    qExpansion (1 / 2 : ℝ) ModularForm.discriminant = 0 := by
  have ht := eventually_differentiableAt_of_analytic_comp
    analyticAt_discriminant_cusp_one
    (by rw [deriv_discriminant_cusp_one]; exact one_ne_zero)
    (Complex.continuousAt_sqrt (Or.inl le_rfl)) Complex.sqrt_zero
    cusp_discriminant_half_eventuallyEq_sqrt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ht
  have hderiv : ∀ x ∈ Ioc (-ε) 0,
      deriv (cuspFunction (1 / 2 : ℝ) ModularForm.discriminant) (x : ℂ) = 0 := by
    intro x hx
    apply deriv_zero_of_not_differentiableAt
    intro hd
    apply not_differentiableAt_sqrt_ofReal hx.2
    apply hball ?_ hd
    simp only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos hx.2]
    linarith [hx.1]
  ext n
  rw [qExpansion_coeff, map_zero]
  cases n with
  | zero =>
      simpa using ModularForm.discriminant_isZeroAtImInfty.cuspFunction_apply_zero
        (by norm_num : (0 : ℝ) < 1 / 2)
  | succ n =>
      rw [iteratedDeriv_succ']
      have hz := iteratedDeriv_eq_zero_of_eqOn_real_Ioc hderiv n 0
        (show (0 : ℝ) ∈ Ioc (-ε) 0 from ⟨neg_neg_of_pos hε, le_rfl⟩)
      simpa using congrArg (fun z : ℂ ↦ (↑(n + 1).factorial)⁻¹ * z) hz
