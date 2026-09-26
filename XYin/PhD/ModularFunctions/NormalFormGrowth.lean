/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Meromorphic.NormalForm
import XYin.PhD.ModularFunctions.CuspGrowth

/-!
# Exponential growth excludes poles near infinity

A meromorphic function in normal form is analytic wherever it is locally bounded. In particular,
an exponential bound on an upper half-plane excludes poles sufficiently high in the half-plane.
-/

open Filter Asymptotics

open scoped Topology UpperHalfPlane Manifold

/-- A locally bounded meromorphic function in normal form is analytic. -/
lemma MeromorphicNFAt.analyticAt_of_eventually_norm_le {f : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicNFAt f x) (hbound : ∃ C : ℝ, ∀ᶠ z in 𝓝 x, ‖f z‖ ≤ C) :
    AnalyticAt ℂ f x := by
  apply hf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra horder
  have ht := tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge horder)
  rw [← tendsto_norm_atTop_iff_cobounded] at ht
  obtain ⟨C, hC⟩ := hbound
  obtain ⟨z, hz, hz'⟩ := ((hC.filter_mono nhdsWithin_le_nhds).and
    (ht.eventually (eventually_gt_atTop C))).exists
  exact (not_lt_of_ge hz) hz'

namespace UpperHalfPlane

/-- A function holomorphic near infinity is analytic near infinity. -/
theorem eventually_analyticAt_of_eventually_mdifferentiableAt {f : ℍ → ℂ}
    (h : ∀ᶠ τ in atImInfty, MDiffAt f τ) :
    ∀ᶠ τ : ℍ in atImInfty, AnalyticAt ℂ (f ∘ ofComplex) τ := by
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 h
  have hV : IsOpen {z : ℂ | max A 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hd : DifferentiableOn ℂ (f ∘ ofComplex) {z : ℂ | max A 0 < z.im} := fun z hz ↦ by
    have hz0 : 0 < z.im := (le_max_right _ _).trans_lt hz
    exact (mdifferentiableAt_iff.1 (hA ⟨z, hz0⟩ ((le_max_left _ _).trans hz.le)))
      |>.differentiableWithinAt
  refine (atImInfty_mem _).2 ⟨max A 0 + 1, fun τ hτ ↦ hd.analyticAt (hV.mem_nhds ?_)⟩
  change max A 0 < τ.im
  linarith

/-- A meromorphic function in normal form with exponential growth is analytic sufficiently high
in the upper half-plane. -/
lemma eventually_analyticAt_of_meromorphicNFOn_of_isOfExponentialGrowth {f : ℍ → ℂ}
    (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet) (hbound : IsOfExponentialGrowth f) :
    ∀ᶠ τ : ℍ in atImInfty, AnalyticAt ℂ (f ∘ ofComplex) τ := by
  obtain ⟨ρ, hρ, hb⟩ := isOfExponentialGrowth_iff_isBigO.1 hbound
  obtain ⟨c, hc0, hc⟩ := hb.exists_pos
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 hc.bound
  refine (atImInfty_mem _).2 ⟨A + 1, fun τ hτ ↦ (hf τ.im_pos).analyticAt_of_eventually_norm_le
    ⟨c * Real.exp (ρ * (τ.im + 1)), ?_⟩⟩
  have hA' : A < τ.im := by linarith
  filter_upwards [continuousAt_const.eventually_lt Complex.continuous_im.continuousAt hA',
    continuousAt_const.eventually_lt Complex.continuous_im.continuousAt τ.im_pos,
    Complex.continuous_im.continuousAt.eventually_lt continuousAt_const (lt_add_one τ.im)]
    with z hzA hz hz1
  have hbz : ‖f ⟨z, hz⟩‖ ≤ c * Real.exp (ρ * z.im) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hA ⟨z, hz⟩ hzA.le
  rw [Function.comp_apply, ofComplex_apply_of_im_pos hz]
  exact hbz.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz1.le hρ)) hc0.le)

/-- An exponential bound excludes poles near infinity for a meromorphic function in normal form. -/
lemma eventually_mdifferentiableAt_of_meromorphicNFOn_of_exponential_bound {f : ℍ → ℂ}
    (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet) (hbound : IsOfExponentialGrowth f) :
    ∀ᶠ τ in atImInfty, MDiffAt f τ :=
  (eventually_analyticAt_of_meromorphicNFOn_of_isOfExponentialGrowth hf hbound).mono
    fun _ h ↦ mdifferentiableAt_iff.2 h.differentiableAt

end UpperHalfPlane
