import XYin.PhD.Test.MMeromorphic.Field
import Mathlib.Analysis.Meromorphic.Complex

/-!
# Bounds and analytic normal representatives

Meromorphic normal form fixes the value at a removable singularity. A finite punctured
norm bound therefore implies analyticity at the center. The normal form hypothesis matters:
changing a single value preserves raw meromorphicity and may destroy analyticity.
-/

open Filter Topology Set

namespace MMeromorphicTest.BoundedNormalForm

/-- A locally bounded meromorphic normal representative is analytic. -/
theorem analyticAt_of_eventually_norm_le {f : ℂ → ℂ} {z : ℂ} {C : ℝ}
    (hf : MeromorphicNFAt f z) (hbound : ∀ᶠ w in 𝓝[≠] z, ‖f w‖ ≤ C) :
    AnalyticAt ℂ f z := by
  apply hf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra! hneg
  have ht : Tendsto (fun w ↦ ‖f w‖) (𝓝[≠] z) atTop :=
    tendsto_norm_atTop_iff_cobounded.mpr (tendsto_cobounded_of_meromorphicOrderAt_neg hneg)
  obtain ⟨w, hwlarge, hwbound⟩ := ((ht.eventually (eventually_gt_atTop C)).and hbound).exists
  exact (not_le_of_gt hwlarge) hwbound

/-- A continuous upper bound is locally finite, so it also rules out a pole. -/
theorem analyticAt_of_eventually_norm_le_continuousAt {f : ℂ → ℂ} {g : ℂ → ℝ} {z : ℂ}
    (hf : MeromorphicNFAt f z) (hg : ContinuousAt g z)
    (hbound : ∀ᶠ w in 𝓝[≠] z, ‖f w‖ ≤ g w) : AnalyticAt ℂ f z := by
  have hgBound : ∀ᶠ w in 𝓝 z, g w < g z + 1 :=
    hg.eventually_lt continuousAt_const (lt_add_one (g z))
  apply analyticAt_of_eventually_norm_le hf (C := g z + 1)
  filter_upwards [hbound, hgBound.filter_mono nhdsWithin_le_nhds] with w hw hgw
  exact hw.trans hgw.le

/-- A normal representative bounded by a continuous function on an open set is analytic there. -/
theorem analyticOnNhd_of_norm_le {f : ℂ → ℂ} {g : ℂ → ℝ} {U : Set ℂ}
    (hf : MeromorphicNFOn f U) (hU : IsOpen U) (hg : ContinuousOn g U)
    (hbound : ∀ z ∈ U, ‖f z‖ ≤ g z) : AnalyticOnNhd ℂ f U := by
  intro z hz
  apply analyticAt_of_eventually_norm_le_continuousAt (hf hz)
    ((hg z hz).continuousAt (hU.mem_nhds hz))
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds hz)] with w hw
  exact hbound w hw

/-- Normalization removes removable singularities under a continuous norm bound. -/
theorem analyticOnNhd_toMeromorphicNFOn_of_norm_le {f : ℂ → ℂ} {g : ℂ → ℝ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hU : IsOpen U) (hg : ContinuousOn g U)
    (hbound : ∀ z ∈ U, ‖f z‖ ≤ g z) : AnalyticOnNhd ℂ (toMeromorphicNFOn f U) U := by
  intro z hz
  apply analyticAt_of_eventually_norm_le_continuousAt
    (meromorphicNFOn_toMeromorphicNFOn f U hz)
    ((hg z hz).continuousAt (hU.mem_nhds hz))
  filter_upwards [hf.toMeromorphicNFOn_eq_self_on_nhdsNE hz,
    eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds hz)] with w hw hwU
  rw [hw]
  exact hbound w hwU

/-- The continuous norm bound survives normalization, including at removable singularities. -/
theorem norm_toMeromorphicNFOn_le_of_norm_le {f : ℂ → ℂ} {g : ℂ → ℝ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hU : IsOpen U) (hg : ContinuousOn g U)
    (hbound : ∀ z ∈ U, ‖f z‖ ≤ g z) : ∀ z ∈ U, ‖toMeromorphicNFOn f U z‖ ≤ g z := by
  intro z hz
  have han := analyticOnNhd_toMeromorphicNFOn_of_norm_le hf hU hg hbound z hz
  apply le_of_tendsto_of_tendsto (b := 𝓝[≠] z)
    (han.continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds)
    (((hg z hz).continuousAt (hU.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [hf.toMeromorphicNFOn_eq_self_on_nhdsNE hz,
    eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds hz)] with w hw hwU
  rw [hw]
  exact hbound w hwU

end MMeromorphicTest.BoundedNormalForm
