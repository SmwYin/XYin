import XYin.PhD.Test.MMeromorphic.LocalFraction
import XYin.PhD.Test.MMeromorphic.Charts

/-!
# Comparing preferred charts and local holomorphic fractions

On a one-dimensional analytic complex manifold the direct local-fraction predicate and the
preferred-chart predicate are equivalent. The local-fraction transport proof uses `C^ω` charts;
the independent preferred-chart API only needs `C^1` compatibility. We do not add an automatic
conversion from a complex `C^1` manifold to a `C^ω` manifold here.
-/

open Filter
open scoped ContDiff Manifold Topology

namespace MMeromorphicTest.Comparison

open LocalFraction

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) ω M]

/-- Local holomorphic fractions and the preferred-chart test agree on analytic Riemann surfaces. -/
theorem localFractionAt_iff_chartsAt {f : M → ℂ} {x : M} :
    MMeromorphicAt 𝓘(ℂ) f x ↔ MMeromorphicExperiment.Charts.MMeromorphicAt f x := by
  let e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  constructor
  · intro hf
    have hf' : MMeromorphicAt 𝓘(ℂ) f (e.symm (e x)) := by
      simpa only [e.left_inv hx] using hf
    have hcoords := hf'.comp_partialHomeomorph (e.map_source hx)
      (contMDiffOn_chart_symm (I := 𝓘(ℂ)))
    exact mmeromorphicAt_iff_meromorphicAt.mp hcoords
  · intro hf
    have hcoords : MMeromorphicAt 𝓘(ℂ) (f ∘ e.symm) (e x) :=
      mmeromorphicAt_iff_meromorphicAt.mpr hf
    have hpull := hcoords.comp_partialHomeomorph hx (contMDiffOn_chart (I := 𝓘(ℂ)))
    apply hpull.congr_nhds
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp only [Function.comp_def, e.left_inv hy]

theorem localFraction_iff_charts {f : M → ℂ} :
    MMeromorphic 𝓘(ℂ) f ↔ MMeromorphicExperiment.Charts.MMeromorphic f :=
  forall_congr' fun _ ↦ localFractionAt_iff_chartsAt

theorem localFractionOn_iff_chartsOn {f : M → ℂ} {s : Set M} :
    MMeromorphicOn 𝓘(ℂ) f s ↔ MMeromorphicExperiment.Charts.MMeromorphicOn f s :=
  forall_congr' fun _ ↦ forall_congr' fun _ ↦ localFractionAt_iff_chartsAt

end MMeromorphicTest.Comparison
