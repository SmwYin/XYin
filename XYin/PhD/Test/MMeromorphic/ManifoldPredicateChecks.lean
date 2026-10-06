import XYin.PhD.ModularFunctions.ManifoldMeromorphic
import XYin.PhD.Test.MMeromorphic.Charts

/-!
# Checks for the production manifold predicates

The production extended-chart definition agrees with the preferred-chart experiment when the
model is the complex line. Consequently the experiment's complex `C¹` coordinate-independence
and holomorphic-pullback theorems apply to the production raw predicate. These comparisons are
one-dimensional and make no assertion equating higher-dimensional fractions with normal form.
-/

open scoped Manifold Topology

namespace MMeromorphicTest.ManifoldPredicateChecks

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- The extended chart for the identity model gives the experiment's preferred-chart predicate. -/
theorem productionAt_iff_chartsAt {f : M → ℂ} {x : M} :
    MMeromorphicAt f x ↔ MMeromorphicExperiment.Charts.MMeromorphicAt f x := by
  simp only [MMeromorphicAt, MMeromorphicExperiment.Charts.MMeromorphicAt,
    extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp]

/-- The global production predicate agrees with the independent preferred-chart experiment. -/
theorem production_iff_charts {f : M → ℂ} :
    MMeromorphic f ↔ MMeromorphicExperiment.Charts.MMeromorphic f :=
  forall_congr' fun _ ↦ productionAt_iff_chartsAt

/-- Production meromorphy can be tested in every compatible complex `C¹` chart. -/
theorem productionAt_iff_of_mem_maximalAtlas [IsManifold 𝓘(ℂ) 1 M]
    {f : M → ℂ} {x : M} {e : OpenPartialHomeomorph M ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 M) (hx : x ∈ e.source) :
    MMeromorphicAt f x ↔ MeromorphicAt (f ∘ e.symm) (e x) :=
  productionAt_iff_chartsAt.trans
    (MMeromorphicExperiment.Charts.MMeromorphicAt.iff_of_mem_maximalAtlas he hx)

/-- The independent experiment checks holomorphic pullback of the production raw predicate. -/
theorem production_comp_mdifferentiable [IsManifold 𝓘(ℂ) 1 M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) 1 N]
    {f : N → ℂ} {g : M → N} (hf : MMeromorphic f)
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) : MMeromorphic (f ∘ g) :=
  production_iff_charts.mpr ((production_iff_charts.mp hf).comp_mdifferentiable hg)

/-- Arithmetic uses the original scalar functions, without changing to chart compositions. -/
theorem arithmetic_sanity {f g : M → ℂ} (hf : MMeromorphic f) (hg : MMeromorphic g) :
    MMeromorphic ((f + g) / f) :=
  (hf.add hg).div hf

/-- The production normal-form predicate supports pointwise inversion. -/
theorem normal_inverse_sanity {f : M → ℂ} (hf : MMeromorphicNF f) : MMeromorphicNF f⁻¹ :=
  hf.inv

end MMeromorphicTest.ManifoldPredicateChecks
