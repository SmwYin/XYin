import XYin.PhD.Test.MMeromorphic.Comparison

/-!
# Complex-line `C^1` manifolds have analytic transition functions

One-variable complex differentiability on an open set implies analyticity. We use this to
provide a named `C^1`-to-`C^ω` manifold theorem rather than registering a global instance.
The local-fraction comparison and inverse API can consequently assume only `C^1` on Riemann
surfaces. This experiment makes no corresponding assertion for arbitrary incomplete normed models.
-/

open Set
open scoped ContDiff Manifold

namespace MMeromorphicTest.RiemannSurface

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M]

/-- A manifold modelled on the complex line with complex `C^1` chart transitions has
complex analytic chart transitions. This is deliberately a theorem, not a global instance. -/
theorem isManifold_analytic : IsManifold 𝓘(ℂ) ω M := by
  refine isManifold_of_contDiffOn 𝓘(ℂ) ω M ?_
  intro e e' he he'
  have hd : ContDiffOn ℂ 1 (e.symm.trans e') (e.symm.trans e').source := by
    simpa [ModelWithCorners.extendCoordChange, OpenPartialHomeomorph.extend] using
      ModelWithCorners.contDiffOn_extendCoordChange (I := 𝓘(ℂ))
        (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he')
  have ha : AnalyticOnNhd ℂ (e.symm.trans e') (e.symm.trans e').source :=
    (hd.differentiableOn one_ne_zero).analyticOnNhd (e.symm.trans e').open_source
  simpa only [mfld_simps] using ha.contDiffOn_of_completeSpace (n := ω)

/-- Local fractions and preferred charts agree under the usual complex `C^1` assumption. -/
theorem localFractionAt_iff_chartsAt {f : M → ℂ} {x : M} :
    LocalFraction.MMeromorphicAt 𝓘(ℂ) f x ↔
      MMeromorphicExperiment.Charts.MMeromorphicAt f x := by
  letI := isManifold_analytic (M := M)
  exact Comparison.localFractionAt_iff_chartsAt

theorem localFraction_iff_charts {f : M → ℂ} :
    LocalFraction.MMeromorphic 𝓘(ℂ) f ↔ MMeromorphicExperiment.Charts.MMeromorphic f := by
  letI := isManifold_analytic (M := M)
  exact Comparison.localFraction_iff_charts

theorem localFractionOn_iff_chartsOn {f : M → ℂ} {s : Set M} :
    LocalFraction.MMeromorphicOn 𝓘(ℂ) f s ↔
      MMeromorphicExperiment.Charts.MMeromorphicOn f s := by
  letI := isManifold_analytic (M := M)
  exact Comparison.localFractionOn_iff_chartsOn

/-- Inversion of local fractions on a complex `C^1` Riemann surface. -/
theorem localFractionAt_inv {f : M → ℂ} {x : M}
    (hf : LocalFraction.MMeromorphicAt 𝓘(ℂ) f x) :
    LocalFraction.MMeromorphicAt 𝓘(ℂ) f⁻¹ x := by
  letI := isManifold_analytic (M := M)
  exact hf.inv_manifold

theorem localFraction_inv {f : M → ℂ} (hf : LocalFraction.MMeromorphic 𝓘(ℂ) f) :
    LocalFraction.MMeromorphic 𝓘(ℂ) f⁻¹ := fun x ↦ localFractionAt_inv (hf x)

/-- Holomorphic functions satisfy the direct local-fraction predicate on a Riemann surface. -/
theorem localFraction_of_mdifferentiable {f : M → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    LocalFraction.MMeromorphic 𝓘(ℂ) f :=
  localFraction_iff_charts.mpr hf.mMeromorphic

/-- In complex dimension one, raw local-fraction representatives allow every holomorphic
pullback. The source and target need only the usual complex `C^1` manifold assumptions. -/
theorem localFraction_comp_mdifferentiable
    {N : Type*} [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) 1 N]
    {f : N → ℂ} {g : M → N} (hf : LocalFraction.MMeromorphic 𝓘(ℂ) f)
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    LocalFraction.MMeromorphic 𝓘(ℂ) (f ∘ g) := by
  exact localFraction_iff_charts.mpr
    ((localFraction_iff_charts.mp hf).comp_mdifferentiable hg)

example : IsManifold 𝓘(ℂ) ω M := isManifold_analytic

example {f : M → ℂ} (hf : LocalFraction.MMeromorphic 𝓘(ℂ) f) :
    LocalFraction.MMeromorphic 𝓘(ℂ) f⁻¹ := localFraction_inv hf

example {f : M → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    LocalFraction.MMeromorphic 𝓘(ℂ) f := localFraction_of_mdifferentiable hf

example {N : Type*} [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) 1 N]
    {f : N → ℂ} {g : M → N} (hf : LocalFraction.MMeromorphic 𝓘(ℂ) f)
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    LocalFraction.MMeromorphic 𝓘(ℂ) (f ∘ g) := localFraction_comp_mdifferentiable hf hg

#print axioms isManifold_analytic
#print axioms localFractionAt_iff_chartsAt
#print axioms localFraction_inv
#print axioms localFraction_comp_mdifferentiable

end MMeromorphicTest.RiemannSurface
