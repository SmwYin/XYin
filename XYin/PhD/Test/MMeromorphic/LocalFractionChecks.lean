import XYin.PhD.Test.MMeromorphic.LocalFraction
import XYin.PhD.Test.MMeromorphic.Comparison
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Checks for the general-dimensional local fraction experiment

The examples use arbitrary complex normed models. The last checks make the distinction between
pointwise representatives and a field of meromorphic sections explicit: the representatives have
zero divisors, and arbitrary values can be hidden along a denominator's zero hypersurface.
-/

open Set UpperHalfPlane
open scoped ContDiff Manifold Topology

namespace MMeromorphicTest.LocalFraction

section AbstractAPI

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {f g : M → ℂ}

example (hf : MMeromorphic I f) (hg : MMeromorphic I g) :
    MMeromorphic I ((f + g) * (f - g)) := (hf.add hg).mul (hf.sub hg)

example (hf : ContMDiff I 𝓘(ℂ) ω f) : MMeromorphic I f := ContMDiff.mmeromorphic hf

example : MMeromorphic I (fun _ : M ↦ (3 : ℂ)) := mmeromorphic_const 3

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℂ F K}
    {N : Type*} [TopologicalSpace N] [ChartedSpace K N] {h : N → M}
    (hf : MMeromorphic I f) (hh : ContMDiff J I ω h) (ho : IsOpenMap h) :
    MMeromorphic J (f ∘ h) := hf.comp_open hh ho

end AbstractAPI

/-- An arbitrary pointwise value at a one-variable singular point. -/
noncomputable def spike (z : ℂ) : ℂ := if z = 0 then 1 else 0

theorem spike_mmeromorphic : MMeromorphic 𝓘(ℂ) spike := by
  refine mmeromorphic_of_globalFraction (a := fun _ ↦ 0) (b := id)
    contMDiff_const contMDiff_id ?_ ?_
  · simpa only [id_eq, ← mem_compl_singleton_iff] using dense_compl_singleton (0 : ℂ)
  · intro z hz
    change z ≠ 0 at hz
    simp [spike, hz]

theorem spike_ne_zero : spike ≠ (0 : ℂ → ℂ) := by
  intro h
  have := congrFun h 0
  simp [spike] at this

theorem id_ne_zero : (id : ℂ → ℂ) ≠ 0 := by
  intro h
  have := congrFun h 1
  simp at this

theorem spike_mul_id : spike * id = (0 : ℂ → ℂ) := by
  funext z
  by_cases hz : z = 0 <;> simp [spike, hz]

/-- The direct predicate alone cannot make its subtype into a pointwise field. -/
theorem pointwise_zero_divisors : ∃ f g : ℂ → ℂ,
    MMeromorphic 𝓘(ℂ) f ∧ MMeromorphic 𝓘(ℂ) g ∧ f ≠ 0 ∧ g ≠ 0 ∧ f * g = 0 :=
  ⟨spike, id, spike_mmeromorphic, ContMDiff.mmeromorphic contMDiff_id,
    spike_ne_zero, id_ne_zero, spike_mul_id⟩

theorem coordinate_nonzero_dense : Dense {p : ℂ × ℂ | p.2 ≠ 0} := by
  simpa only [← mem_compl_singleton_iff] using
    (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_snd : IsOpenMap (@Prod.snd ℂ ℂ))

/-- A two-dimensional quotient with a whole hypersurface of zeros of the denominator. -/
theorem coordinate_ratio_mmeromorphic :
    MMeromorphic 𝓘(ℂ, ℂ × ℂ) (fun p : ℂ × ℂ ↦ p.1 / p.2) :=
  mmeromorphic_of_globalFraction contDiff_fst.contMDiff contDiff_snd.contMDiff
    coordinate_nonzero_dense
    (fun _ _ ↦ rfl)

/-- Arbitrary values along a polar hypersurface do not affect the represented fraction.
This is why subsequent equality must forget these values. -/
theorem arbitrary_hypersurface_values (v : ℂ → ℂ) :
    MMeromorphic 𝓘(ℂ, ℂ × ℂ) (fun p : ℂ × ℂ ↦ if p.2 = 0 then v p.1 else 0) := by
  refine mmeromorphic_of_globalFraction (a := fun _ ↦ 0) (b := Prod.snd)
    contMDiff_const contDiff_snd.contMDiff coordinate_nonzero_dense ?_
  intro p hp
  change p.2 ≠ 0 at hp
  simp [hp]

example {f : ℂ → ℂ} {z : ℂ} :
    MMeromorphicAt 𝓘(ℂ) f z ↔ MeromorphicAt f z := mmeromorphicAt_iff_meromorphicAt

example {f : ℂ → ℂ} :
    MMeromorphic 𝓘(ℂ) f ↔ MeromorphicOn f univ := mmeromorphic_iff_meromorphicOn

example {f : ℂ → ℂ} (hf : MMeromorphic 𝓘(ℂ) f) :
    MMeromorphic 𝓘(ℂ) f⁻¹ := hf.inv_complex

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ}
    (hf : MMeromorphic 𝓘(ℂ, E) f) (hg : MMeromorphic 𝓘(ℂ, E) g) :
    MMeromorphic 𝓘(ℂ, E) (f / g) := hf.div_normed hg

example : MMeromorphic 𝓘(ℂ, ℂ × ℂ) (fun p : ℂ × ℂ ↦ p.1 / p.2)⁻¹ :=
  coordinate_ratio_mmeromorphic.inv_normed

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℂ, E) ω A]
    {f : A → ℂ} (hf : MMeromorphic 𝓘(ℂ, E) f) : MMeromorphic 𝓘(ℂ, E) f⁻¹ :=
  hf.inv_manifold

example {f : ℍ → ℂ} :
    MMeromorphic 𝓘(ℂ) f ↔ MMeromorphicTest.UHP.Meromorphic f :=
  mmeromorphic_upperHalfPlane_iff

example {f : ℍ → ℂ} (hf : MDiff f) : MMeromorphic 𝓘(ℂ) f :=
  mmeromorphic_upperHalfPlane_iff.mpr (MMeromorphicTest.UHP.of_mdifferentiable hf)

example {f : ℍ → ℂ} {h : ℍ → ℍ} (hf : MMeromorphic 𝓘(ℂ) f) (hh : MDiff h) :
    MMeromorphic 𝓘(ℂ) (f ∘ h) :=
  mmeromorphic_upperHalfPlane_iff.mpr
    (MMeromorphicTest.UHP.comp (mmeromorphic_upperHalfPlane_iff.mp hf) hh)

example {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] {f : M → ℂ} {x : M} :
    MMeromorphicAt 𝓘(ℂ) f x ↔ MMeromorphicExperiment.Charts.MMeromorphicAt f x :=
  MMeromorphicTest.Comparison.localFractionAt_iff_chartsAt

example {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] {f : M → ℂ} :
    MMeromorphic 𝓘(ℂ) f ↔ MMeromorphicExperiment.Charts.MMeromorphic f :=
  MMeromorphicTest.Comparison.localFraction_iff_charts

private theorem conj_not_differentiableAt (z : ℂ) :
    ¬ DifferentiableAt ℂ (starRingEnd ℂ) z := by
  intro hd
  obtain ⟨g, hg⟩ := (differentiableAt_iff_restrictScalars ℝ
    (Complex.conjCLE.differentiableAt : DifferentiableAt ℝ (starRingEnd ℂ) z)).mp hd
  rw [Complex.conjCLE.fderiv] at hg
  have h1 : g 1 = 1 := by
    simpa using congrArg (fun k : ℂ →L[ℝ] ℂ ↦ k 1) hg
  have hi : g Complex.I = -Complex.I := by
    simpa using congrArg (fun k : ℂ →L[ℝ] ℂ ↦ k Complex.I) hg
  have hlin := g.map_smul Complex.I (1 : ℂ)
  simp only [smul_eq_mul, mul_one, h1, hi] at hlin
  have he := congrArg Complex.im hlin
  norm_num at he

theorem conj_not_mmeromorphicAt (z : ℂ) :
    ¬ MMeromorphicAt 𝓘(ℂ) (starRingEnd ℂ) z := by
  intro hf
  obtain ⟨y, hy⟩ := (mmeromorphicAt_iff_meromorphicAt.mp hf).eventually_analyticAt.exists
  exact conj_not_differentiableAt y
    ((hy.contDiffAt (n := 1)).differentiableAt (by simp))

/-- A holomorphic embedding into the exceptional hypersurface can pull a representative back
to an arbitrary function. Taking conjugation makes unrestricted pullback formally false. -/
theorem unrestricted_holomorphic_pullback_fails :
    ∃ (f : ℂ × ℂ → ℂ) (h : ℂ → ℂ × ℂ),
      MMeromorphic 𝓘(ℂ, ℂ × ℂ) f ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) ω h ∧
      ¬ MMeromorphic 𝓘(ℂ) (f ∘ h) := by
  let f : ℂ × ℂ → ℂ := fun p ↦ if p.2 = 0 then (starRingEnd ℂ) p.1 else 0
  let h : ℂ → ℂ × ℂ := fun z ↦ (z, 0)
  refine ⟨f, h, arbitrary_hypersurface_values (starRingEnd ℂ),
    (contDiff_id.prodMk contDiff_const).contMDiff, ?_⟩
  intro hpull
  apply conj_not_mmeromorphicAt 0
  simpa [f, h, Function.comp_def] using hpull 0

#print axioms MMeromorphicAt.add
#print axioms MMeromorphicAt.mul
#print axioms MMeromorphicAt.comp_open
#print axioms pointwise_zero_divisors
#print axioms arbitrary_hypersurface_values
#print axioms mmeromorphicAt_iff_meromorphicAt
#print axioms unrestricted_holomorphic_pullback_fails
#print axioms MMeromorphicAt.inv_normed
#print axioms MMeromorphicAt.inv_manifold
#print axioms mmeromorphic_upperHalfPlane_iff
#print axioms MMeromorphicTest.Comparison.localFractionAt_iff_chartsAt

end MMeromorphicTest.LocalFraction
