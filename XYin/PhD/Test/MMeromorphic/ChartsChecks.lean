import XYin.PhD.Test.MMeromorphic.Charts
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import XYin.PhD.Test.MMeromorphic.UpperHalfPlane

/-!
# Sanity and API checks for the preferred-chart version

The examples exercise the predicate on the original functions, rather than repeatedly unfolding
their complex coordinate expressions. They include an upper-half-plane example with poles.
-/

open Filter Set
open scoped Topology Manifold ContDiff

namespace MMeromorphicExperiment.Charts

section Arithmetic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  {f g h : M → ℂ}

example (hf : MMeromorphic f) (hg : MMeromorphic g) (hh : MMeromorphic h) :
    MMeromorphic (fun x ↦ (f x + g x) / h x) := (hf.add hg).div hh

example (hf : MMeromorphic f) :
    MMeromorphic (fun x ↦ (f x)⁻¹ + (f x) ^ 3) := hf.inv.add (hf.pow 3)

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {v : M → E}
    (hf : MMeromorphic f) (hv : MMeromorphic v) :
    MMeromorphic (fun x ↦ f x • v x) := hf.smul hv

example {s t : Set M} (hf : MMeromorphicOn f s) (hg : MMeromorphicOn g s) (hst : t ⊆ s) :
    MMeromorphicOn (fun x ↦ (f x + g x)⁻¹) t := ((hf.add hg).inv).mono_set hst

end Arithmetic

section ChartsAndPullback

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) 1 M] [TopologicalSpace N] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) 1 N] {f : N → ℂ} {g : M → N}

example (hf : MMeromorphic f) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    MMeromorphic (fun x ↦ f (g x)) := hf.comp_mdifferentiable hg

example {h : M → ℂ} (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) :
    MMeromorphic h := hh.mMeromorphic

example {h : M → ℂ} {x : M} {e : OpenPartialHomeomorph M ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 M) (hx : x ∈ e.source)
    (hh : MMeromorphicAt h x) : MeromorphicAt (h ∘ e.symm) (e x) :=
  (MMeromorphicAt.iff_of_mem_maximalAtlas he hx).mp hh

example {h : M → ℂ} {x : M} {e : OpenPartialHomeomorph M ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 M) (hx : x ∈ e.source)
    (hh : MeromorphicAt (h ∘ e.symm) (e x)) : MMeromorphicAt h x :=
  (MMeromorphicAt.iff_of_mem_maximalAtlas he hx).mpr hh

end ChartsAndPullback

@[simp]
lemma mMeromorphicAt_upperHalfPlane_iff {f : UpperHalfPlane → ℂ} {τ : UpperHalfPlane} :
    MMeromorphicAt f τ ↔ MeromorphicAt (f ∘ UpperHalfPlane.ofComplex) (τ : ℂ) := Iff.rfl

/-- The generic chart predicate specializes exactly to the minimal upper-half-plane version. -/
lemma mMeromorphic_upperHalfPlane_iff {f : UpperHalfPlane → ℂ} :
    MMeromorphic f ↔ MMeromorphicTest.UHP.Meromorphic f := by
  rw [MMeromorphicTest.UHP.iff_forall]
  rfl

example : MMeromorphic (fun z : ℂ ↦ z⁻¹) := by
  rw [mMeromorphic_complex_iff]
  exact Meromorphic.inv (fun z ↦ MeromorphicAt.id z)

/-- Raw-function pullback allows constant maps, including maps to an assigned pole value.
Such pullback need not respect equivalence classes that forget the assigned value. -/
example {f : ℂ → ℂ} (hf : MMeromorphic f) (a : ℂ) :
    MMeromorphic (fun _ : ℂ ↦ f a) := hf.comp_mdifferentiable mdifferentiable_const

example : MMeromorphic (fun τ : UpperHalfPlane ↦ (τ : ℂ)) :=
  UpperHalfPlane.mdifferentiable_coe.mMeromorphic

/-- This rational expression has a pole inside the upper half plane. -/
example : MMeromorphic (fun τ : UpperHalfPlane ↦ ((τ : ℂ) ^ 2 + 2) / ((τ : ℂ) - Complex.I)) := by
  have hcoe : MMeromorphic (fun τ : UpperHalfPlane ↦ (τ : ℂ)) :=
    UpperHalfPlane.mdifferentiable_coe.mMeromorphic
  exact ((hcoe.pow 2).add (.const 2)).div (hcoe.sub (.const Complex.I))

#print axioms MMeromorphicAt.iff_of_mem_maximalAtlas
#print axioms MMeromorphic.comp_mdifferentiable
#print axioms MDifferentiable.mMeromorphic
#print axioms mMeromorphic_upperHalfPlane_iff

end MMeromorphicExperiment.Charts
