/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Geometry.Manifold.Notation

/-!
# Meromorphic functions in complex manifold charts

These predicates apply directly to `f : M → ℂ` on a space charted over the complex line.
They use the preferred chart at each point and do not depend on a meromorphic function field.
Their definitions require only `ChartedSpace ℂ M`. Interpreting them independently of the
preferred charts requires complex compatible transitions, for example
`IsManifold 𝓘(ℂ) 1 M`. In complex dimension one, complex `C¹` transitions are analytic.
The local definitions need no connectedness, Hausdorffness, or countability assumption.

`MMeromorphicOn` and `MMeromorphicNFOn` assert a neighborhood property at every point of a set;
they are not within-set predicates. Raw meromorphy ignores assigned values at isolated
singularities. Normal form fixes removable values and assigns zero at poles. Addition and
multiplication of normal representatives can require normalization after cancellation.

On `ℍ`, the inverse preferred chart is `UpperHalfPlane.ofComplex`. Thus the chart predicates
recover the existing one-variable predicates on `upperHalfPlaneSet`. These definitions concern
complex dimension one; local analytic fractions are a separate extension to higher dimensions.
-/

open UpperHalfPlane Filter
open scoped Manifold Topology

section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- `f : M → ℂ` is meromorphic at `x`, read in the preferred chart at `x`. -/
def MMeromorphicAt (f : M → ℂ) (x : M) : Prop :=
  MeromorphicAt (f ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x)

/-- `f : M → ℂ` is meromorphic in normal form at `x`, read in its preferred chart. -/
def MMeromorphicNFAt (f : M → ℂ) (x : M) : Prop :=
  MeromorphicNFAt (f ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x)

/-- `f : M → ℂ` is meromorphic at every point. -/
def MMeromorphic (f : M → ℂ) : Prop := ∀ x, MMeromorphicAt f x

/-- `f : M → ℂ` is meromorphic in normal form at every point. -/
def MMeromorphicNF (f : M → ℂ) : Prop := ∀ x, MMeromorphicNFAt f x

/-- Meromorphy in a neighborhood of every point of `s`, rather than within `s`. -/
def MMeromorphicOn (f : M → ℂ) (s : Set M) : Prop := ∀ x ∈ s, MMeromorphicAt f x

/-- Meromorphic normal form in a neighborhood of every point of `s`. -/
def MMeromorphicNFOn (f : M → ℂ) (s : Set M) : Prop := ∀ x ∈ s, MMeromorphicNFAt f x

/-- The order of `f : M → ℂ` at `x`, read in the preferred chart at `x`. -/
noncomputable def mmeromorphicOrderAt (f : M → ℂ) (x : M) : WithTop ℤ :=
  meromorphicOrderAt (f ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x)

variable {f g : M → ℂ} {x : M} {s t : Set M}

theorem MMeromorphicAt.const (c : ℂ) (x : M) : MMeromorphicAt (fun _ ↦ c) x :=
  MeromorphicAt.const _ _

theorem MMeromorphicAt.add (hf : MMeromorphicAt f x) (hg : MMeromorphicAt g x) :
    MMeromorphicAt (f + g) x := MeromorphicAt.add hf hg

theorem MMeromorphicAt.neg (hf : MMeromorphicAt f x) : MMeromorphicAt (-f) x :=
  MeromorphicAt.neg hf

theorem MMeromorphicAt.sub (hf : MMeromorphicAt f x) (hg : MMeromorphicAt g x) :
    MMeromorphicAt (f - g) x := MeromorphicAt.sub hf hg

theorem MMeromorphicAt.mul (hf : MMeromorphicAt f x) (hg : MMeromorphicAt g x) :
    MMeromorphicAt (f * g) x := MeromorphicAt.mul hf hg

theorem MMeromorphicAt.inv (hf : MMeromorphicAt f x) : MMeromorphicAt f⁻¹ x :=
  MeromorphicAt.inv hf

theorem MMeromorphicAt.div (hf : MMeromorphicAt f x) (hg : MMeromorphicAt g x) :
    MMeromorphicAt (f / g) x := MeromorphicAt.div hf hg

theorem MMeromorphicAt.pow (hf : MMeromorphicAt f x) (n : ℕ) :
    MMeromorphicAt (f ^ n) x := MeromorphicAt.pow hf n

theorem MMeromorphic.const (c : ℂ) : MMeromorphic (fun _ : M ↦ c) :=
  fun x ↦ MMeromorphicAt.const c x

theorem MMeromorphic.add (hf : MMeromorphic f) (hg : MMeromorphic g) :
    MMeromorphic (f + g) := fun x ↦ (hf x).add (hg x)

theorem MMeromorphic.neg (hf : MMeromorphic f) : MMeromorphic (-f) := fun x ↦ (hf x).neg

theorem MMeromorphic.sub (hf : MMeromorphic f) (hg : MMeromorphic g) :
    MMeromorphic (f - g) := fun x ↦ (hf x).sub (hg x)

theorem MMeromorphic.mul (hf : MMeromorphic f) (hg : MMeromorphic g) :
    MMeromorphic (f * g) := fun x ↦ (hf x).mul (hg x)

theorem MMeromorphic.inv (hf : MMeromorphic f) : MMeromorphic f⁻¹ := fun x ↦ (hf x).inv

theorem MMeromorphic.div (hf : MMeromorphic f) (hg : MMeromorphic g) :
    MMeromorphic (f / g) := fun x ↦ (hf x).div (hg x)

theorem MMeromorphic.pow (hf : MMeromorphic f) (n : ℕ) : MMeromorphic (f ^ n) :=
  fun x ↦ (hf x).pow n

theorem MMeromorphicNFAt.inv (hf : MMeromorphicNFAt f x) : MMeromorphicNFAt f⁻¹ x :=
  MeromorphicNFAt.inv hf

theorem MMeromorphicNF.inv (hf : MMeromorphicNF f) : MMeromorphicNF f⁻¹ :=
  fun x ↦ (hf x).inv

theorem MMeromorphicNFAt.mmeromorphicAt (hf : MMeromorphicNFAt f x) : MMeromorphicAt f x :=
  MeromorphicNFAt.meromorphicAt hf

theorem MMeromorphicNF.mmeromorphic (hf : MMeromorphicNF f) : MMeromorphic f :=
  fun x ↦ (hf x).mmeromorphicAt

theorem MMeromorphicNFOn.mmeromorphicOn (hf : MMeromorphicNFOn f s) : MMeromorphicOn f s :=
  fun x hx ↦ (hf x hx).mmeromorphicAt

theorem MMeromorphic.mmeromorphicOn (hf : MMeromorphic f) (s : Set M) :
    MMeromorphicOn f s := fun x _ ↦ hf x

theorem MMeromorphicNF.mmeromorphicNFOn (hf : MMeromorphicNF f) (s : Set M) :
    MMeromorphicNFOn f s := fun x _ ↦ hf x

theorem MMeromorphicOn.mono (hf : MMeromorphicOn f s) (hts : t ⊆ s) :
    MMeromorphicOn f t := fun x hx ↦ hf x (hts hx)

theorem MMeromorphicNFOn.mono (hf : MMeromorphicNFOn f s) (hts : t ⊆ s) :
    MMeromorphicNFOn f t := fun x hx ↦ hf x (hts hx)

theorem MMeromorphicNFAt.mmeromorphicOrderAt_nonneg_iff_analyticAt
    (hf : MMeromorphicNFAt f x) :
    0 ≤ mmeromorphicOrderAt f x ↔
      AnalyticAt ℂ (f ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x) :=
  MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt hf

end Manifold

namespace UpperHalfPlane

/-- The preferred chart of `ℍ` is the inclusion into `ℂ`. -/
theorem chartAt_eq (τ : ℍ) : chartAt ℂ τ = isOpenEmbedding_coe.toOpenPartialHomeomorph _ := rfl

/-- The inverse of the preferred chart of `ℍ` is `ofComplex`. -/
theorem chartAt_symm_eq_ofComplex (τ : ℍ) : (chartAt ℂ τ).symm = ofComplex := rfl

theorem extChartAt_symm_eq_ofComplex (τ : ℍ) : ⇑(extChartAt 𝓘(ℂ) τ).symm = ofComplex := by
  rw [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, chartAt_symm_eq_ofComplex,
    Function.comp_id]

theorem extChartAt_apply_eq_coe (τ : ℍ) : extChartAt 𝓘(ℂ) τ τ = (τ : ℂ) := by
  rw [extChartAt_coe]
  rfl

variable {f : ℍ → ℂ} {τ : ℍ}

theorem mmeromorphicAt_iff : MMeromorphicAt f τ ↔ MeromorphicAt (f ∘ ofComplex) τ := by
  rw [MMeromorphicAt, extChartAt_symm_eq_ofComplex, extChartAt_apply_eq_coe]

theorem mmeromorphicNFAt_iff : MMeromorphicNFAt f τ ↔ MeromorphicNFAt (f ∘ ofComplex) τ := by
  rw [MMeromorphicNFAt, extChartAt_symm_eq_ofComplex, extChartAt_apply_eq_coe]

theorem mmeromorphicOrderAt_eq :
    mmeromorphicOrderAt f τ = meromorphicOrderAt (f ∘ ofComplex) τ := by
  rw [mmeromorphicOrderAt, extChartAt_symm_eq_ofComplex, extChartAt_apply_eq_coe]

/-- The analogue of `mdifferentiable_iff` for meromorphy in normal form. -/
theorem mmeromorphicNF_iff :
    MMeromorphicNF f ↔ MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet :=
  ⟨fun h z hz ↦ mmeromorphicNFAt_iff.1 (h ⟨z, hz⟩),
    fun h τ ↦ mmeromorphicNFAt_iff.2 (h τ.im_pos)⟩

theorem mmeromorphic_iff : MMeromorphic f ↔ MeromorphicOn (f ∘ ofComplex) upperHalfPlaneSet :=
  ⟨fun h z hz ↦ mmeromorphicAt_iff.1 (h ⟨z, hz⟩),
    fun h τ ↦ mmeromorphicAt_iff.2 (h τ τ.im_pos)⟩

/-- On a subset of `ℍ`, the chart predicate agrees with meromorphy on its image in `ℂ`. -/
theorem mmeromorphicOn_iff {s : Set ℍ} :
    MMeromorphicOn f s ↔ MeromorphicOn (f ∘ ofComplex) ((↑) '' s) := by
  constructor
  · rintro h z ⟨τ, hτ, rfl⟩
    exact mmeromorphicAt_iff.mp (h τ hτ)
  · intro h τ hτ
    exact mmeromorphicAt_iff.mpr (h τ ⟨τ, hτ, rfl⟩)

/-- Normal form on a subset of `ℍ` agrees with normal form on its image in `ℂ`. -/
theorem mmeromorphicNFOn_iff {s : Set ℍ} :
    MMeromorphicNFOn f s ↔ MeromorphicNFOn (f ∘ ofComplex) ((↑) '' s) := by
  constructor
  · rintro h z ⟨τ, hτ, rfl⟩
    exact mmeromorphicNFAt_iff.mp (h τ hτ)
  · intro h τ hτ
    exact mmeromorphicNFAt_iff.mpr (h ⟨τ, hτ, rfl⟩)

/-- Holomorphic functions on `ℍ` are meromorphic in normal form. -/
theorem _root_.MDifferentiable.mmeromorphicNF (hf : MDiff f) : MMeromorphicNF f := by
  rw [mmeromorphicNF_iff]
  intro z hz
  exact ((mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet z hz).meromorphicNFAt

/-- A function on `ℍ` is holomorphic iff it is meromorphic in normal form without poles. -/
theorem mdifferentiable_iff_mmeromorphicNF :
    MDiff f ↔ MMeromorphicNF f ∧ ∀ τ : ℍ, 0 ≤ mmeromorphicOrderAt f τ := by
  refine ⟨fun hf ↦ ⟨hf.mmeromorphicNF, fun τ ↦ ?_⟩, fun ⟨hNF, hord⟩ τ ↦ ?_⟩
  · rw [mmeromorphicOrderAt_eq,
      (mmeromorphicNFAt_iff.1 (hf.mmeromorphicNF τ)).meromorphicOrderAt_nonneg_iff_analyticAt]
    exact (mdifferentiable_iff.1 hf).analyticOnNhd isOpen_upperHalfPlaneSet τ τ.im_pos
  · rw [mdifferentiableAt_iff]
    refine ((mmeromorphicNFAt_iff.1 (hNF τ)).meromorphicOrderAt_nonneg_iff_analyticAt.1
      ?_).differentiableAt
    rw [← mmeromorphicOrderAt_eq]
    exact hord τ

end UpperHalfPlane
