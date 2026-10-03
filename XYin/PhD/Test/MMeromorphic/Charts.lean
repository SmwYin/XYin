import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# A preferred-chart meromorphic predicate

This experiment deliberately defines a predicate on the original function `f : M → E`.
Its implementation uses the chart at the point, while its public arithmetic API uses `f`.
No continuity of `f` is required: mathlib meromorphy ignores arbitrary values at poles.

The definitions only require a charted space modelled on `ℂ`. Coordinate independence and
holomorphic pullback require complex differentiable transition maps.
-/

open Filter Set
open scoped Topology Manifold ContDiff

namespace MMeromorphicExperiment.Charts

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Meromorphy at a point, tested in its preferred complex coordinate chart. -/
def MMeromorphicAt (f : M → E) (x : M) : Prop :=
  MeromorphicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

/-- Meromorphy at every point of a set; this is not a within-set notion. -/
def MMeromorphicOn (f : M → E) (s : Set M) : Prop :=
  ∀ x ∈ s, MMeromorphicAt f x

/-- Meromorphy on a space modelled on the complex line. -/
def MMeromorphic (f : M → E) : Prop := ∀ x, MMeromorphicAt f x

namespace MMeromorphicAt

variable {f g : M → E} {x : M}

lemma congr_nhds (hf : MMeromorphicAt f x) (hfg : f =ᶠ[𝓝 x] g) :
    MMeromorphicAt g x := by
  have ht := ((chartAt ℂ x).symm.continuousAt (mem_chart_target ℂ x)).tendsto
  rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at ht
  exact _root_.MeromorphicAt.congr hf
    ((hfg.comp_tendsto ht).filter_mono nhdsWithin_le_nhds)

lemma const (c : E) (x : M) : MMeromorphicAt (fun _ ↦ c) x := MeromorphicAt.const _ _

lemma add (hf : MMeromorphicAt f x) (hg : MMeromorphicAt g x) :
    MMeromorphicAt (f + g) x := _root_.MeromorphicAt.add hf hg

lemma neg (hf : MMeromorphicAt f x) : MMeromorphicAt (-f) x := _root_.MeromorphicAt.neg hf

lemma sub (hf : MMeromorphicAt f x) (hg : MMeromorphicAt g x) :
    MMeromorphicAt (f - g) x := _root_.MeromorphicAt.sub hf hg

lemma smul {f : M → ℂ} {g : M → E}
    (hf : MMeromorphicAt f x) (hg : MMeromorphicAt g x) :
    MMeromorphicAt (f • g) x := _root_.MeromorphicAt.smul hf hg

lemma mul {f g : M → ℂ} (hf : MMeromorphicAt f x) (hg : MMeromorphicAt g x) :
    MMeromorphicAt (f * g) x := _root_.MeromorphicAt.mul hf hg

lemma inv {f : M → ℂ} (hf : MMeromorphicAt f x) : MMeromorphicAt f⁻¹ x :=
  _root_.MeromorphicAt.inv hf

lemma div {f g : M → ℂ} (hf : MMeromorphicAt f x) (hg : MMeromorphicAt g x) :
    MMeromorphicAt (f / g) x := _root_.MeromorphicAt.div hf hg

lemma pow {f : M → ℂ} (hf : MMeromorphicAt f x) (n : ℕ) :
    MMeromorphicAt (f ^ n) x := _root_.MeromorphicAt.pow hf n

lemma zpow {f : M → ℂ} (hf : MMeromorphicAt f x) (n : ℤ) :
    MMeromorphicAt (f ^ n) x := _root_.MeromorphicAt.zpow hf n

end MMeromorphicAt

namespace MMeromorphic

variable {f g : M → E}

lemma meromorphicAt (hf : MMeromorphic f) (x : M) : MMeromorphicAt f x := hf x

lemma meromorphicOn (hf : MMeromorphic f) (s : Set M) : MMeromorphicOn f s := fun x _ ↦ hf x

lemma const (c : E) : MMeromorphic (fun _ : M ↦ c) := fun x ↦ .const c x

lemma add (hf : MMeromorphic f) (hg : MMeromorphic g) : MMeromorphic (f + g) :=
  fun x ↦ (hf x).add (hg x)

lemma neg (hf : MMeromorphic f) : MMeromorphic (-f) := fun x ↦ (hf x).neg

lemma sub (hf : MMeromorphic f) (hg : MMeromorphic g) : MMeromorphic (f - g) :=
  fun x ↦ (hf x).sub (hg x)

lemma smul {f : M → ℂ} {g : M → E} (hf : MMeromorphic f) (hg : MMeromorphic g) :
    MMeromorphic (f • g) := fun x ↦ (hf x).smul (hg x)

lemma mul {f g : M → ℂ} (hf : MMeromorphic f) (hg : MMeromorphic g) :
    MMeromorphic (f * g) := fun x ↦ (hf x).mul (hg x)

lemma inv {f : M → ℂ} (hf : MMeromorphic f) : MMeromorphic f⁻¹ := fun x ↦ (hf x).inv

lemma div {f g : M → ℂ} (hf : MMeromorphic f) (hg : MMeromorphic g) :
    MMeromorphic (f / g) := fun x ↦ (hf x).div (hg x)

lemma pow {f : M → ℂ} (hf : MMeromorphic f) (n : ℕ) :
    MMeromorphic (f ^ n) := fun x ↦ (hf x).pow n

lemma zpow {f : M → ℂ} (hf : MMeromorphic f) (n : ℤ) :
    MMeromorphic (f ^ n) := fun x ↦ (hf x).zpow n

end MMeromorphic

namespace MMeromorphicOn

variable {f g : M → E} {s t : Set M}

lemma mono_set (hf : MMeromorphicOn f s) (hst : t ⊆ s) : MMeromorphicOn f t :=
  fun x hx ↦ hf x (hst hx)

lemma add (hf : MMeromorphicOn f s) (hg : MMeromorphicOn g s) : MMeromorphicOn (f + g) s :=
  fun x hx ↦ (hf x hx).add (hg x hx)

lemma mul {f g : M → ℂ} (hf : MMeromorphicOn f s) (hg : MMeromorphicOn g s) :
    MMeromorphicOn (f * g) s := fun x hx ↦ (hf x hx).mul (hg x hx)

lemma inv {f : M → ℂ} (hf : MMeromorphicOn f s) : MMeromorphicOn f⁻¹ s :=
  fun x hx ↦ (hf x hx).inv

end MMeromorphicOn

@[simp]
lemma mMeromorphicAt_complex_iff {f : ℂ → E} {z : ℂ} :
    MMeromorphicAt f z ↔ MeromorphicAt f z := by
  simp [MMeromorphicAt]

@[simp]
lemma mMeromorphic_complex_iff {f : ℂ → E} : MMeromorphic f ↔ Meromorphic f := by
  simp [MMeromorphic, Meromorphic]

section CoordinateIndependence

variable [IsManifold 𝓘(ℂ) 1 M]

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- A complex differentiable transition between compatible charts is analytic. -/
lemma analyticAt_coord_change {e e' : OpenPartialHomeomorph M ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 M)
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    AnalyticAt ℂ (e' ∘ e.symm) (e x) := by
  have hd : ContDiffOn ℂ 1 (e' ∘ e.symm) (e.symm.trans e').source := by
    simpa [ModelWithCorners.extendCoordChange, OpenPartialHomeomorph.extend] using
      ModelWithCorners.contDiffOn_extendCoordChange (I := 𝓘(ℂ)) he he'
  exact (hd.differentiableOn one_ne_zero).analyticAt
    ((e.symm.trans e').open_source.mem_nhds (by simpa [hx] using And.intro (e.map_source hx) hx'))

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- Meromorphy can be tested in any compatible chart containing the point. -/
lemma meromorphicAt_chart_change {f : M → E} {e e' : OpenPartialHomeomorph M ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 M)
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (hf : MeromorphicAt (f ∘ e'.symm) (e' x)) :
    MeromorphicAt (f ∘ e.symm) (e x) := by
  have ha := analyticAt_coord_change he he' hx hx'
  have hf' : MeromorphicAt (f ∘ e'.symm) ((e' ∘ e.symm) (e x)) := by
    simpa [Function.comp_apply, e.left_inv hx] using hf
  apply (hf'.comp_analyticAt ha).congr
  have ht := (e.symm.continuousAt (e.map_source hx)).tendsto
  rw [e.left_inv hx] at ht
  filter_upwards [nhdsWithin_le_nhds <| ht.eventually
    (e'.eventually_left_inverse hx')] with z hz
  simp [Function.comp_apply, hz]

lemma MMeromorphicAt.iff_of_mem_maximalAtlas {f : M → E} {x : M}
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 M)
    (hx : x ∈ e.source) :
    MMeromorphicAt f x ↔ MeromorphicAt (f ∘ e.symm) (e x) := by
  exact ⟨meromorphicAt_chart_change he (IsManifold.chart_mem_maximalAtlas x)
      hx (mem_chart_source ℂ x),
    meromorphicAt_chart_change (IsManifold.chart_mem_maximalAtlas x) he
      (mem_chart_source ℂ x) hx⟩

end CoordinateIndependence

section HolomorphicPullback

variable [IsManifold 𝓘(ℂ) 1 M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) 1 N]

/-- A manifold differentiable map has an analytic coordinate expression near every point. -/
lemma analyticAt_chart_comp {g : M → N} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (x : M) :
    AnalyticAt ℂ (chartAt ℂ (g x) ∘ g ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  let e := chartAt ℂ x
  let e' := chartAt ℂ (g x)
  have he : x ∈ e.source := mem_chart_source ℂ x
  have he' : g x ∈ e'.source := mem_chart_source ℂ (g x)
  have ht := ((hg (e.symm (e x))).continuousAt.comp
    (e.symm.continuousAt (e.map_source he))).tendsto
  simp only [Function.comp_apply, e.left_inv he] at ht
  filter_upwards [e.open_target.mem_nhds (e.map_source he),
    ht.eventually (e'.open_source.mem_nhds he')] with z hz hz'
  exact ((contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ))
      (IsManifold.chart_mem_maximalAtlas (g x)) hz').mdifferentiableAt one_ne_zero |>.comp z
      ((hg (e.symm z)).comp z
        ((contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ))
          (IsManifold.chart_mem_maximalAtlas x) hz).mdifferentiableAt
            one_ne_zero))).differentiableAt

lemma MMeromorphicAt.comp_mdifferentiable {f : N → E} {g : M → N} {x : M}
    (hf : MMeromorphicAt f (g x)) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    MMeromorphicAt (f ∘ g) x := by
  have ha := analyticAt_chart_comp hg x
  let e := chartAt ℂ x
  let e' := chartAt ℂ (g x)
  have he : x ∈ e.source := mem_chart_source ℂ x
  have he' : g x ∈ e'.source := mem_chart_source ℂ (g x)
  have hf' : MeromorphicAt (f ∘ e'.symm) ((e' ∘ g ∘ e.symm) (e x)) := by
    simpa [Function.comp_apply, e.left_inv he] using hf
  apply (hf'.comp_analyticAt ha).congr
  have ht := ((hg (e.symm (e x))).continuousAt.comp
    (e.symm.continuousAt (e.map_source he))).tendsto
  simp only [Function.comp_apply, e.left_inv he] at ht
  filter_upwards [nhdsWithin_le_nhds <| ht.eventually
    (e'.eventually_left_inverse he')] with z hz
  exact congrArg f hz

lemma MMeromorphic.comp_mdifferentiable {f : N → E} {g : M → N}
    (hf : MMeromorphic f) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    MMeromorphic (f ∘ g) := fun x ↦ (hf (g x)).comp_mdifferentiable hg

lemma MMeromorphicOn.comp_mdifferentiable {f : N → E} {g : M → N}
    {s : Set M} {t : Set N} (hf : MMeromorphicOn f t)
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hgst : MapsTo g s t) :
    MMeromorphicOn (f ∘ g) s := fun x hx ↦ (hf (g x) (hgst hx)).comp_mdifferentiable hg

variable [CompleteSpace E]

/-- Holomorphic functions are meromorphic, with a general complex Banach codomain. -/
lemma _root_.MDifferentiable.mMeromorphic {f : M → E}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, E) f) :
    MMeromorphic f := by
  intro x
  have hd := hf.comp_mdifferentiableOn
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := 1) (x := x)).mdifferentiableOn one_ne_zero)
  exact (hd.differentiableOn.analyticAt (chart_target_mem_nhds ℂ x)).meromorphicAt

end HolomorphicPullback

end MMeromorphicExperiment.Charts
