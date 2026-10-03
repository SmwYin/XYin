import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import XYin.PhD.Test.MMeromorphic.UpperHalfPlane
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.FieldSimp

/-!
# Local holomorphic fractions on arbitrary complex models

This experimental predicate is stated directly on `f : M → ℂ`. Its denominator is required
to have a dense nonzero locus in the entire chosen neighborhood. Values on its zero locus
are deliberately ignored, as they are for the existing one-variable `MeromorphicAt`.

No finite-dimensionality, connectedness, or manifold compatibility is needed for the elementary
ring API. Those hypotheses belong in subsequent coordinate-invariance, identity-principle,
and field theorems. The intended geometric setting is a boundaryless complex analytic manifold.
-/

open Set Filter
open scoped ContDiff Manifold Topology

namespace MMeromorphicTest.LocalFraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A dense nonzero locus relative to an open domain, expressed without subtype bookkeeping. -/
def RegularDenominator (b : M → ℂ) (U : Set M) : Prop :=
  U ⊆ closure (U ∩ {y | b y ≠ 0})

/-- A pointwise representative is meromorphic at `x` if locally it agrees with a quotient of
analytic manifold functions wherever the denominator is nonzero. -/
def MMeromorphicAt (f : M → ℂ) (x : M) : Prop :=
  ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ a b : M → ℂ,
    ContMDiffOn I 𝓘(ℂ) ω a U ∧ ContMDiffOn I 𝓘(ℂ) ω b U ∧
      RegularDenominator b U ∧ EqOn f (fun y ↦ a y / b y) (U ∩ {y | b y ≠ 0})

/-- The direct local-fraction predicate on all of the manifold. -/
def MMeromorphic (f : M → ℂ) : Prop := ∀ x, MMeromorphicAt I f x

/-- Restriction of the direct predicate to a set. This is a neighborhood predicate rather than
an analogue of differentiability *within* a potentially thin set. -/
def MMeromorphicOn (f : M → ℂ) (s : Set M) : Prop := ∀ x ∈ s, MMeromorphicAt I f x

variable {I}

private theorem regularDenominator_one (U : Set M) :
    RegularDenominator (fun _ : M ↦ (1 : ℂ)) U := by
  simpa [RegularDenominator] using (subset_closure : U ⊆ closure U)

theorem RegularDenominator.mono_open {b : M → ℂ} {U V : Set M}
    (hd : RegularDenominator b U) (hV : IsOpen V) (hVU : V ⊆ U) :
    RegularDenominator b V := by
  intro y hy
  have hcl : y ∈ closure ((U ∩ {z | b z ≠ 0}) ∩ V) :=
    hV.closure_inter ⟨hd (hVU hy), hy⟩
  exact closure_mono (t := V ∩ {z | b z ≠ 0}) (fun z hz ↦ ⟨hz.2, hz.1.2⟩) hcl

private theorem regularDenominator_mul {a b : M → ℂ} {U V : Set M}
    (hV : IsOpen V) (ha : ContMDiffOn I 𝓘(ℂ) ω a U) (hU : IsOpen U)
    (hda : RegularDenominator a U) (hdb : RegularDenominator b V) :
    RegularDenominator (a * b) (U ∩ V) := by
  let A := U ∩ {y | a y ≠ 0}
  let B := V ∩ {y | b y ≠ 0}
  have hAo : IsOpen A := ha.continuousOn.isOpen_inter_preimage hU isOpen_ne
  have hAB : A ∩ V ⊆ closure (A ∩ B) := by
    intro y hy
    exact hAo.inter_closure ⟨hy.1, hdb hy.2⟩
  have hcl : closure (A ∩ V) ⊆ closure (A ∩ B) :=
    closure_minimal hAB isClosed_closure
  intro x hx
  have hxAV : x ∈ closure (A ∩ V) := hV.closure_inter ⟨hda hx.1, hx.2⟩
  apply closure_mono (s := A ∩ B) (t := (U ∩ V) ∩ {y | (a * b) y ≠ 0}) ?_ (hcl hxAV)
  intro y hy
  exact ⟨⟨hy.1.1, hy.2.1⟩, mul_ne_zero hy.1.2 hy.2.2⟩

theorem ContMDiff.mmeromorphic {f : M → ℂ} (hf : ContMDiff I 𝓘(ℂ) ω f) :
    MMeromorphic I f := by
  intro x
  refine ⟨univ, isOpen_univ, mem_univ x, f, fun _ ↦ 1, hf.contMDiffOn,
    contMDiffOn_const, regularDenominator_one univ, ?_⟩
  intro y hy
  simp

theorem mmeromorphic_const (c : ℂ) : MMeromorphic I (fun _ : M ↦ c) :=
  ContMDiff.mmeromorphic contMDiff_const

/-- A globally given quotient gives local witnesses. Equality is only required on the
denominator's regular locus; its values at poles may have been assigned independently. -/
theorem mmeromorphic_of_globalFraction {f a b : M → ℂ}
    (ha : ContMDiff I 𝓘(ℂ) ω a) (hb : ContMDiff I 𝓘(ℂ) ω b)
    (hd : Dense {y | b y ≠ 0}) (heq : EqOn f (fun y ↦ a y / b y) {y | b y ≠ 0}) :
    MMeromorphic I f := by
  intro x
  refine ⟨univ, isOpen_univ, mem_univ x, a, b, ha.contMDiffOn, hb.contMDiffOn, ?_, ?_⟩
  · simpa [RegularDenominator] using (show univ ⊆ closure {y | b y ≠ 0} from fun y _ ↦ hd y)
  · exact fun y hy ↦ heq hy.2

theorem MMeromorphicAt.neg {f : M → ℂ} {x : M} (hf : MMeromorphicAt I f x) :
    MMeromorphicAt I (-f) x := by
  rcases hf with ⟨U, hU, hxU, a, b, ha, hb, hd, heq⟩
  refine ⟨U, hU, hxU, -a, b, ha.neg, hb, hd, ?_⟩
  intro y hy
  change -f y = -a y / b y
  rw [heq hy, neg_div]

theorem MMeromorphicAt.congr_nhds {f g : M → ℂ} {x : M}
    (hf : MMeromorphicAt I f x) (hfg : f =ᶠ[𝓝 x] g) : MMeromorphicAt I g x := by
  rcases hf with ⟨U, hU, hxU, a, b, ha, hb, hd, heq⟩
  obtain ⟨V, hVeq, hV, hxV⟩ := eventually_nhds_iff.mp hfg
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, a, b,
    ha.mono inter_subset_left, hb.mono inter_subset_left,
    hd.mono_open (hU.inter hV) inter_subset_left, ?_⟩
  intro z hz
  exact (hVeq z hz.1.2).symm.trans (heq ⟨hz.1.1, hz.2⟩)

theorem MMeromorphicAt.add {f g : M → ℂ} {x : M}
    (hf : MMeromorphicAt I f x) (hg : MMeromorphicAt I g x) :
    MMeromorphicAt I (f + g) x := by
  rcases hf with ⟨U, hU, hxU, a, b, ha, hb, hdb, heqf⟩
  rcases hg with ⟨V, hV, hxV, c, d, hc, hd, hdd, heqg⟩
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, a * d + c * b, b * d,
    ((ha.mono inter_subset_left).mul (hd.mono inter_subset_right)).add
      ((hc.mono inter_subset_right).mul (hb.mono inter_subset_left)),
    (hb.mono inter_subset_left).mul (hd.mono inter_subset_right),
    regularDenominator_mul hV hb hU hdb hdd, ?_⟩
  intro y hy
  have hby : b y ≠ 0 := (mul_ne_zero_iff.mp hy.2).1
  have hdy : d y ≠ 0 := (mul_ne_zero_iff.mp hy.2).2
  change f y + g y = (a y * d y + c y * b y) / (b y * d y)
  rw [heqf ⟨hy.1.1, hby⟩, heqg ⟨hy.1.2, hdy⟩]
  field_simp

theorem MMeromorphicAt.mul {f g : M → ℂ} {x : M}
    (hf : MMeromorphicAt I f x) (hg : MMeromorphicAt I g x) :
    MMeromorphicAt I (f * g) x := by
  rcases hf with ⟨U, hU, hxU, a, b, ha, hb, hdb, heqf⟩
  rcases hg with ⟨V, hV, hxV, c, d, hc, hd, hdd, heqg⟩
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, a * c, b * d,
    (ha.mono inter_subset_left).mul (hc.mono inter_subset_right),
    (hb.mono inter_subset_left).mul (hd.mono inter_subset_right),
    regularDenominator_mul hV hb hU hdb hdd, ?_⟩
  intro y hy
  have hby : b y ≠ 0 := (mul_ne_zero_iff.mp hy.2).1
  have hdy : d y ≠ 0 := (mul_ne_zero_iff.mp hy.2).2
  change f y * g y = (a y * c y) / (b y * d y)
  rw [heqf ⟨hy.1.1, hby⟩, heqg ⟨hy.1.2, hdy⟩, div_mul_div_comm]

theorem MMeromorphic.neg {f : M → ℂ} (hf : MMeromorphic I f) : MMeromorphic I (-f) :=
  fun x ↦ (hf x).neg

theorem MMeromorphic.add {f g : M → ℂ} (hf : MMeromorphic I f) (hg : MMeromorphic I g) :
    MMeromorphic I (f + g) := fun x ↦ (hf x).add (hg x)

theorem MMeromorphic.mul {f g : M → ℂ} (hf : MMeromorphic I f) (hg : MMeromorphic I g) :
    MMeromorphic I (f * g) := fun x ↦ (hf x).mul (hg x)

theorem MMeromorphic.sub {f g : M → ℂ} (hf : MMeromorphic I f) (hg : MMeromorphic I g) :
    MMeromorphic I (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Inversion with an explicitly regular numerator. The original denominator is retained in
the new denominator so that arbitrary values on the old exceptional locus are still ignored. -/
theorem mmeromorphicAt_inv_of_regularFraction {f a b : M → ℂ} {U : Set M} {x : M}
    (hU : IsOpen U) (hxU : x ∈ U) (ha : ContMDiffOn I 𝓘(ℂ) ω a U)
    (hb : ContMDiffOn I 𝓘(ℂ) ω b U) (hda : RegularDenominator a U)
    (hdb : RegularDenominator b U)
    (heq : EqOn f (fun y ↦ a y / b y) (U ∩ {y | b y ≠ 0})) :
    MMeromorphicAt I f⁻¹ x := by
  refine ⟨U ∩ U, hU.inter hU, ⟨hxU, hxU⟩, b * b, a * b,
    (hb.mono inter_subset_left).mul (hb.mono inter_subset_right),
    (ha.mono inter_subset_left).mul (hb.mono inter_subset_right),
    regularDenominator_mul hU ha hU hda hdb, ?_⟩
  intro y hy
  have hay : a y ≠ 0 := (mul_ne_zero_iff.mp hy.2).1
  have hby : b y ≠ 0 := (mul_ne_zero_iff.mp hy.2).2
  change (f y)⁻¹ = b y * b y / (a y * b y)
  rw [heq ⟨hy.1.1, hby⟩, inv_div]
  field_simp

/-- Inversion when the local numerator is identically zero. -/
theorem mmeromorphicAt_inv_of_zeroFraction {f a b : M → ℂ} {U : Set M} {x : M}
    (hU : IsOpen U) (hxU : x ∈ U) (hb : ContMDiffOn I 𝓘(ℂ) ω b U)
    (hdb : RegularDenominator b U) (ha : EqOn a 0 U)
    (heq : EqOn f (fun y ↦ a y / b y) (U ∩ {y | b y ≠ 0})) :
    MMeromorphicAt I f⁻¹ x := by
  refine ⟨U, hU, hxU, 0, b, contMDiffOn_const, hb, hdb, ?_⟩
  intro y hy
  change (f y)⁻¹ = 0 / b y
  simp only [heq hy, ha hy.1, Pi.zero_apply, zero_div, inv_zero]

section Pullback

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℂ F K}
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N]

/-- Open analytic pullbacks preserve the direct local fraction predicate. Openness guarantees
that a denominator's dense regular locus stays dense after pullback. -/
theorem MMeromorphicAt.comp_open {f : M → ℂ} {h : N → M} {x : N}
    (hf : MMeromorphicAt I f (h x)) (hh : ContMDiff J I ω h) (ho : IsOpenMap h) :
    MMeromorphicAt J (f ∘ h) x := by
  rcases hf with ⟨U, hU, hxU, a, b, ha, hb, hd, heq⟩
  refine ⟨h ⁻¹' U, hU.preimage hh.continuous, hxU, a ∘ h, b ∘ h,
    ha.comp hh.contMDiffOn (fun _ hy ↦ hy),
    hb.comp hh.contMDiffOn (fun _ hy ↦ hy), ?_, ?_⟩
  · intro y hy
    exact ho.preimage_closure_subset_closure_preimage (hd hy)
  · intro y hy
    exact heq hy

theorem MMeromorphic.comp_open {f : M → ℂ} {h : N → M} (hf : MMeromorphic I f)
    (hh : ContMDiff J I ω h) (ho : IsOpenMap h) : MMeromorphic J (f ∘ h) :=
  fun x ↦ (hf (h x)).comp_open hh ho

/-- Local analytic changes of coordinates preserve the predicate. An open partial
homeomorphism only needs to be analytic on its source. -/
theorem MMeromorphicAt.comp_partialHomeomorph {f : M → ℂ}
    {e : OpenPartialHomeomorph N M} {x : N} (hf : MMeromorphicAt I f (e x))
    (hx : x ∈ e.source) (he : ContMDiffOn J I ω e e.source) :
    MMeromorphicAt J (f ∘ e) x := by
  rcases hf with ⟨U, hU, hxU, a, b, ha, hb, hd, heq⟩
  let V := e.source ∩ e ⁻¹' U
  have hV : IsOpen V := he.continuousOn.isOpen_inter_preimage e.open_source hU
  refine ⟨V, hV, ⟨hx, hxU⟩, a ∘ e, b ∘ e,
    ha.comp (he.mono inter_subset_left) inter_subset_right,
    hb.comp (he.mono inter_subset_left) inter_subset_right, ?_, ?_⟩
  · intro y hy
    have hyc : y ∈ e.source ∩ closure (e ⁻¹' (U ∩ {z | b z ≠ 0})) := by
      rw [← e.preimage_closure]
      exact ⟨hy.1, hd hy.2⟩
    simpa only [V, preimage_inter, ← inter_assoc, preimage_setOf_eq] using
      e.open_source.inter_closure hyc
  · intro y hy
    exact heq ⟨hy.1.2, hy.2⟩

end Pullback

section OneVariable

private theorem regularDenominator_eventually_ne_zero {b : ℂ → ℂ} {U : Set ℂ} {x : ℂ}
    (hxU : x ∈ U) (hd : RegularDenominator b U)
    (hb : AnalyticAt ℂ b x) : ∀ᶠ z in 𝓝[≠] x, b z ≠ 0 := by
  rcases hb.eventually_eq_zero_or_eventually_ne_zero with hz | hn
  · obtain ⟨V, hVzero, hV, hxV⟩ := eventually_nhds_iff.mp hz
    obtain ⟨z, hzV, hzreg⟩ := mem_closure_iff.mp (hd hxU) V hV hxV
    exact False.elim (hzreg.2 (hVzero z hzV))
  · exact hn

/-- On the complex line, the local fraction predicate agrees with mathlib's established
punctured-neighborhood definition, including its freedom to choose a value at a pole. -/
theorem mmeromorphicAt_iff_meromorphicAt {f : ℂ → ℂ} {x : ℂ} :
    MMeromorphicAt 𝓘(ℂ) f x ↔ MeromorphicAt f x := by
  constructor
  · rintro ⟨U, hU, hxU, a, b, ha, hb, hd, heq⟩
    have haan : AnalyticAt ℂ a x :=
      ((ha x hxU).contMDiffAt (hU.mem_nhds hxU)).contDiffAt.analyticAt
    have hban : AnalyticAt ℂ b x :=
      ((hb x hxU).contMDiffAt (hU.mem_nhds hxU)).contDiffAt.analyticAt
    have hn := regularDenominator_eventually_ne_zero hxU hd hban
    have hfg : (fun z ↦ a z / b z) =ᶠ[𝓝[≠] x] f := by
      filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hxU), hn] with z hzU hz
      exact (heq ⟨hzU, hz⟩).symm
    exact (haan.meromorphicAt.div hban.meromorphicAt).congr hfg
  · rintro ⟨n, haan⟩
    let a : ℂ → ℂ := fun z ↦ (z - x) ^ n • f z
    let b : ℂ → ℂ := fun z ↦ (z - x) ^ n
    have haat : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω a x := haan.contDiffAt.contMDiffAt
    obtain ⟨U, hxU, haU⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp haat
    obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hxU
    have hb : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω b :=
      ((contDiff_id.sub contDiff_const).pow n).contMDiff
    have hdb : Dense {z | b z ≠ 0} := (dense_compl_singleton x).mono fun z hz ↦
      pow_ne_zero n (sub_ne_zero.mpr hz)
    refine ⟨V, hV, hxV, a, b, haU.mono hVU, hb.contMDiffOn,
      hdb.open_subset_closure_inter hV, ?_⟩
    intro z hz
    change f z = ((z - x) ^ n * f z) / (z - x) ^ n
    exact (mul_div_cancel_left₀ (f z) hz.2).symm

theorem mmeromorphic_iff_meromorphicOn {f : ℂ → ℂ} :
    MMeromorphic 𝓘(ℂ) f ↔ MeromorphicOn f univ := by
  simp only [MMeromorphic, MeromorphicOn, mem_univ, forall_const,
    mmeromorphicAt_iff_meromorphicAt]

/-- The existing one-variable API supplies unrestricted inversion after the comparison. -/
theorem MMeromorphicAt.inv_complex {f : ℂ → ℂ} {x : ℂ} (hf : MMeromorphicAt 𝓘(ℂ) f x) :
    MMeromorphicAt 𝓘(ℂ) f⁻¹ x :=
  mmeromorphicAt_iff_meromorphicAt.mpr (mmeromorphicAt_iff_meromorphicAt.mp hf).inv

theorem MMeromorphic.inv_complex {f : ℂ → ℂ} (hf : MMeromorphic 𝓘(ℂ) f) :
    MMeromorphic 𝓘(ℂ) f⁻¹ := fun x ↦ (hf x).inv_complex

end OneVariable

section NormedModel

/-- The direct local fraction predicate is closed under inversion on arbitrary complex normed
models. The proof uses the several-variable analytic identity principle on a connected ball;
it does not require finite-dimensionality or completeness of the domain. -/
theorem MMeromorphicAt.inv_normed {f : E → ℂ} {x : E}
    (hf : MMeromorphicAt 𝓘(ℂ, E) f x) : MMeromorphicAt 𝓘(ℂ, E) f⁻¹ x := by
  rcases hf with ⟨U, hU, hxU, a, b, ha, hb, hd, heq⟩
  by_cases hazero : a =ᶠ[𝓝 x] 0
  · obtain ⟨V, hVzero, hV, hxV⟩ := eventually_nhds_iff.mp hazero
    apply mmeromorphicAt_inv_of_zeroFraction (a := a) (b := b) (U := U ∩ V)
      (hU.inter hV) ⟨hxU, hxV⟩ (hb.mono inter_subset_left)
      (hd.mono_open (hU.inter hV) inter_subset_left)
    · exact fun z hz ↦ hVzero z hz.2
    · exact fun z hz ↦ heq ⟨hz.1.1, hz.2⟩
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hxU
    let V : Set E := Metric.ball x r
    have hV : IsOpen V := Metric.isOpen_ball
    have hxV : x ∈ V := Metric.mem_ball_self hr
    have haa : AnalyticOnNhd ℂ a V := fun z hz ↦
      ((ha z (hball hz)).contMDiffAt (hU.mem_nhds (hball hz))).contDiffAt.analyticAt
    have hda : RegularDenominator a V := by
      intro y hy
      apply mem_closure_iff.mpr
      intro O hO hyO
      by_contra hnone
      have hazero_y : a =ᶠ[𝓝 y] 0 := by
        filter_upwards [(hO.inter hV).mem_nhds ⟨hyO, hy⟩] with z hz
        by_contra hn
        exact hnone ⟨z, hz.1, ⟨hz.2, hn⟩⟩
      have hzero := haa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        Metric.isPreconnected_ball hy hazero_y
      apply hazero
      filter_upwards [hV.mem_nhds hxV] with z hz
      exact hzero hz
    apply mmeromorphicAt_inv_of_regularFraction (a := a) (b := b) (U := V) hV hxV
      (ha.mono hball) (hb.mono hball) hda (hd.mono_open hV hball)
    exact fun z hz ↦ heq ⟨hball hz.1, hz.2⟩

theorem MMeromorphic.inv_normed {f : E → ℂ} (hf : MMeromorphic 𝓘(ℂ, E) f) :
    MMeromorphic 𝓘(ℂ, E) f⁻¹ := fun x ↦ (hf x).inv_normed

theorem MMeromorphicAt.div_normed {f g : E → ℂ} {x : E}
    (hf : MMeromorphicAt 𝓘(ℂ, E) f x) (hg : MMeromorphicAt 𝓘(ℂ, E) g x) :
    MMeromorphicAt 𝓘(ℂ, E) (f / g) x := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv_normed

theorem MMeromorphic.div_normed {f g : E → ℂ}
    (hf : MMeromorphic 𝓘(ℂ, E) f) (hg : MMeromorphic 𝓘(ℂ, E) g) :
    MMeromorphic 𝓘(ℂ, E) (f / g) := fun x ↦ (hf x).div_normed (hg x)

end NormedModel

section AnalyticManifold

variable {A : Type*} [TopologicalSpace A] [ChartedSpace E A]
  [IsManifold 𝓘(ℂ, E) ω A]

/-- Inversion on boundaryless analytic complex manifolds with arbitrary normed model.
The chart transport is proved through local analytic fractions rather than assumed. -/
theorem MMeromorphicAt.inv_manifold {f : A → ℂ} {x : A}
    (hf : MMeromorphicAt 𝓘(ℂ, E) f x) : MMeromorphicAt 𝓘(ℂ, E) f⁻¹ x := by
  let e := chartAt E x
  have hx : x ∈ e.source := mem_chart_source E x
  have hf' : MMeromorphicAt 𝓘(ℂ, E) f (e.symm (e x)) := by
    simpa only [e.left_inv hx] using hf
  have hc := hf'.comp_partialHomeomorph (e.map_source hx) (contMDiffOn_chart_symm (I := 𝓘(ℂ, E)))
  have hinv := hc.inv_normed
  have hpull := hinv.comp_partialHomeomorph hx (contMDiffOn_chart (I := 𝓘(ℂ, E)))
  apply hpull.congr_nhds
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_def, Pi.inv_apply, e.left_inv hy]

theorem MMeromorphic.inv_manifold {f : A → ℂ} (hf : MMeromorphic 𝓘(ℂ, E) f) :
    MMeromorphic 𝓘(ℂ, E) f⁻¹ := fun x ↦ (hf x).inv_manifold

end AnalyticManifold

section UpperHalfPlane

open UpperHalfPlane

/-- The direct local holomorphic fraction predicate gives exactly the upper half-plane
condition used by the modular-function experiment. -/
theorem mmeromorphicAt_upperHalfPlane_iff {f : ℍ → ℂ} {τ : ℍ} :
    MMeromorphicAt 𝓘(ℂ) f τ ↔ MeromorphicAt (f ∘ ofComplex) (τ : ℂ) := by
  constructor
  · intro hf
    have hf' : MMeromorphicAt 𝓘(ℂ) f (ofComplex (τ : ℂ)) := by
      simpa only [ofComplex_apply] using hf
    apply mmeromorphicAt_iff_meromorphicAt.mp
    apply hf'.comp_partialHomeomorph (by simpa [ofComplex, range_coe] using τ.im_pos)
    intro z hz
    have hz' : 0 < z.im := by simpa [ofComplex, range_coe] using hz
    exact (contMDiffAt_ofComplex hz').contMDiffWithinAt
  · intro hf
    have hc := (mmeromorphicAt_iff_meromorphicAt.mpr hf).comp_open
      (contMDiff_coe (n := ω)) isOpenEmbedding_coe.isOpenMap
    simpa only [Function.comp_def, ofComplex_apply] using hc

theorem mmeromorphic_upperHalfPlane_iff {f : ℍ → ℂ} :
    MMeromorphic 𝓘(ℂ) f ↔ MMeromorphicTest.UHP.Meromorphic f := by
  rw [MMeromorphicTest.UHP.iff_forall]
  exact forall_congr' fun τ ↦ mmeromorphicAt_upperHalfPlane_iff

end UpperHalfPlane

end MMeromorphicTest.LocalFraction
