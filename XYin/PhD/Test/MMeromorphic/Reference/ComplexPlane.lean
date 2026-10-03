/-
Reference experiment adapted from Zhenhua Wu's public MeromorphicFunction repository.
Source: https://github.com/Zeta-Wu/MeromorphicFunction/blob/main/MeromorphicFunction/ComplexPlane.lean
Source blob: 80664cbe86b808d9bad1921dd23036abdc74057b.
-/
import XYin.PhD.Test.MMeromorphic.Reference.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.CommRingCat

open CategoryTheory Opposite
open Set Filter TopologicalSpace
open scoped Topology

namespace MeromorphicFunction

section ComplexPlane

variable {U : Set ℂ} {f g : ℂ → ℂ} {x : ℂ}

lemma eventuallyEq_zero_of_eqOn_zero {V : Set ℂ} (hV : IsOpen V) (hx : x ∈ V)
    (hEq : EqOn f 0 V) :
    f =ᶠ[𝓝 x] 0 := by
  filter_upwards [hV.mem_nhds hx] with z hz
  exact hEq hz

lemma analyticOnNhd_eqOn_zero_connectedComponentIn_of_eventuallyEq_zero
    (hf : AnalyticOnNhd ℂ f U) (hx : x ∈ U) (hfx : f =ᶠ[𝓝 x] 0) :
    EqOn f 0 (connectedComponentIn U x) := by
  let V := connectedComponentIn U x
  have hfV : AnalyticOnNhd ℂ f V :=
    hf.mono (connectedComponentIn_subset U x)
  have hxV : x ∈ V := mem_connectedComponentIn hx
  exact hfV.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_connectedComponentIn hxV hfx

lemma analyticOnNhd_eqOn_connectedComponentIn_of_eventuallyEq
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hx : x ∈ U) (hfgx : f =ᶠ[𝓝 x] g) :
    EqOn f g (connectedComponentIn U x) := by
  let V := connectedComponentIn U x
  have hfV : AnalyticOnNhd ℂ f V :=
    hf.mono (connectedComponentIn_subset U x)
  have hgV : AnalyticOnNhd ℂ g V :=
    hg.mono (connectedComponentIn_subset U x)
  have hxV : x ∈ V := mem_connectedComponentIn hx
  exact hfV.eqOn_of_preconnected_of_eventuallyEq hgV
    isPreconnected_connectedComponentIn hxV hfgx

theorem isOpen_setOf_germ_ne_zero (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) :
    IsOpen {x : ℂ | x ∈ U ∧ ¬ f =ᶠ[𝓝 x] 0} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨hxU, hx_ne⟩
  let V := connectedComponentIn U x
  have hV_open : IsOpen V := hU.connectedComponentIn
  have hxV : x ∈ V := mem_connectedComponentIn hxU
  refine mem_of_superset (hV_open.mem_nhds hxV) ?_
  intro y hyV
  have hyU : y ∈ U := connectedComponentIn_subset U x hyV
  refine ⟨hyU, ?_⟩
  intro hy_zero
  have hEq : EqOn f 0 V :=
    (hf.mono (connectedComponentIn_subset U x)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_connectedComponentIn hyV hy_zero
  have hx_zero : f =ᶠ[𝓝 x] 0 :=
    eventuallyEq_zero_of_eqOn_zero hV_open hxV hEq
  exact hx_ne hx_zero

end ComplexPlane

noncomputable section

section HolomorphicSheaf

abbrev ComplexTopCat : TopCat := TopCat.of ℂ

abbrev opensInclusion {U V : Opens ComplexTopCat} (i : U ⟶ V) : U → V :=
  Opens.inclusion (CategoryTheory.leOfHom i)

abbrev HolomorphicPredicate {U : Opens ComplexTopCat} (f : U → ℂ) : Prop :=
  ∀ x : U,
    ∃ s : Set ℂ, IsOpen s ∧ x.1 ∈ s ∧ s ⊆ (U : Set ℂ) ∧
      ∃ g : ℂ → ℂ,
        EqOn f (fun y : U ↦ g y.1) {y : U | y.1 ∈ s} ∧ AnalyticAt ℂ g x.1

lemma holomorphicPredicate_res {U V : Opens ComplexTopCat} (i : U ⟶ V) {f : V → ℂ}
    (hf : HolomorphicPredicate f) :
    HolomorphicPredicate (fun x : U ↦ f (opensInclusion i x)) := by
  intro x
  rcases hf (opensInclusion i x) with ⟨s, hs_open, hx_s, hsV, g, hEq, hg⟩
  refine ⟨s ∩ (U : Set ℂ), hs_open.inter U.isOpen, ⟨hx_s, x.2⟩, ?_, g, ?_, hg⟩
  · intro y hy
    exact hy.2
  · intro y hy
    exact hEq (show opensInclusion i y ∈ {z : V | z.1 ∈ s} from hy.1)

lemma holomorphicPredicate_locality {U : Opens ComplexTopCat} {f : U → ℂ}
    (h :
      ∀ x : U, ∃ (V : Opens ComplexTopCat) (_ : x.1 ∈ V) (i : V ⟶ U),
        HolomorphicPredicate (fun y : V ↦ f (opensInclusion i y))) :
    HolomorphicPredicate f := by
  intro x
  rcases h x with ⟨V, hxV, i, hi⟩
  rcases hi ⟨x.1, hxV⟩ with ⟨s, hs_open, hx_s, hsV, g, hEq, hg⟩
  refine ⟨s, hs_open, hx_s, ?_, g, ?_, hg⟩
  · intro y hy
    exact i.le (hsV hy)
  · intro y hy
    have hyV : y.1 ∈ V := hsV hy
    simpa using hEq (show (⟨y.1, hyV⟩ : V) ∈ {z : V | z.1 ∈ s} from hy)

def holomorphicLocalPredicate : TopCat.LocalPredicate fun _ : ComplexTopCat ↦ ℂ where
  pred := fun {_} f ↦ HolomorphicPredicate f
  res := by
    intro U V i f hf
    exact holomorphicPredicate_res i hf
  locality := by
    intro U f h
    exact holomorphicPredicate_locality h

lemma holomorphicPredicate_zero {U : Opens ComplexTopCat} :
    holomorphicLocalPredicate.pred (U := U) (fun _ ↦ 0) := by
  intro x
  refine ⟨(U : Set ℂ), U.isOpen, x.2, by intro y hy; exact hy, fun _ ↦ 0, ?_, analyticAt_const⟩
  intro y hy
  rfl

lemma holomorphicPredicate_one {U : Opens ComplexTopCat} :
    holomorphicLocalPredicate.pred (U := U) (fun _ ↦ 1) := by
  intro x
  refine ⟨(U : Set ℂ), U.isOpen, x.2, by intro y hy; exact hy, fun _ ↦ 1, ?_, analyticAt_const⟩
  intro y hy
  rfl

lemma holomorphicPredicate_neg {U : Opens ComplexTopCat} {f : U → ℂ}
    (hf : holomorphicLocalPredicate.pred f) :
    holomorphicLocalPredicate.pred (fun x ↦ -f x) := by
  intro x
  rcases hf x with ⟨s, hs_open, hx_s, hsU, g, hEq, hg⟩
  refine ⟨s, hs_open, hx_s, hsU, fun z ↦ -g z, ?_, hg.neg⟩
  intro y hy
  simp [hEq hy]

lemma holomorphicPredicate_add {U : Opens ComplexTopCat} {f g : U → ℂ}
    (hf : holomorphicLocalPredicate.pred f) (hg : holomorphicLocalPredicate.pred g) :
    holomorphicLocalPredicate.pred (fun x ↦ f x + g x) := by
  intro x
  rcases hf x with ⟨s, hs_open, hx_s, hsU, F, hF, hF_an⟩
  rcases hg x with ⟨t, ht_open, hx_t, htU, G, hG, hG_an⟩
  refine ⟨s ∩ t, hs_open.inter ht_open, ⟨hx_s, hx_t⟩, ?_, fun z ↦ F z + G z, ?_, hF_an.add hG_an⟩
  · intro y hy
    exact hsU hy.1
  · intro y hy
    simp [hF hy.1, hG hy.2]

lemma holomorphicPredicate_mul {U : Opens ComplexTopCat} {f g : U → ℂ}
    (hf : holomorphicLocalPredicate.pred f) (hg : holomorphicLocalPredicate.pred g) :
    holomorphicLocalPredicate.pred (fun x ↦ f x * g x) := by
  intro x
  rcases hf x with ⟨s, hs_open, hx_s, hsU, F, hF, hF_an⟩
  rcases hg x with ⟨t, ht_open, hx_t, htU, G, hG, hG_an⟩
  refine ⟨s ∩ t, hs_open.inter ht_open, ⟨hx_s, hx_t⟩, ?_, fun z ↦ F z * G z, ?_, hF_an.mul hG_an⟩
  · intro y hy
    exact hsU hy.1
  · intro y hy
    simp [hF hy.1, hG hy.2]

def holomorphicSheaf : TopCat.Sheaf (Type _) ComplexTopCat :=
  TopCat.subsheafToTypes holomorphicLocalPredicate

def holomorphicSubring (U : Opens ComplexTopCat) : Subring (U → ℂ) where
  carrier := {f | holomorphicLocalPredicate.pred (U := U) f}
  zero_mem' := holomorphicPredicate_zero
  one_mem' := holomorphicPredicate_one
  add_mem' := holomorphicPredicate_add
  mul_mem' := holomorphicPredicate_mul
  neg_mem' := holomorphicPredicate_neg

instance holomorphicSectionCommRing (U : (Opens ComplexTopCat)ᵒᵖ) :
    CommRing ((holomorphicSheaf).presheaf.obj U) :=
  inferInstanceAs (CommRing (holomorphicSubring (unop U)))

def holomorphicPresheafCommRing : TopCat.Presheaf CommRingCat ComplexTopCat :=
  { obj := fun U ↦ CommRingCat.of ((holomorphicSheaf).presheaf.obj U)
    map := fun i ↦ CommRingCat.ofHom
      { toFun := fun f ↦ ((holomorphicSheaf).presheaf.map i) f
        map_zero' := by
          apply Subtype.ext
          funext x
          rfl
        map_one' := by
          apply Subtype.ext
          funext x
          rfl
        map_add' := by
          intro a b
          apply Subtype.ext
          funext x
          rfl
        map_mul' := by
          intro a b
          apply Subtype.ext
          funext x
          rfl }
    map_id := by
      intro U
      ext f
      apply Subtype.ext
      funext x
      rfl
    map_comp := by
      intro U V W i j
      ext f
      apply Subtype.ext
      funext x
      rfl }

def holomorphicSheafCommRing : TopCat.Sheaf CommRingCat ComplexTopCat where
  obj := holomorphicPresheafCommRing
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact holomorphicSheaf.property

def holomorphicRingedSpace : AlgebraicGeometry.RingedSpace :=
  { carrier := ComplexTopCat
    presheaf := holomorphicSheafCommRing.presheaf
    IsSheaf := holomorphicSheafCommRing.property }

def sectionFun {U : Opens ComplexTopCat} (f : (holomorphicSheaf).presheaf.obj (op U)) : ℂ → ℂ := by
  classical
  exact fun z ↦ if hz : z ∈ U then f.1 ⟨z, hz⟩ else 0

@[simp]
lemma sectionFun_apply {U : Opens ComplexTopCat} (f : (holomorphicSheaf).presheaf.obj (op U))
    {z : ℂ} (hz : z ∈ U) :
    sectionFun f z = f.1 ⟨z, hz⟩ := by
  simp [sectionFun, hz]

def ringSectionFun {U : Opens ComplexTopCat}
    (f : holomorphicSheafCommRing.presheaf.obj (op U)) : ℂ → ℂ := by
  classical
  exact fun z ↦ if hz : z ∈ U then f.1 ⟨z, hz⟩ else 0

@[simp]
lemma ringSectionFun_apply {U : Opens ComplexTopCat}
    (f : holomorphicSheafCommRing.presheaf.obj (op U)) {z : ℂ} (hz : z ∈ U) :
    ringSectionFun f z = f.1 ⟨z, hz⟩ := by
  simp [ringSectionFun, hz]

lemma analyticOnNhd_sectionFun {U : Opens ComplexTopCat}
    (f : (holomorphicSheaf).presheaf.obj (op U)) :
    AnalyticOnNhd ℂ (sectionFun f) U := by
  intro z hz
  rcases f.2 ⟨z, hz⟩ with ⟨s, hs_open, hz_s, hsU, g, hEq, hg⟩
  apply hg.congr
  have hs_nhds : s ∈ 𝓝 z := hs_open.mem_nhds hz_s
  filter_upwards [hs_nhds] with w hw
  have hwU : w ∈ U := hsU hw
  have hw_sub : (⟨w, hwU⟩ : U) ∈ {y : U | y.1 ∈ s} := hw
  simpa [sectionFun, hwU] using (hEq hw_sub).symm

lemma analyticOnNhd_ringSectionFun {U : Opens ComplexTopCat}
    (f : holomorphicSheafCommRing.presheaf.obj (op U)) :
    AnalyticOnNhd ℂ (ringSectionFun f) U := by
  intro z hz
  rcases f.2 ⟨z, hz⟩ with ⟨s, hs_open, hz_s, hsU, g, hEq, hg⟩
  apply hg.congr
  have hs_nhds : s ∈ 𝓝 z := hs_open.mem_nhds hz_s
  filter_upwards [hs_nhds] with w hw
  have hwU : w ∈ U := hsU hw
  have hw_sub : (⟨w, hwU⟩ : U) ∈ {y : U | y.1 ∈ s} := hw
  simpa [ringSectionFun, hwU] using (hEq hw_sub).symm

def holomorphicSheafCommRing_evalAt (x : ComplexTopCat)
    (U : TopologicalSpace.OpenNhds x) :
    holomorphicSheafCommRing.presheaf.obj (Opposite.op U.1) ⟶ CommRingCat.of ℂ :=
  CommRingCat.ofHom
    { toFun := fun f ↦ f.1 ⟨x, U.2⟩
      map_one' := rfl
      map_mul' := by
        intro f g
        rfl
      map_zero' := rfl
      map_add' := by
        intro f g
        rfl }

def holomorphicSheafCommRing_evalHom (x : ComplexTopCat) :
    holomorphicSheafCommRing.presheaf.stalk x ⟶ CommRingCat.of ℂ := by
  refine CategoryTheory.Limits.colimit.desc _ ⟨_, ⟨fun U ↦ ?_, ?_⟩⟩
  · exact holomorphicSheafCommRing_evalAt x (unop U)
  · cat_disch

def holomorphicSheafCommRing_eval (x : ℂ) :
    holomorphicSheafCommRing.presheaf.stalk x →+* ℂ :=
  (holomorphicSheafCommRing_evalHom x).hom

@[simp, reassoc, elementwise]
lemma holomorphicSheafCommRing_ι_evalHom (x : ComplexTopCat) (U) :
    CategoryTheory.Limits.colimit.ι
        ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ holomorphicSheafCommRing.presheaf) U ≫
      holomorphicSheafCommRing_evalHom x =
    holomorphicSheafCommRing_evalAt x (unop U) :=
  CategoryTheory.Limits.colimit.ι_desc _ _

@[simp]
lemma holomorphicSheafCommRing_eval_germ {U : Opens ComplexTopCat} (x : ℂ) (hx : x ∈ U)
    (f : holomorphicSheafCommRing.presheaf.obj (op U)) :
    holomorphicSheafCommRing_eval x (holomorphicSheafCommRing.presheaf.germ U x hx f) =
      f.1 ⟨x, hx⟩ := by
  change
    ((holomorphicSheafCommRing_evalHom x).hom)
      (((CategoryTheory.Limits.colimit.ι
        ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ holomorphicSheafCommRing.presheaf)
        (Opposite.op ⟨U, hx⟩)).hom) f) = _
  exact congr_arg (fun e ↦ e f) (holomorphicSheafCommRing_ι_evalHom x ⟨U, hx⟩)

lemma isUnit_stalk_of_eval_ne_zero {x : ℂ}
    (f : holomorphicSheafCommRing.presheaf.stalk x)
    (hf : holomorphicSheafCommRing_eval x f ≠ 0) :
    IsUnit f := by
  obtain ⟨U, hxU, s, rfl⟩ := holomorphicSheafCommRing.presheaf.exists_germ_eq f
  have hsx_ne_zero : s.1 ⟨x, hxU⟩ ≠ 0 := by
    intro hsx_zero
    apply hf
    rw [holomorphicSheafCommRing_eval_germ x hxU s, hsx_zero]
  have hs_ne : ∀ᶠ z in 𝓝 x, ringSectionFun s z ≠ 0 := by
    have hcont : ContinuousAt (ringSectionFun s) x :=
      (analyticOnNhd_ringSectionFun s x hxU).continuousAt
    exact hcont.eventually_ne (by simpa [ringSectionFun, sectionFun, hxU] using hsx_ne_zero)
  rw [eventually_nhds_iff] at hs_ne
  obtain ⟨V, hV_ne, hV_open, hxV⟩ := hs_ne
  let W : Opens ComplexTopCat := ⟨V ∩ U, hV_open.inter U.isOpen⟩
  have hxW : x ∈ W := ⟨hxV, hxU⟩
  let iWU : W ⟶ U := homOfLE fun z hz => hz.2
  let sW : holomorphicSheafCommRing.presheaf.obj (op W) :=
    holomorphicSheafCommRing.presheaf.map iWU.op s
  have hsW_ne : ∀ y : W, sW.1 y ≠ 0 := by
    intro y
    change s.1 ⟨y.1, y.2.2⟩ ≠ 0
    have hy : ringSectionFun s y.1 ≠ 0 := hV_ne y.1 y.2.1
    intro hzero
    apply hy
    simp [ringSectionFun, hzero]
  let t : holomorphicSheafCommRing.presheaf.obj (op W) :=
    ⟨fun y ↦ (sW.1 y)⁻¹, by
      intro y
      let g : ℂ → ℂ := fun z ↦ (ringSectionFun sW z)⁻¹
      refine ⟨(W : Set ℂ), W.isOpen, y.2, by intro z hz; exact hz, g, ?_, ?_⟩
      · intro z hz
        change (sW.1 z)⁻¹ = (ringSectionFun sW z.1)⁻¹
        rw [ringSectionFun_apply sW z.2]
      · exact ((analyticOnNhd_ringSectionFun sW).inv fun z hz =>
            by
              rw [ringSectionFun_apply sW hz]
              exact hsW_ne ⟨z, hz⟩) y.1 y.2⟩
  refine ⟨⟨holomorphicSheafCommRing.presheaf.germ W x hxW sW,
      holomorphicSheafCommRing.presheaf.germ W x hxW t, ?_, ?_⟩,
      holomorphicSheafCommRing.presheaf.germ_res_apply iWU x hxW s⟩
  · have hmul : sW * t = 1 := by
      apply Subtype.ext
      funext y
      exact mul_inv_cancel₀ (hsW_ne y)
    rw [← map_mul, hmul, map_one]
  · have hmul : t * sW = 1 := by
      apply Subtype.ext
      funext y
      exact inv_mul_cancel₀ (hsW_ne y)
    rw [← map_mul, hmul, map_one]

lemma holomorphicStalk_nontrivial (x : ℂ) :
    Nontrivial (holomorphicSheafCommRing.presheaf.stalk x) := by
  refine ⟨⟨holomorphicSheafCommRing.presheaf.Γgerm x 0,
    holomorphicSheafCommRing.presheaf.Γgerm x 1, ?_⟩⟩
  intro h
  have := congrArg (holomorphicSheafCommRing_eval x) h
  simp at this

lemma stalk_eq_zero_of_eval_eq_zero_and_isUnit {x : ℂ}
    (f : holomorphicSheafCommRing.presheaf.stalk x)
    (hf0 : holomorphicSheafCommRing_eval x f = 0) (hfunit : IsUnit f) : False := by
  rcases hfunit with ⟨u, rfl⟩
  have hunit_eval : IsUnit (holomorphicSheafCommRing_eval x ↑u) := by
    exact IsUnit.map (holomorphicSheafCommRing_eval x) u.isUnit
  rw [hf0] at hunit_eval
  simp at hunit_eval

theorem holomorphicSheafCommRing_isUnit_stalk_iff {x : ℂ}
    (f : holomorphicSheafCommRing.presheaf.stalk x) :
    IsUnit f ↔ holomorphicSheafCommRing_eval x f ≠ 0 := by
  constructor
  · intro hf hzero
    exact stalk_eq_zero_of_eval_eq_zero_and_isUnit f hzero hf
  · intro hf
    exact isUnit_stalk_of_eval_ne_zero f hf

theorem holomorphicSheafCommRing_nonunits_stalk (x : ℂ) :
    nonunits (holomorphicSheafCommRing.presheaf.stalk x) =
      RingHom.ker (holomorphicSheafCommRing_eval x) := by
  ext1 f
  rw [mem_nonunits_iff, not_iff_comm, Iff.comm]
  exact holomorphicSheafCommRing_isUnit_stalk_iff f

lemma germ_eq_zero_iff_eventuallyEq_zero {U : Opens ComplexTopCat} (x : ℂ) (hx : x ∈ U)
    (s : holomorphicSheafCommRing.presheaf.obj (op U)) :
    holomorphicSheafCommRing.presheaf.germ U x hx s = 0 ↔ ringSectionFun s =ᶠ[𝓝 x] 0 := by
  constructor
  · intro hs
    obtain ⟨V, iVU, hxV, hVzero⟩ :=
      holomorphicRingedSpace.exists_res_eq_zero_of_germ_eq_zero U s ⟨x, hx⟩ hs
    refine Filter.mem_of_superset (V.isOpen.mem_nhds hxV) ?_
    intro z hzV
    have hEq := congrFun (congrArg Subtype.val hVzero) ⟨z, hzV⟩
    change ringSectionFun s z = 0
    rw [ringSectionFun_apply s (iVU.le hzV)]
    change s.1 ⟨z, iVU.le hzV⟩ = 0 at hEq
    exact hEq
  · intro hs
    rw [Filter.EventuallyEq, eventually_nhds_iff] at hs
    obtain ⟨V, hVzero, hV_open, hxV⟩ := hs
    let W : Opens ComplexTopCat := ⟨V ∩ U, hV_open.inter U.isOpen⟩
    have hxW : x ∈ W := ⟨hxV, hx⟩
    let iWU : W ⟶ U := homOfLE fun z hz => hz.2
    have hWzero : holomorphicSheafCommRing.presheaf.map iWU.op s = 0 := by
      apply Subtype.ext
      funext y
      change s.1 ⟨y.1, y.2.2⟩ = 0
      have hy : ringSectionFun s y.1 = 0 := hVzero y.1 y.2.1
      rw [ringSectionFun_apply s y.2.2] at hy
      exact hy
    rw [← holomorphicSheafCommRing.presheaf.germ_res_apply iWU x hxW s, hWzero, map_zero]

lemma holomorphicStalk_eq_zero_or_eq_zero_of_mul_eq_zero (x : ℂ)
    (a b : holomorphicSheafCommRing.presheaf.stalk x) (hab : a * b = 0) :
    a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    obtain ⟨U, hxU, s, hs⟩ := holomorphicSheafCommRing.presheaf.exists_germ_eq a
    obtain ⟨V, hVU, hxV, t, ht⟩ := holomorphicSheafCommRing.presheaf.exists_le_germ_eq b hxU
    let iVU : V ⟶ U := homOfLE hVU
    let sV : holomorphicSheafCommRing.presheaf.obj (op V) :=
      holomorphicSheafCommRing.presheaf.map iVU.op s
    have hsV_ne_zero : holomorphicSheafCommRing.presheaf.germ V x hxV sV ≠ 0 := by
      intro hsV_zero
      apply ha
      exact hs.symm.trans <| by
        rw [← holomorphicSheafCommRing.presheaf.germ_res_apply iVU x hxV s]
        exact hsV_zero
    have hprod_germ :
        holomorphicSheafCommRing.presheaf.germ V x hxV (sV * t) = 0 := by
      calc
        holomorphicSheafCommRing.presheaf.germ V x hxV (sV * t)
            = holomorphicSheafCommRing.presheaf.germ V x hxV sV *
                holomorphicSheafCommRing.presheaf.germ V x hxV t := by
                  rw [map_mul]
        _ = a * b := by
              rw [← ht, ← hs, ← holomorphicSheafCommRing.presheaf.germ_res_apply iVU x hxV s]
        _ = 0 := hab
    have hsV_event_ne : ∀ᶠ z in 𝓝[≠] x, ringSectionFun sV z ≠ 0 := by
      rcases (analyticOnNhd_ringSectionFun sV x hxV).eventually_eq_zero_or_eventually_ne_zero with
        hs_zero | hs_ne
      · exact False.elim <| hsV_ne_zero ((germ_eq_zero_iff_eventuallyEq_zero x hxV sV).2 hs_zero)
      · exact hs_ne
    have hprod_event_zero : ringSectionFun (sV * t) =ᶠ[𝓝 x] 0 :=
      (germ_eq_zero_iff_eventuallyEq_zero x hxV (sV * t)).1 hprod_germ
    have ht_event_zero_within : ∀ᶠ z in 𝓝[≠] x, ringSectionFun t z = 0 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hxV), hsV_event_ne,
        hprod_event_zero.filter_mono nhdsWithin_le_nhds] with z hzV hsVnz hprodz
      have : ringSectionFun sV z * ringSectionFun t z = 0 := by
        rw [ringSectionFun_apply sV hzV, ringSectionFun_apply t hzV]
        have hp : ringSectionFun (sV * t) z = 0 := hprodz
        rw [ringSectionFun_apply (sV * t) hzV] at hp
        exact hp
      exact (mul_eq_zero.mp this).resolve_left hsVnz
    have ht_freq_zero : ∃ᶠ z in 𝓝[≠] x, ringSectionFun t z = 0 := ht_event_zero_within.frequently
    have ht_event_zero : ringSectionFun t =ᶠ[𝓝 x] 0 :=
      (analyticOnNhd_ringSectionFun t x hxV).frequently_zero_iff_eventually_zero.mp ht_freq_zero
    exact ht.symm.trans ((germ_eq_zero_iff_eventuallyEq_zero x hxV t).2 ht_event_zero)

instance holomorphicStalk_noZeroDivisors (x : ℂ) :
    NoZeroDivisors (holomorphicSheafCommRing.presheaf.stalk x) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    exact holomorphicStalk_eq_zero_or_eq_zero_of_mul_eq_zero x a b hab

instance holomorphicStalk_nontrivial_inst (x : ℂ) :
    Nontrivial (holomorphicSheafCommRing.presheaf.stalk x) :=
  holomorphicStalk_nontrivial x

instance holomorphicStalk_isDomain (x : ℂ) :
    IsDomain (holomorphicSheafCommRing.presheaf.stalk x) :=
  NoZeroDivisors.to_isDomain _

def holomorphicLocallyRingedSpace : AlgebraicGeometry.LocallyRingedSpace :=
  { carrier := ComplexTopCat
    presheaf := holomorphicSheafCommRing.presheaf
    IsSheaf := holomorphicSheafCommRing.property
    isLocalRing := by
      intro x
      refine IsLocalRing.of_nonunits_add ?_
      rw [holomorphicSheafCommRing_nonunits_stalk]
      intro a b
      exact Ideal.add_mem _ }

instance : AlgebraicGeometry.LocallyRingedSpace.HasDomainStalks holomorphicLocallyRingedSpace where
  isDomain_stalk := holomorphicStalk_isDomain

lemma holomorphic_uniqueContinuation {U : Opens ComplexTopCat}
    (hU : IsPreconnected (U : Set ℂ))
    (s t : holomorphicSheafCommRing.presheaf.obj (op U)) {x : ℂ} (hx : x ∈ U)
    (hst : holomorphicSheafCommRing.presheaf.germ U x hx s =
      holomorphicSheafCommRing.presheaf.germ U x hx t) :
    s = t := by
  obtain ⟨W, hxW, iWU, iWV, hW_eq⟩ :=
    holomorphicSheafCommRing.presheaf.germ_eq x hx hx s t hst
  have hEventual : ringSectionFun s =ᶠ[𝓝 x] ringSectionFun t := by
    refine Filter.mem_of_superset (W.isOpen.mem_nhds hxW) ?_
    intro z hzW
    have hzUs : z ∈ U := iWU.le hzW
    have hzUt : z ∈ U := iWV.le hzW
    have hEq := congrFun (congrArg Subtype.val hW_eq) ⟨z, hzW⟩
    change ringSectionFun s z = ringSectionFun t z
    rw [ringSectionFun_apply s hzUs, ringSectionFun_apply t hzUt]
    change s.1 ⟨z, hzUs⟩ = t.1 ⟨z, hzUt⟩ at hEq
    exact hEq
  have hs_eq :
      EqOn (ringSectionFun s) (ringSectionFun t) (connectedComponentIn (U : Set ℂ) x) :=
    analyticOnNhd_eqOn_connectedComponentIn_of_eventuallyEq
      (analyticOnNhd_ringSectionFun s) (analyticOnNhd_ringSectionFun t) hx hEventual
  have hconn : connectedComponentIn (U : Set ℂ) x = U := hU.connectedComponentIn hx
  apply Subtype.ext
  funext y
  have hy : y.1 ∈ connectedComponentIn (U : Set ℂ) x := by simp [hconn]
  rw [← ringSectionFun_apply s y.2, ← ringSectionFun_apply t y.2]
  have hxy : ringSectionFun s y.1 = ringSectionFun t y.1 := by
    exact hs_eq hy
  exact hxy

instance :
    AlgebraicGeometry.LocallyRingedSpace.UniqueContinuation holomorphicLocallyRingedSpace where
  eq_of_germ_eq := by
    intro U hU s t x hx hst
    exact holomorphic_uniqueContinuation hU s t hx hst

/-- Meromorphic global sections on the complex plane form a field. -/
theorem isField_meromorphicGlobalSections_holomorphicLocallyRingedSpace :
    IsField holomorphicLocallyRingedSpace.meromorphicGlobalSections := by
  let _ : ConnectedSpace holomorphicLocallyRingedSpace := by
    change ConnectedSpace ℂ
    infer_instance
  let _ : LocallyConnectedSpace holomorphicLocallyRingedSpace := by
    change LocallyConnectedSpace ℂ
    infer_instance
  exact
    AlgebraicGeometry.LocallyRingedSpace.isField_meromorphicGlobalSections_of_uniqueContinuation
      holomorphicLocallyRingedSpace

end HolomorphicSheaf

end

end MeromorphicFunction
