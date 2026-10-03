import XYin.PhD.Test.MMeromorphic.SheafLocalBridge
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Analysis.Meromorphic.IsolatedZeros

/-!
# Gluing direct meromorphic functions into the reference sheaf

Certified local fractions describing the same raw function have identical analytic
cross-products on overlaps. Their localizations, hence their sheafifications, agree.
The sheaf gluing theorem then constructs a global meromorphic section from the direct
`MeromorphicOn` predicate. This forward construction does not yet assert a global isomorphism.
-/

open CategoryTheory Opposite AlgebraicGeometry Filter Set TopologicalSpace
open TopologicalSpace.Opens
open scoped Topology nonZeroDivisors

namespace MMeromorphicTest.SheafLocalBridge

open MeromorphicFunction

noncomputable section

namespace LocalSheafFraction

variable {f : ℂ → ℂ} {x : ℂ}

/-- A stalkwise regular denominator does not vanish on a sufficiently small punctured
neighborhood of any point in its domain. -/
lemma denominator_eventually_ne_zero (q : LocalSheafFraction f x) {z : ℂ}
    (hz : z ∈ q.domain) : ∀ᶠ w in 𝓝[≠] z, ringSectionFun q.denominator w ≠ 0 := by
  have hg : X.presheaf.germ q.domain z hz q.denominator ≠ 0 := by
    have hreg := q.denominator_regular
    simp only [LocallyRingedSpace.meromorphicSubmonoidPresheaf,
      TopCat.Presheaf.submonoidPresheafOfStalk_obj, Submonoid.mem_iInf,
      Submonoid.mem_comap] at hreg
    exact mem_nonZeroDivisors_iff_ne_zero.mp (hreg ⟨z, hz⟩)
  have hb := analyticOnNhd_ringSectionFun q.denominator z hz
  exact hb.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hzero ↦
    hg ((germ_eq_zero_iff_eventuallyEq_zero z hz q.denominator).mpr hzero)

private lemma eventually_ne_fixed_center (z x : ℂ) : ∀ᶠ w in 𝓝[≠] z, w ≠ x := by
  by_cases hzx : z = x
  · subst x
    exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds (eventually_ne_nhds hzx)

/-- Equality on a punctured neighborhood identifies the analytic cross-products, even
at the center where a denominator can vanish. -/
lemma cross_mul_eq_of_eventuallyEq {g : ℂ → ℂ} {y : ℂ}
    (q : LocalSheafFraction f x) (r : LocalSheafFraction g y)
    (z : ↥(q.domain ⊓ r.domain)) (hfg : f =ᶠ[𝓝[≠] (z : ℂ)] g) :
    q.numerator.val ⟨z, z.property.1⟩ * r.denominator.val ⟨z, z.property.2⟩ =
      r.numerator.val ⟨z, z.property.2⟩ * q.denominator.val ⟨z, z.property.1⟩ := by
  have ha := analyticOnNhd_ringSectionFun q.numerator z z.property.1
  have hb := analyticOnNhd_ringSectionFun q.denominator z z.property.1
  have hc := analyticOnNhd_ringSectionFun r.numerator z z.property.2
  have hd := analyticOnNhd_ringSectionFun r.denominator z z.property.2
  have heq : (fun w ↦ ringSectionFun q.numerator w * ringSectionFun r.denominator w)
      =ᶠ[𝓝[≠] (z : ℂ)]
      (fun w ↦ ringSectionFun r.numerator w * ringSectionFun q.denominator w) := by
    filter_upwards [q.denominator_eventually_ne_zero z.property.1,
      r.denominator_eventually_ne_zero z.property.2,
      eventually_ne_fixed_center z x, eventually_ne_fixed_center z y,
      nhdsWithin_le_nhds (q.domain.isOpen.mem_nhds z.property.1),
      nhdsWithin_le_nhds (r.domain.isOpen.mem_nhds z.property.2), hfg]
      with w hbw hdw hwx hwy hwq hwr hwfg
    have hq := q.eq_away_center ⟨w, hwq⟩ hwx
    have hr := r.eq_away_center ⟨w, hwr⟩ hwy
    rw [hwfg, hr] at hq
    have hbw' : q.denominator.val ⟨w, hwq⟩ ≠ 0 := by
      simpa only [ringSectionFun_apply _ hwq] using hbw
    have hdw' : r.denominator.val ⟨w, hwr⟩ ≠ 0 := by
      simpa only [ringSectionFun_apply _ hwr] using hdw
    have hcross := (div_eq_div_iff hdw' hbw').mp hq
    simpa only [ringSectionFun_apply _ hwq, ringSectionFun_apply _ hwr] using hcross.symm
  have hordinary := ((ha.fun_mul hd).frequently_eq_iff_eventually_eq
    (hc.fun_mul hb)).mp heq.frequently
  simpa only [ringSectionFun_apply _ z.property.1, ringSectionFun_apply _ z.property.2] using
    Filter.EventuallyEq.eq_of_nhds hordinary

/-- Local fractions describing the same raw function have equal analytic cross-products
throughout every overlap, including points where the denominators vanish. -/
lemma cross_mul_eq {y : ℂ} (q : LocalSheafFraction f x) (r : LocalSheafFraction f y)
    (z : ↥(q.domain ⊓ r.domain)) :
    q.numerator.val ⟨z, z.property.1⟩ * r.denominator.val ⟨z, z.property.2⟩ =
      r.numerator.val ⟨z, z.property.2⟩ * q.denominator.val ⟨z, z.property.1⟩ :=
  q.cross_mul_eq_of_eventuallyEq r z (EventuallyEq.rfl)

set_option backward.isDefEq.respectTransparency false in
lemma map_toPresheaf {V : Opens ComplexTopCat} (q : LocalSheafFraction f x)
    (i : V ⟶ q.domain) :
    X.meromorphicPresheaf.map i.op q.toPresheaf =
      Localization.mk (X.presheaf.map i.op q.numerator)
        ⟨X.presheaf.map i.op q.denominator,
          X.meromorphicSubmonoidPresheaf.map i.op q.denominator_regular⟩ := by
  change (IsLocalization.map (Localization (X.meromorphicSubmonoidPresheaf.obj (op V)))
    (X.presheaf.map i.op).hom (X.meromorphicSubmonoidPresheaf.map i.op))
      (Localization.mk q.numerator ⟨q.denominator, q.denominator_regular⟩) = _
  simp only [Localization.mk_eq_mk', IsLocalization.map_mk']

set_option backward.isDefEq.respectTransparency false in
lemma toPresheaf_overlap {y : ℂ} (q : LocalSheafFraction f x) (r : LocalSheafFraction f y) :
    X.meromorphicPresheaf.map (infLELeft q.domain r.domain).op q.toPresheaf =
      X.meromorphicPresheaf.map (infLERight q.domain r.domain).op r.toPresheaf := by
  rw [map_toPresheaf, map_toPresheaf]
  simp only [Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_of_eq'
    (S := Localization (X.meromorphicSubmonoidPresheaf.obj (op (q.domain ⊓ r.domain))))
  apply Subtype.ext
  funext z
  exact r.cross_mul_eq q ⟨z, ⟨z.property.2, z.property.1⟩⟩

lemma toSheaf_overlap {y : ℂ} (q : LocalSheafFraction f x) (r : LocalSheafFraction f y) :
    X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op q.toSheaf =
      X.meromorphicSheaf.presheaf.map (infLERight q.domain r.domain).op r.toSheaf := by
  let α := CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
    X.meromorphicPresheaf
  have hq := congrArg (fun k ↦ k q.toPresheaf)
    (α.naturality (infLELeft q.domain r.domain).op)
  have hr := congrArg (fun k ↦ k r.toPresheaf)
    (α.naturality (infLERight q.domain r.domain).op)
  simp only [ConcreteCategory.comp_apply] at hq hr
  exact hq.symm.trans ((congrArg (α.app _) (q.toPresheaf_overlap r)).trans hr)

set_option backward.isDefEq.respectTransparency false in
/-- Codiscretely equal direct meromorphic functions define the same localized section
on every overlap of certified local fractions. -/
lemma toPresheaf_overlap_of_codiscrete {g : ℂ → ℂ} {y : ℂ}
    (q : LocalSheafFraction f x) (r : LocalSheafFraction g y)
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (hfg : f =ᶠ[codiscreteWithin (univ : Set ℂ)] g) :
    X.meromorphicPresheaf.map (infLELeft q.domain r.domain).op q.toPresheaf =
      X.meromorphicPresheaf.map (infLERight q.domain r.domain).op r.toPresheaf := by
  rw [map_toPresheaf, map_toPresheaf]
  simp only [Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_of_eq'
    (S := Localization (X.meromorphicSubmonoidPresheaf.obj (op (q.domain ⊓ r.domain))))
  apply Subtype.ext
  funext z
  exact r.cross_mul_eq_of_eventuallyEq q ⟨z, ⟨z.property.2, z.property.1⟩⟩
    ((hg z (mem_univ z)).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (hf z (mem_univ z)) (mem_univ z) isOpen_univ.preperfect hfg.symm)

/-- Codiscrete equality also identifies the sheafified local sections. -/
lemma toSheaf_overlap_of_codiscrete {g : ℂ → ℂ} {y : ℂ}
    (q : LocalSheafFraction f x) (r : LocalSheafFraction g y)
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (hfg : f =ᶠ[codiscreteWithin (univ : Set ℂ)] g) :
    X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op q.toSheaf =
      X.meromorphicSheaf.presheaf.map (infLERight q.domain r.domain).op r.toSheaf := by
  let α := CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
    X.meromorphicPresheaf
  have hq := congrArg (fun k ↦ k q.toPresheaf)
    (α.naturality (infLELeft q.domain r.domain).op)
  have hr := congrArg (fun k ↦ k r.toPresheaf)
    (α.naturality (infLERight q.domain r.domain).op)
  simp only [ConcreteCategory.comp_apply] at hq hr
  exact hq.symm.trans ((congrArg (α.app _)
    (q.toPresheaf_overlap_of_codiscrete r hf hg hfg)).trans hr)

end LocalSheafFraction

/-- Fractions coming from direct meromorphy glue to a unique global sheaf section. -/
theorem existsUnique_globalSection {f : ℂ → ℂ} (hf : MeromorphicOn f univ) :
    ∃! s : X.meromorphicGlobalSections, ∀ x : ℂ,
      X.meromorphicSheaf.presheaf.map (homOfLE
        (le_top : (localSheafFraction (hf x (mem_univ x))).domain ≤ ⊤)).op s =
        (localSheafFraction (hf x (mem_univ x))).toSheaf := by
  let q := fun x : ℂ ↦ localSheafFraction (hf x (mem_univ x))
  let U := fun x : ℂ ↦ (q x).domain
  have hcover : (⊤ : Opens ComplexTopCat) ≤ iSup U := by
    intro z hz
    exact Opens.mem_iSup.mpr ⟨z, (q z).point_mem⟩
  have hcompatible : TopCat.Presheaf.IsCompatible X.meromorphicSheaf.presheaf U
      (fun x ↦ (q x).toSheaf) := fun x y ↦ (q x).toSheaf_overlap (q y)
  exact X.meromorphicSheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
    hcover (fun x ↦ (q x).toSheaf) hcompatible

/-- A global meromorphic sheaf section constructed from the raw analytic predicate. -/
def globalSection {f : ℂ → ℂ} (hf : MeromorphicOn f univ) : X.meromorphicGlobalSections :=
  (existsUnique_globalSection hf).choose

lemma globalSection_restrict {f : ℂ → ℂ} (hf : MeromorphicOn f univ) (x : ℂ) :
    X.meromorphicSheaf.presheaf.map (homOfLE
      (le_top : (localSheafFraction (hf x (mem_univ x))).domain ≤ ⊤)).op (globalSection hf) =
      (localSheafFraction (hf x (mem_univ x))).toSheaf :=
  (existsUnique_globalSection hf).choose_spec.1 x

/-- The forward construction forgets arbitrary values on discrete subsets, as the
codiscrete quotient construction does. -/
theorem globalSection_congr {f g : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (hfg : f =ᶠ[codiscreteWithin (univ : Set ℂ)] g) :
    globalSection hf = globalSection hg := by
  apply TopCat.Presheaf.IsSheaf.section_ext X.meromorphicSheaf.property
  intro x hx
  let q := localSheafFraction (hf x (mem_univ x))
  let r := localSheafFraction (hg x (mem_univ x))
  refine ⟨q.domain ⊓ r.domain, le_top, ⟨q.point_mem, r.point_mem⟩, ?_⟩
  have hq := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op k)
      (globalSection_restrict hf x)
  have hr := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (infLERight q.domain r.domain).op k)
      (globalSection_restrict hg x)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hq hr
  exact hq.trans ((q.toSheaf_overlap_of_codiscrete r hf hg hfg).trans hr.symm)

example : X.meromorphicGlobalSections :=
  globalSection (MeromorphicOn.const 1)

example : X.meromorphicGlobalSections :=
  globalSection (MeromorphicOn.id.inv : MeromorphicOn (fun z : ℂ ↦ z⁻¹) univ)

#print axioms LocalSheafFraction.toSheaf_overlap
#print axioms existsUnique_globalSection
#print axioms globalSection
#print axioms globalSection_congr

end

end MMeromorphicTest.SheafLocalBridge
