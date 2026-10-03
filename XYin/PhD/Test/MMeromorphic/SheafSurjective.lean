import XYin.PhD.Test.MMeromorphic.SheafLiftData
import XYin.PhD.Test.MMeromorphic.SheafFractionEquality
import XYin.PhD.Test.MMeromorphic.NormalGluing

/-!
# Recovering global normal representatives from meromorphic sheaf sections

Local fraction lifts agree as punctured germs because their sheafifications agree. Normalize
these representatives, glue their actual values, and compare their sheafification with the
original section. This is the reverse construction from sheaf sections to an analytic predicate.
-/

open CategoryTheory Opposite AlgebraicGeometry Filter Set TopologicalSpace
open TopologicalSpace.Opens
open scoped Topology nonZeroDivisors

namespace MMeromorphicTest.SheafLocalBridge

open MeromorphicFunction

noncomputable section

namespace LocalSheafFraction

variable {f g : ℂ → ℂ} {x y : ℂ}

set_option backward.isDefEq.respectTransparency false in
lemma toPresheaf_overlap_of_localEq (q : LocalSheafFraction f x)
    (r : LocalSheafFraction g y)
    (hfg : ∀ z ∈ q.domain ⊓ r.domain, f =ᶠ[𝓝[≠] z] g) :
    X.meromorphicPresheaf.map (infLELeft q.domain r.domain).op q.toPresheaf =
      X.meromorphicPresheaf.map (infLERight q.domain r.domain).op r.toPresheaf := by
  rw [map_toPresheaf, map_toPresheaf]
  simp only [Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_of_eq'
    (S := Localization (X.meromorphicSubmonoidPresheaf.obj (op (q.domain ⊓ r.domain))))
  apply Subtype.ext
  funext z
  exact r.cross_mul_eq_of_eventuallyEq q ⟨z, ⟨z.property.2, z.property.1⟩⟩
    (hfg z z.property).symm

lemma toSheaf_overlap_of_localEq (q : LocalSheafFraction f x)
    (r : LocalSheafFraction g y)
    (hfg : ∀ z ∈ q.domain ⊓ r.domain, f =ᶠ[𝓝[≠] z] g) :
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
    (q.toPresheaf_overlap_of_localEq r hfg)).trans hr)

end LocalSheafFraction

/-- The lifts of a given section form a compatible analytic family. -/
def liftedFamily {U : Opens ComplexTopCat} (s : X.meromorphicSheaf.presheaf.obj (op U)) :
    NormalGluing.LocalFamily U where
  domain x := (fractionLift s x).domain
  domain_le x := (fractionLift s x).inclusion
  mem_domain x := (fractionLift s x).point_mem
  representative x := (fractionLift s x).ratio
  meromorphic x := (fractionLift s x).ratio_meromorphic
  compatible x y _z hzx hzy :=
    LocalSheafFraction.eventuallyEq_of_toSheaf_overlap_eq
      ((fractionLift s x).certificate (fractionLift s x).point_mem)
      ((fractionLift s y).certificate (fractionLift s y).point_mem) hzx hzy
        ((fractionLift s x).certificates_overlap (fractionLift s y))

/-- A canonical normal representative, chosen from locally lifted fractions. -/
def sheafRepresentative {U : Opens ComplexTopCat}
    (s : X.meromorphicSheaf.presheaf.obj (op U)) : ℂ → ℂ := (liftedFamily s).glue

theorem sheafRepresentative_normal {U : Opens ComplexTopCat}
    (s : X.meromorphicSheaf.presheaf.obj (op U)) :
    MeromorphicNFOn (sheafRepresentative s) U := (liftedFamily s).glue_meromorphicNFOn

theorem sheafRepresentative_meromorphic {U : Opens ComplexTopCat}
    (s : X.meromorphicSheaf.presheaf.obj (op U)) :
    MeromorphicOn (sheafRepresentative s) U := (sheafRepresentative_normal s).meromorphicOn

lemma sheafRepresentative_eventuallyEq_ratio {U : Opens ComplexTopCat}
    (s : X.meromorphicSheaf.presheaf.obj (op U)) (x : U) {z : ℂ}
    (hz : z ∈ (fractionLift s x).domain) :
    sheafRepresentative s =ᶠ[𝓝[≠] z] (fractionLift s x).ratio := by
  have he : sheafRepresentative s =ᶠ[𝓝 z] (liftedFamily s).normalized x := by
    filter_upwards [(fractionLift s x).domain.isOpen.mem_nhds hz] with w hw
    exact (liftedFamily s).glue_eqOn x hw
  exact (he.filter_mono nhdsWithin_le_nhds).trans
    ((fractionLift s x).ratio_meromorphic.toMeromorphicNFOn_eq_self_on_nhdsNE hz)

/-- Sheafifying the reconstructed normal representative recovers the given section. -/
theorem sectionOn_sheafRepresentative {U : Opens ComplexTopCat}
    (s : X.meromorphicSheaf.presheaf.obj (op U)) :
    sectionOn (sheafRepresentative_meromorphic s) = s := by
  apply TopCat.Presheaf.IsSheaf.section_ext X.meromorphicSheaf.property
  intro z hz
  let x : U := ⟨z, hz⟩
  let q := localSheafFractionOn (sheafRepresentative_meromorphic s) x
  let r := fractionLift s x
  let t := r.certificate r.point_mem
  let V := q.domain ⊓ r.domain
  refine ⟨V, inf_le_left.trans (show q.domain ≤ U from inf_le_right),
    ⟨q.point_mem, r.point_mem⟩, ?_⟩
  have hq := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op k)
      (sectionOn_restrict (sheafRepresentative_meromorphic s) x)
  have hr := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (infLERight q.domain r.domain).op k)
      (r.certificate_represents r.point_mem)
  have hqt : X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op q.toSheaf =
      X.meromorphicSheaf.presheaf.map (infLERight q.domain r.domain).op t.toSheaf :=
    q.toSheaf_overlap_of_localEq t fun w hw ↦ sheafRepresentative_eventuallyEq_ratio s x hw.2
  have hqcomp := TopCat.Presheaf.restrict_restrict
    (F := X.meromorphicSheaf.presheaf) (inf_le_left : V ≤ q.domain)
    (show q.domain ≤ U from inf_le_right) (sectionOn (sheafRepresentative_meromorphic s))
  have hrcomp := TopCat.Presheaf.restrict_restrict
    (F := X.meromorphicSheaf.presheaf) (inf_le_right : V ≤ r.domain) r.inclusion s
  exact hqcomp.symm.trans (hq.trans (hqt.trans (hr.trans hrcomp)))

theorem exists_meromorphic_representative {U : Opens ComplexTopCat}
    (s : X.meromorphicSheaf.presheaf.obj (op U)) :
    ∃ f : ℂ → ℂ, ∃ hf : MeromorphicOn f U, sectionOn hf = s :=
  ⟨sheafRepresentative s, sheafRepresentative_meromorphic s, sectionOn_sheafRepresentative s⟩

#print axioms liftedFamily
#print axioms sectionOn_sheafRepresentative
#print axioms exists_meromorphic_representative

end

end MMeromorphicTest.SheafLocalBridge
