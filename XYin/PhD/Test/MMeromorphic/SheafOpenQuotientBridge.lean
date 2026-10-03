import XYin.PhD.Test.MMeromorphic.SheafArithmeticBridge
import XYin.PhD.Test.MMeromorphic.SheafOpenField
import XYin.PhD.Test.MMeromorphic.Field

/-!
# Codiscrete meromorphic classes map to sheaf sections on arbitrary opens

This extends the already tested local-fraction construction and its arithmetic from the
whole plane to every open complex domain. The predicate is proved before the section is
constructed. Connectedness is only needed for the final field injectivity theorem.
Surjectivity is deliberately a separate comparison theorem.
-/

open CategoryTheory Opposite AlgebraicGeometry Filter Set TopologicalSpace
open TopologicalSpace.Opens
open scoped Topology nonZeroDivisors

namespace MMeromorphicTest.SheafLocalBridge

open MeromorphicFunction

noncomputable section

/-- The glued section agrees with any certified fraction on a domain contained in `U`. -/
lemma sectionOn_restrict_fraction {f : ℂ → ℂ} {U : Opens ComplexTopCat}
    (hf : MeromorphicOn f U) {x : ℂ} (q : LocalSheafFraction f x) (hqU : q.domain ≤ U) :
    X.meromorphicSheaf.presheaf.map (homOfLE hqU).op (sectionOn hf) = q.toSheaf := by
  apply TopCat.Presheaf.IsSheaf.section_ext X.meromorphicSheaf.property
  intro z hz
  let r := localSheafFractionOn hf ⟨z, hqU hz⟩
  have hrU : r.domain ≤ U := inf_le_right
  refine ⟨q.domain ⊓ r.domain, inf_le_left, ⟨hz, r.point_mem⟩, ?_⟩
  have hr := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (infLERight q.domain r.domain).op k)
      (sectionOn_restrict hf ⟨z, hqU hz⟩)
  change X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op
    (X.meromorphicSheaf.presheaf.map (homOfLE hqU).op (sectionOn hf)) =
      X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op q.toSheaf
  have hqcomp := TopCat.Presheaf.restrict_restrict
    (F := X.meromorphicSheaf.presheaf) (inf_le_left : q.domain ⊓ r.domain ≤ q.domain)
    hqU (sectionOn hf)
  have hrcomp := TopCat.Presheaf.restrict_restrict
    (F := X.meromorphicSheaf.presheaf) (inf_le_right : q.domain ⊓ r.domain ≤ r.domain)
    hrU (sectionOn hf)
  exact hqcomp.trans (hrcomp.symm.trans (hr.trans (q.toSheaf_overlap r).symm))

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise addition agrees with addition of the associated sheaf sections over `U`. -/
theorem sectionOn_add {f g : ℂ → ℂ} {U : Opens ComplexTopCat}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) :
    sectionOn (hf.add hg) = sectionOn hf + sectionOn hg := by
  apply TopCat.Presheaf.IsSheaf.section_ext X.meromorphicSheaf.property
  intro x hx
  let q := localSheafFractionOn hf ⟨x, hx⟩
  let r := localSheafFractionOn hg ⟨x, hx⟩
  have hqU : q.domain ≤ U := inf_le_right
  have hrU : r.domain ≤ U := inf_le_right
  obtain ⟨V, hxV, hVq, hVr, hgood⟩ := q.exists_good_domain r
  have hVU : V ≤ U := hVq.trans hqU
  refine ⟨V, hVU, hxV, ?_⟩
  let t := q.addOn r V hVq hVr hxV hgood
  have ht := sectionOn_restrict_fraction (hf.add hg) t hVU
  have hq := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (homOfLE hVq).op k)
      (sectionOn_restrict_fraction hf q hqU)
  have hr := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (homOfLE hVr).op k)
      (sectionOn_restrict_fraction hg r hrU)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hq hr
  change X.meromorphicSheaf.presheaf.map (homOfLE hVU).op
    (sectionOn (hf.add hg)) = X.meromorphicSheaf.presheaf.map (homOfLE hVU).op
      (sectionOn hf + sectionOn hg)
  change X.meromorphicSheaf.presheaf.map (homOfLE hVU).op
    (sectionOn (hf.add hg)) = t.toSheaf at ht
  change X.meromorphicSheaf.presheaf.map (homOfLE hVU).op (sectionOn hf) = _ at hq
  change X.meromorphicSheaf.presheaf.map (homOfLE hVU).op (sectionOn hg) = _ at hr
  rw [(X.meromorphicSheaf.presheaf.map (homOfLE hVU).op).hom.map_add]
  exact ht.trans ((q.toSheaf_addOn r V hVq hVr hxV hgood).trans
    (congrArg₂ (· + ·) hq.symm hr.symm))

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise multiplication agrees with multiplication of sheaf sections over `U`. -/
theorem sectionOn_mul {f g : ℂ → ℂ} {U : Opens ComplexTopCat}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) :
    sectionOn (hf.mul hg) = sectionOn hf * sectionOn hg := by
  apply TopCat.Presheaf.IsSheaf.section_ext X.meromorphicSheaf.property
  intro x hx
  let q := localSheafFractionOn hf ⟨x, hx⟩
  let r := localSheafFractionOn hg ⟨x, hx⟩
  have hqU : q.domain ≤ U := inf_le_right
  have hrU : r.domain ≤ U := inf_le_right
  let V := q.domain ⊓ r.domain
  have hVU : V ≤ U := inf_le_left.trans hqU
  let t := q.mulOn r V inf_le_left inf_le_right ⟨q.point_mem, r.point_mem⟩
  refine ⟨V, hVU, ⟨q.point_mem, r.point_mem⟩, ?_⟩
  have ht := sectionOn_restrict_fraction (hf.mul hg) t hVU
  have hq := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op k)
      (sectionOn_restrict_fraction hf q hqU)
  have hr := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (infLERight q.domain r.domain).op k)
      (sectionOn_restrict_fraction hg r hrU)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hq hr
  change X.meromorphicSheaf.presheaf.map (homOfLE hVU).op
    (sectionOn (hf.mul hg)) = X.meromorphicSheaf.presheaf.map (homOfLE hVU).op
      (sectionOn hf * sectionOn hg)
  change X.meromorphicSheaf.presheaf.map (homOfLE hVU).op
    (sectionOn (hf.mul hg)) = t.toSheaf at ht
  change X.meromorphicSheaf.presheaf.map (homOfLE hVU).op (sectionOn hf) = _ at hq
  change X.meromorphicSheaf.presheaf.map (homOfLE hVU).op (sectionOn hg) = _ at hr
  rw [(X.meromorphicSheaf.presheaf.map (homOfLE hVU).op).hom.map_mul]
  exact ht.trans ((q.toSheaf_mulOn r V inf_le_left inf_le_right
    ⟨q.point_mem, r.point_mem⟩).trans (congrArg₂ (· * ·) hq.symm hr.symm))

namespace LocalSheafFraction

/-- The fraction `1/1` directly on an arbitrary open domain. -/
def oneFractionOn (U : Opens ComplexTopCat) (x : U) :
    LocalSheafFraction (fun _ ↦ 1) x := by
  refine ⟨U, x.property, 1, 1, Submonoid.one_mem _, ?_⟩
  intro y hy
  change (1 : ℂ) = 1 / 1
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma oneFractionOn_toSheaf (U : Opens ComplexTopCat) (x : U) :
    (oneFractionOn U x).toSheaf = 1 := by
  change (CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
    X.meromorphicPresheaf).app (op U) (Localization.mk 1 1) = 1
  have hmk : (Localization.mk (1 : HolomorphicSection U)
      (1 : X.meromorphicSubmonoidPresheaf.obj (op U)) :
      Localization (X.meromorphicSubmonoidPresheaf.obj (op U))) = 1 := by
    rw [Localization.mk_one_eq_algebraMap, map_one]
  rw [hmk]
  exact ((CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
    X.meromorphicPresheaf).app (op U)).hom.map_one

set_option backward.isDefEq.respectTransparency false in
/-- Codiscretely equal representatives define equal localized fractions on every overlap
whose domains lie inside the meromorphicity domain. -/
lemma toPresheaf_overlap_of_codiscreteOn {f g : ℂ → ℂ} {U : Opens ComplexTopCat}
    {x y : ℂ} (q : LocalSheafFraction f x) (r : LocalSheafFraction g y)
    (hqU : q.domain ≤ U) (_hrU : r.domain ≤ U)
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hfg : f =ᶠ[codiscreteWithin (U : Set ℂ)] g) :
    X.meromorphicPresheaf.map (infLELeft q.domain r.domain).op q.toPresheaf =
      X.meromorphicPresheaf.map (infLERight q.domain r.domain).op r.toPresheaf := by
  rw [map_toPresheaf, map_toPresheaf]
  simp only [Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_of_eq'
    (S := Localization (X.meromorphicSubmonoidPresheaf.obj (op (q.domain ⊓ r.domain))))
  apply Subtype.ext
  funext z
  have hzU : (z : ℂ) ∈ U := hqU z.property.1
  exact r.cross_mul_eq_of_eventuallyEq q ⟨z, ⟨z.property.2, z.property.1⟩⟩
    ((hg z hzU).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (hf z hzU) hzU U.isOpen.preperfect hfg.symm)

lemma toSheaf_overlap_of_codiscreteOn {f g : ℂ → ℂ} {U : Opens ComplexTopCat}
    {x y : ℂ} (q : LocalSheafFraction f x) (r : LocalSheafFraction g y)
    (hqU : q.domain ≤ U) (hrU : r.domain ≤ U)
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hfg : f =ᶠ[codiscreteWithin (U : Set ℂ)] g) :
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
    (q.toPresheaf_overlap_of_codiscreteOn r hqU hrU hf hg hfg)).trans hr)

end LocalSheafFraction

@[simp] theorem sectionOn_one (U : Opens ComplexTopCat) :
    sectionOn (MeromorphicOn.const (U := (U : Set ℂ)) (1 : ℂ)) = 1 := by
  apply TopCat.Presheaf.IsSheaf.section_ext X.meromorphicSheaf.property
  intro x hx
  refine ⟨U, le_rfl, hx, ?_⟩
  rw [map_one]
  exact (sectionOn_restrict_fraction (MeromorphicOn.const (1 : ℂ))
    (LocalSheafFraction.oneFractionOn U ⟨x, hx⟩) le_rfl).trans
      (LocalSheafFraction.oneFractionOn_toSheaf U ⟨x, hx⟩)

/-- The associated section depends only on the codiscrete equivalence class in `U`. -/
theorem sectionOn_congr {f g : ℂ → ℂ} {U : Opens ComplexTopCat}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hfg : f =ᶠ[codiscreteWithin (U : Set ℂ)] g) : sectionOn hf = sectionOn hg := by
  apply TopCat.Presheaf.IsSheaf.section_ext X.meromorphicSheaf.property
  intro x hx
  let q := localSheafFractionOn hf ⟨x, hx⟩
  let r := localSheafFractionOn hg ⟨x, hx⟩
  have hqU : q.domain ≤ U := inf_le_right
  have hrU : r.domain ≤ U := inf_le_right
  refine ⟨q.domain ⊓ r.domain, inf_le_left.trans hqU, ⟨q.point_mem, r.point_mem⟩, ?_⟩
  have hq := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op k)
      (sectionOn_restrict hf ⟨x, hx⟩)
  have hr := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (infLERight q.domain r.domain).op k)
      (sectionOn_restrict hg ⟨x, hx⟩)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hq hr
  exact hq.trans ((q.toSheaf_overlap_of_codiscreteOn r hqU hrU hf hg hfg).trans hr.symm)

/-- Descend the direct meromorphic predicate to a sheaf section on `U`. -/
def ofGermOn (U : Opens ComplexTopCat) (a : MeromorphicGerms (U : Set ℂ)) :
    X.meromorphicSheaf.presheaf.obj (op U) := sectionOn a.property.choose_spec.1

@[simp] theorem ofGermOn_toGerm {U : Opens ComplexTopCat} {f : ℂ → ℂ}
    (hf : MeromorphicOn f U) : ofGermOn U (toGerm hf) = sectionOn hf := by
  apply sectionOn_congr
  exact Germ.coe_eq.mp (toGerm hf).property.choose_spec.2

@[simp] theorem ofGermOn_add (U : Opens ComplexTopCat)
    (a b : MeromorphicGerms (U : Set ℂ)) :
    ofGermOn U (a + b) = ofGermOn U a + ofGermOn U b := by
  obtain ⟨f, hf, hef⟩ := a.property
  obtain ⟨g, hg, heg⟩ := b.property
  have ha : toGerm hf = a := Subtype.ext hef
  have hb : toGerm hg = b := Subtype.ext heg
  rw [← ha, ← hb, ← toGerm_add, ofGermOn_toGerm, ofGermOn_toGerm, ofGermOn_toGerm]
  exact sectionOn_add hf hg

@[simp] theorem ofGermOn_mul (U : Opens ComplexTopCat)
    (a b : MeromorphicGerms (U : Set ℂ)) :
    ofGermOn U (a * b) = ofGermOn U a * ofGermOn U b := by
  obtain ⟨f, hf, hef⟩ := a.property
  obtain ⟨g, hg, heg⟩ := b.property
  have ha : toGerm hf = a := Subtype.ext hef
  have hb : toGerm hg = b := Subtype.ext heg
  rw [← ha, ← hb, ← toGerm_mul, ofGermOn_toGerm, ofGermOn_toGerm, ofGermOn_toGerm]
  exact sectionOn_mul hf hg

@[simp] theorem ofGermOn_one (U : Opens ComplexTopCat) : ofGermOn U 1 = 1 := by
  rw [← toGerm_one (𝕜 := ℂ) (U := (U : Set ℂ)), ofGermOn_toGerm, sectionOn_one]

@[simp] theorem ofGermOn_zero (U : Opens ComplexTopCat) : ofGermOn U 0 = 0 := by
  have h := ofGermOn_add U 0 0
  rw [zero_add] at h
  exact add_eq_left.mp h.symm

/-- A ring homomorphism from independently defined meromorphic classes to sheaf sections. -/
def toSheafRingHomOn (U : Opens ComplexTopCat) :
    MeromorphicGerms (U : Set ℂ) →+* X.meromorphicSheaf.presheaf.obj (op U) where
  toFun := ofGermOn U
  map_zero' := ofGermOn_zero U
  map_one' := ofGermOn_one U
  map_add' := ofGermOn_add U
  map_mul' := ofGermOn_mul U

@[simp] theorem toSheafRingHomOn_toGerm {U : Opens ComplexTopCat} {f : ℂ → ℂ}
    (hf : MeromorphicOn f U) : toSheafRingHomOn U (toGerm hf) = sectionOn hf :=
  ofGermOn_toGerm hf

/-- On a connected nonempty complex domain this ring map is automatically injective. -/
theorem toSheafRingHomOn_injective (U : Opens ComplexTopCat)
    (hU : _root_.IsConnected (U : Set ℂ)) : Function.Injective (toSheafRingHomOn U) := by
  letI : NeBot (codiscreteWithin (U : Set ℂ)) :=
    codiscreteWithin_neBot_of_open (U : Set ℂ) U.isOpen hU.nonempty
  letI := meromorphicGermField (U : Set ℂ) hU.isPreconnected
  letI : LocallyConnectedSpace X := by
    change LocallyConnectedSpace ℂ
    infer_instance
  letI := (MMeromorphicTest.SheafOpen.isField_meromorphicSections X U hU).toField
  exact (toSheafRingHomOn U).injective

example (U : Opens ComplexTopCat) (a b : MeromorphicGerms (U : Set ℂ)) :
    toSheafRingHomOn U (a * b + 1) = toSheafRingHomOn U a * toSheafRingHomOn U b + 1 := by
  simp

#print axioms sectionOn_add
#print axioms sectionOn_congr
#print axioms toSheafRingHomOn
#print axioms toSheafRingHomOn_injective

end

end MMeromorphicTest.SheafLocalBridge
