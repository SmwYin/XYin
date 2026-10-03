import XYin.PhD.Test.MMeromorphic.SheafOpenBridge

/-!
# Arithmetic in the forward meromorphic sheaf construction

Local addition uses a smaller neighborhood on which both denominators vanish only possibly
at the shared center. Products need no such restriction. The localization formulas then
identify these certificates with addition and multiplication of meromorphic sheaf sections.
-/

open CategoryTheory Opposite AlgebraicGeometry Filter Set TopologicalSpace
open TopologicalSpace.Opens
open scoped Topology nonZeroDivisors

namespace MMeromorphicTest.SheafLocalBridge

open MeromorphicFunction

noncomputable section

namespace LocalSheafFraction

variable {f g : ℂ → ℂ} {x : ℂ}

/-- Around a common center, shrink two fraction domains so their denominators are nonzero
away from that center. This is needed for pointwise addition of raw fractions. -/
lemma exists_good_domain (q : LocalSheafFraction f x) (r : LocalSheafFraction g x) :
    ∃ V : Opens ComplexTopCat, x ∈ V ∧ V ≤ q.domain ∧ V ≤ r.domain ∧
      ∀ y ∈ V, y ≠ x → ringSectionFun q.denominator y ≠ 0 ∧
        ringSectionFun r.denominator y ≠ 0 := by
  have hb := eventually_nhdsWithin_iff.mp
    (q.denominator_eventually_ne_zero q.point_mem)
  have hd := eventually_nhdsWithin_iff.mp
    (r.denominator_eventually_ne_zero r.point_mem)
  have hgood : ∀ᶠ y in 𝓝 x, y ∈ q.domain ∧ y ∈ r.domain ∧
      (y ≠ x → ringSectionFun q.denominator y ≠ 0 ∧
        ringSectionFun r.denominator y ≠ 0) := by
    filter_upwards [hb, hd, q.domain.isOpen.mem_nhds q.point_mem,
      r.domain.isOpen.mem_nhds r.point_mem] with y hby hdy hyq hyr
    exact ⟨hyq, hyr, fun hy ↦ ⟨hby hy, hdy hy⟩⟩
  obtain ⟨V, hVgood, hVopen, hxV⟩ := eventually_nhds_iff.mp hgood
  exact ⟨⟨V, hVopen⟩, hxV, fun y hy ↦ (hVgood y hy).1,
    fun y hy ↦ (hVgood y hy).2.1, fun y hy ↦ (hVgood y hy).2.2⟩

/-- Add two certified fractions after shrinking their domains to avoid extra denominator
zeros away from the shared center. -/
def addOn (q : LocalSheafFraction f x) (r : LocalSheafFraction g x)
    (V : Opens ComplexTopCat) (hVq : V ≤ q.domain) (hVr : V ≤ r.domain) (hxV : x ∈ V)
    (hgood : ∀ y ∈ V, y ≠ x → ringSectionFun q.denominator y ≠ 0 ∧
      ringSectionFun r.denominator y ≠ 0) : LocalSheafFraction (f + g) x := by
  let i : V ⟶ q.domain := homOfLE hVq
  let j : V ⟶ r.domain := homOfLE hVr
  let a := X.presheaf.map i.op q.numerator
  let b := X.presheaf.map i.op q.denominator
  let c := X.presheaf.map j.op r.numerator
  let d := X.presheaf.map j.op r.denominator
  refine ⟨V, hxV, b * c + d * a, b * d,
    Submonoid.mul_mem _ (X.meromorphicSubmonoidPresheaf.map i.op q.denominator_regular)
      (X.meromorphicSubmonoidPresheaf.map j.op r.denominator_regular), ?_⟩
  intro y hy
  change f y + g y =
    (q.denominator.val ⟨y, hVq y.property⟩ * r.numerator.val ⟨y, hVr y.property⟩ +
      r.denominator.val ⟨y, hVr y.property⟩ * q.numerator.val ⟨y, hVq y.property⟩) /
      (q.denominator.val ⟨y, hVq y.property⟩ * r.denominator.val ⟨y, hVr y.property⟩)
  rw [q.eq_away_center ⟨y, hVq y.property⟩ hy,
    r.eq_away_center ⟨y, hVr y.property⟩ hy]
  have hb : q.denominator.val ⟨y, hVq y.property⟩ ≠ 0 := by
    simpa only [ringSectionFun_apply _ (hVq y.property)] using (hgood y y.property hy).1
  have hd : r.denominator.val ⟨y, hVr y.property⟩ ≠ 0 := by
    simpa only [ringSectionFun_apply _ (hVr y.property)] using (hgood y y.property hy).2
  field_simp
  ring

/-- Multiply local fractions on any common open containing their center. -/
def mulOn (q : LocalSheafFraction f x) (r : LocalSheafFraction g x)
    (V : Opens ComplexTopCat) (hVq : V ≤ q.domain) (hVr : V ≤ r.domain) (hxV : x ∈ V) :
    LocalSheafFraction (f * g) x := by
  let i : V ⟶ q.domain := homOfLE hVq
  let j : V ⟶ r.domain := homOfLE hVr
  refine ⟨V, hxV, X.presheaf.map i.op q.numerator * X.presheaf.map j.op r.numerator,
    X.presheaf.map i.op q.denominator * X.presheaf.map j.op r.denominator,
    Submonoid.mul_mem _ (X.meromorphicSubmonoidPresheaf.map i.op q.denominator_regular)
      (X.meromorphicSubmonoidPresheaf.map j.op r.denominator_regular), ?_⟩
  intro y hy
  change f y * g y =
    (q.numerator.val ⟨y, hVq y.property⟩ * r.numerator.val ⟨y, hVr y.property⟩) /
      (q.denominator.val ⟨y, hVq y.property⟩ * r.denominator.val ⟨y, hVr y.property⟩)
  rw [q.eq_away_center ⟨y, hVq y.property⟩ hy,
    r.eq_away_center ⟨y, hVr y.property⟩ hy, div_mul_div_comm]

set_option backward.isDefEq.respectTransparency false in
lemma toPresheaf_addOn (q : LocalSheafFraction f x) (r : LocalSheafFraction g x)
    (V : Opens ComplexTopCat) (hVq : V ≤ q.domain) (hVr : V ≤ r.domain) (hxV : x ∈ V)
    (hgood : ∀ y ∈ V, y ≠ x → ringSectionFun q.denominator y ≠ 0 ∧
      ringSectionFun r.denominator y ≠ 0) :
    (q.addOn r V hVq hVr hxV hgood).toPresheaf =
      X.meromorphicPresheaf.map (homOfLE hVq).op q.toPresheaf +
        X.meromorphicPresheaf.map (homOfLE hVr).op r.toPresheaf := by
  rw [map_toPresheaf, map_toPresheaf, Localization.add_mk]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma toPresheaf_mulOn (q : LocalSheafFraction f x) (r : LocalSheafFraction g x)
    (V : Opens ComplexTopCat) (hVq : V ≤ q.domain) (hVr : V ≤ r.domain) (hxV : x ∈ V) :
    (q.mulOn r V hVq hVr hxV).toPresheaf =
      X.meromorphicPresheaf.map (homOfLE hVq).op q.toPresheaf *
        X.meromorphicPresheaf.map (homOfLE hVr).op r.toPresheaf := by
  rw [map_toPresheaf, map_toPresheaf]
  dsimp only [mulOn, toPresheaf]
  change Localization.mk _ _ = _
  simp only [Localization.mk_eq_mk']
  exact IsLocalization.mk'_mul
    (S := Localization (X.meromorphicSubmonoidPresheaf.obj (op V)))
    (X.presheaf.map (homOfLE hVq).op q.numerator)
    (X.presheaf.map (homOfLE hVr).op r.numerator)
    ⟨X.presheaf.map (homOfLE hVq).op q.denominator,
      X.meromorphicSubmonoidPresheaf.map (homOfLE hVq).op q.denominator_regular⟩
    ⟨X.presheaf.map (homOfLE hVr).op r.denominator,
      X.meromorphicSubmonoidPresheaf.map (homOfLE hVr).op r.denominator_regular⟩

lemma toSheaf_addOn (q : LocalSheafFraction f x) (r : LocalSheafFraction g x)
    (V : Opens ComplexTopCat) (hVq : V ≤ q.domain) (hVr : V ≤ r.domain) (hxV : x ∈ V)
    (hgood : ∀ y ∈ V, y ≠ x → ringSectionFun q.denominator y ≠ 0 ∧
      ringSectionFun r.denominator y ≠ 0) :
    (q.addOn r V hVq hVr hxV hgood).toSheaf =
      X.meromorphicSheaf.presheaf.map (homOfLE hVq).op q.toSheaf +
        X.meromorphicSheaf.presheaf.map (homOfLE hVr).op r.toSheaf := by
  let α := CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
    X.meromorphicPresheaf
  have hq := congrArg (fun k ↦ k q.toPresheaf) (α.naturality (homOfLE hVq).op)
  have hr := congrArg (fun k ↦ k r.toPresheaf) (α.naturality (homOfLE hVr).op)
  simp only [ConcreteCategory.comp_apply] at hq hr
  change (α.app (op V)) _ = _
  rw [toPresheaf_addOn]
  exact ((α.app (op V)).hom.map_add _ _).trans (congrArg₂ (· + ·) hq hr)

lemma toSheaf_mulOn (q : LocalSheafFraction f x) (r : LocalSheafFraction g x)
    (V : Opens ComplexTopCat) (hVq : V ≤ q.domain) (hVr : V ≤ r.domain) (hxV : x ∈ V) :
    (q.mulOn r V hVq hVr hxV).toSheaf =
      X.meromorphicSheaf.presheaf.map (homOfLE hVq).op q.toSheaf *
        X.meromorphicSheaf.presheaf.map (homOfLE hVr).op r.toSheaf := by
  let α := CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
    X.meromorphicPresheaf
  have hq := congrArg (fun k ↦ k q.toPresheaf) (α.naturality (homOfLE hVq).op)
  have hr := congrArg (fun k ↦ k r.toPresheaf) (α.naturality (homOfLE hVr).op)
  simp only [ConcreteCategory.comp_apply] at hq hr
  change (α.app (op V)) _ = _
  rw [toPresheaf_mulOn]
  exact ((α.app (op V)).hom.map_mul _ _).trans (congrArg₂ (· * ·) hq hr)

/-- The constant one is represented by the fraction `1/1` on the whole plane. -/
def oneFraction (x : ℂ) : LocalSheafFraction (fun _ ↦ 1) x := by
  refine ⟨⊤, mem_top x, 1, 1, Submonoid.one_mem _, ?_⟩
  intro y hy
  change (1 : ℂ) = 1 / 1
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma oneFraction_toSheaf (x : ℂ) : (oneFraction x).toSheaf = 1 := by
  change (CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
    X.meromorphicPresheaf).app (op ⊤) (Localization.mk 1 1) = 1
  have hmk : (Localization.mk (1 : HolomorphicSection ⊤)
      (1 : X.meromorphicSubmonoidPresheaf.obj (op ⊤)) :
      Localization (X.meromorphicSubmonoidPresheaf.obj (op ⊤))) = 1 := by
    rw [Localization.mk_one_eq_algebraMap, map_one]
  rw [hmk]
  exact ((CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
    X.meromorphicPresheaf).app (op ⊤)).hom.map_one

end LocalSheafFraction

/-- The global section restricts to any certified fraction for the same raw function,
independently of the choice used to construct its local gluing. -/
lemma globalSection_restrict_fraction {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    {x : ℂ} (q : LocalSheafFraction f x) :
    X.meromorphicSheaf.presheaf.map (homOfLE (le_top : q.domain ≤ ⊤)).op
      (globalSection hf) = q.toSheaf := by
  apply TopCat.Presheaf.IsSheaf.section_ext X.meromorphicSheaf.property
  intro z hz
  let r := localSheafFraction (hf z (mem_univ z))
  refine ⟨q.domain ⊓ r.domain, inf_le_left, ⟨hz, r.point_mem⟩, ?_⟩
  have hr := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (infLERight q.domain r.domain).op k)
      (globalSection_restrict hf z)
  change X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op
    (X.meromorphicSheaf.presheaf.map (homOfLE le_top).op (globalSection hf)) =
      X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op q.toSheaf
  have hqcomp := TopCat.Presheaf.restrict_restrict
    (F := X.meromorphicSheaf.presheaf) (inf_le_left : q.domain ⊓ r.domain ≤ q.domain)
    le_top (globalSection hf)
  have hrcomp := TopCat.Presheaf.restrict_restrict
    (F := X.meromorphicSheaf.presheaf) (inf_le_right : q.domain ⊓ r.domain ≤ r.domain)
    le_top (globalSection hf)
  exact hqcomp.trans (hrcomp.symm.trans (hr.trans (q.toSheaf_overlap r).symm))

/-- Addition of direct meromorphic functions agrees with sheaf-section addition. -/
theorem globalSection_add {f g : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ) :
    globalSection (hf.add hg) = globalSection hf + globalSection hg := by
  apply TopCat.Presheaf.IsSheaf.section_ext X.meromorphicSheaf.property
  intro x hx
  let q := localSheafFraction (hf x (mem_univ x))
  let r := localSheafFraction (hg x (mem_univ x))
  obtain ⟨V, hxV, hVq, hVr, hgood⟩ := q.exists_good_domain r
  refine ⟨V, le_top, hxV, ?_⟩
  let t := q.addOn r V hVq hVr hxV hgood
  have ht := globalSection_restrict_fraction (hf.add hg) t
  have hq := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (homOfLE hVq).op k)
      (globalSection_restrict_fraction hf q)
  have hr := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (homOfLE hVr).op k)
      (globalSection_restrict_fraction hg r)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hq hr
  change X.meromorphicSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    (globalSection (hf.add hg)) = X.meromorphicSheaf.presheaf.map (homOfLE le_top).op
      (globalSection hf + globalSection hg)
  change X.meromorphicSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    (globalSection (hf.add hg)) = t.toSheaf at ht
  change X.meromorphicSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    (globalSection hf) = _ at hq
  change X.meromorphicSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    (globalSection hg) = _ at hr
  rw [map_add]
  exact ht.trans ((q.toSheaf_addOn r V hVq hVr hxV hgood).trans
    (congrArg₂ (· + ·) hq.symm hr.symm))

/-- Multiplication of direct meromorphic functions agrees with sheaf-section multiplication. -/
theorem globalSection_mul {f g : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ) :
    globalSection (hf.mul hg) = globalSection hf * globalSection hg := by
  apply TopCat.Presheaf.IsSheaf.section_ext X.meromorphicSheaf.property
  intro x hx
  let q := localSheafFraction (hf x (mem_univ x))
  let r := localSheafFraction (hg x (mem_univ x))
  let V := q.domain ⊓ r.domain
  let t := q.mulOn r V inf_le_left inf_le_right ⟨q.point_mem, r.point_mem⟩
  refine ⟨V, le_top, ⟨q.point_mem, r.point_mem⟩, ?_⟩
  have ht := globalSection_restrict_fraction (hf.mul hg) t
  have hq := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op k)
      (globalSection_restrict_fraction hf q)
  have hr := congrArg (fun k ↦
    X.meromorphicSheaf.presheaf.map (infLERight q.domain r.domain).op k)
      (globalSection_restrict_fraction hg r)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hq hr
  change X.meromorphicSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    (globalSection (hf.mul hg)) = X.meromorphicSheaf.presheaf.map (homOfLE le_top).op
      (globalSection hf * globalSection hg)
  change X.meromorphicSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    (globalSection (hf.mul hg)) = t.toSheaf at ht
  change X.meromorphicSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    (globalSection hf) = _ at hq
  change X.meromorphicSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    (globalSection hg) = _ at hr
  rw [map_mul]
  exact ht.trans ((q.toSheaf_mulOn r V inf_le_left inf_le_right
    ⟨q.point_mem, r.point_mem⟩).trans (congrArg₂ (· * ·) hq.symm hr.symm))

@[simp] theorem globalSection_one : globalSection (MeromorphicOn.const (1 : ℂ)) = 1 := by
  have h := globalSection_restrict_fraction (MeromorphicOn.const (1 : ℂ))
    (LocalSheafFraction.oneFraction 0)
  change X.meromorphicSheaf.presheaf.map (𝟙 (op ⊤)) (globalSection _) =
    (LocalSheafFraction.oneFraction 0).toSheaf at h
  rw [CategoryTheory.Functor.map_id] at h
  simpa only [
    ConcreteCategory.id_apply, LocalSheafFraction.oneFraction_toSheaf] using h

#print axioms globalSection_add
#print axioms globalSection_mul
#print axioms globalSection_one

end

end MMeromorphicTest.SheafLocalBridge
