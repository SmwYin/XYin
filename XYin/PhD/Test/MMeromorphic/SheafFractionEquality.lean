import XYin.PhD.Test.MMeromorphic.SheafReverseBridge
import Mathlib.CategoryTheory.Sites.LocallyInjective

/-!
# Equality of local sheaf fractions implies equality of raw meromorphic germs

The canonical sheafification map is locally injective. Equal sheafified local fractions
therefore become equal in a smaller localization. Stalkwise regularity makes the clearing
multiplier and denominators nonzero on sufficiently small punctured neighborhoods, giving
equality of the raw holomorphic ratios there.
-/

open CategoryTheory Opposite AlgebraicGeometry Filter Set TopologicalSpace
open TopologicalSpace.Opens
open scoped Topology nonZeroDivisors

namespace MMeromorphicTest.SheafLocalBridge

open MeromorphicFunction

noncomputable section

/-- Holomorphic numerator and stalkwise regular denominator give a certified local
fraction of their raw pointwise ratio at any point of the domain. -/
def sectionFraction {V : Opens ComplexTopCat} (a b : HolomorphicSection V)
    (hb : b ∈ X.meromorphicSubmonoidPresheaf.obj (op V)) {x : ℂ} (hx : x ∈ V) :
    LocalSheafFraction (fun z ↦ ringSectionFun a z / ringSectionFun b z) x := by
  refine ⟨V, hx, a, b, hb, ?_⟩
  intro y hy
  simp only [ringSectionFun_apply _ y.property]

/-- Equal images under sheafification become equal after restriction around any point. -/
theorem exists_restriction_eq_of_sheafify_eq {U : Opens ComplexTopCat}
    (t₁ t₂ : X.meromorphicPresheaf.obj (op U))
    (h : (CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
      X.meromorphicPresheaf).app (op U) t₁ =
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
          X.meromorphicPresheaf).app (op U) t₂) {z : ℂ} (hz : z ∈ U) :
    ∃ (V : Opens ComplexTopCat) (hVU : V ≤ U), z ∈ V ∧
      X.meromorphicPresheaf.map (homOfLE hVU).op t₁ =
        X.meromorphicPresheaf.map (homOfLE hVU).op t₂ := by
  let α := CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
    X.meromorphicPresheaf
  have hcover := CategoryTheory.Presheaf.equalizerSieve_mem
    (Opens.grothendieckTopology X.toTopCat) α t₁ t₂ h
  obtain ⟨V, i, heq, hzV⟩ := hcover z hz
  exact ⟨V, leOfHom i, hzV, heq⟩

set_option backward.isDefEq.respectTransparency false in
/-- Equality in a localization implies equality of the raw ratios on punctured
neighborhoods of every point, using stalkwise regularity. -/
lemma ratio_eventuallyEq_of_localization_eq {U : Opens ComplexTopCat}
    (a b c d : HolomorphicSection U)
    (hb : b ∈ X.meromorphicSubmonoidPresheaf.obj (op U))
    (hd : d ∈ X.meromorphicSubmonoidPresheaf.obj (op U))
    (heq : (Localization.mk a ⟨b, hb⟩ :
      Localization (X.meromorphicSubmonoidPresheaf.obj (op U))) =
        Localization.mk c ⟨d, hd⟩) {z : ℂ} (hz : z ∈ U) :
    (fun w ↦ ringSectionFun a w / ringSectionFun b w) =ᶠ[𝓝[≠] z]
      (fun w ↦ ringSectionFun c w / ringSectionFun d w) := by
  simp only [Localization.mk_eq_mk'] at heq
  obtain ⟨e, he⟩ := (IsLocalization.eq
    (S := Localization (X.meromorphicSubmonoidPresheaf.obj (op U)))).mp heq
  let q := sectionFraction a b hb hz
  let r := sectionFraction c d hd hz
  let m := sectionFraction (0 : HolomorphicSection U) e.val e.property hz
  filter_upwards [q.denominator_eventually_ne_zero hz,
    r.denominator_eventually_ne_zero hz, m.denominator_eventually_ne_zero hz,
    nhdsWithin_le_nhds (U.isOpen.mem_nhds hz)] with w hbw hdw hew hw
  have hb' : b.val ⟨w, hw⟩ ≠ 0 := by
    simpa only [q, sectionFraction, ringSectionFun_apply _ hw] using hbw
  have hd' : d.val ⟨w, hw⟩ ≠ 0 := by
    simpa only [r, sectionFraction, ringSectionFun_apply _ hw] using hdw
  have he' : e.val.val ⟨w, hw⟩ ≠ 0 := by
    simpa only [m, sectionFraction, ringSectionFun_apply _ hw] using hew
  have hv := congrArg (fun k : HolomorphicSection U ↦ k.val ⟨w, hw⟩) he
  change e.val.val ⟨w, hw⟩ * (d.val ⟨w, hw⟩ * a.val ⟨w, hw⟩) =
    e.val.val ⟨w, hw⟩ * (b.val ⟨w, hw⟩ * c.val ⟨w, hw⟩) at hv
  have hc := mul_left_cancel₀ he' hv
  simpa only [ringSectionFun_apply _ hw] using
    (div_eq_div_iff hb' hd').mpr (by simpa only [mul_comm] using hc)

namespace LocalSheafFraction

private lemma eventually_ne_center (z x : ℂ) : ∀ᶠ w in 𝓝[≠] z, w ≠ x := by
  by_cases hzx : z = x
  · subst x
    exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds (eventually_ne_nhds hzx)

set_option backward.isDefEq.respectTransparency false in
/-- Equal sheafified certified fractions describe the same meromorphic germ at every
point of their overlap, regardless of arbitrary raw values at their centers. -/
theorem eventuallyEq_of_toSheaf_overlap_eq {f g : ℂ → ℂ} {x y z : ℂ}
    (q : LocalSheafFraction f x) (r : LocalSheafFraction g y)
    (hzq : z ∈ q.domain) (hzr : z ∈ r.domain)
    (h : X.meromorphicSheaf.presheaf.map (infLELeft q.domain r.domain).op q.toSheaf =
      X.meromorphicSheaf.presheaf.map (infLERight q.domain r.domain).op r.toSheaf) :
    f =ᶠ[𝓝[≠] z] g := by
  let α := CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
    X.meromorphicPresheaf
  let t₁ := X.meromorphicPresheaf.map (infLELeft q.domain r.domain).op q.toPresheaf
  let t₂ := X.meromorphicPresheaf.map (infLERight q.domain r.domain).op r.toPresheaf
  have hq := congrArg (fun k ↦ k q.toPresheaf)
    (α.naturality (infLELeft q.domain r.domain).op)
  have hr := congrArg (fun k ↦ k r.toPresheaf)
    (α.naturality (infLERight q.domain r.domain).op)
  simp only [ConcreteCategory.comp_apply] at hq hr
  have heqα : α.app (op (q.domain ⊓ r.domain)) t₁ =
      α.app (op (q.domain ⊓ r.domain)) t₂ := hq.trans (h.trans hr.symm)
  obtain ⟨T, hTJ, hzT, heqT⟩ := exists_restriction_eq_of_sheafify_eq t₁ t₂ heqα ⟨hzq, hzr⟩
  have hTq : T ≤ q.domain := hTJ.trans inf_le_left
  have hTr : T ≤ r.domain := hTJ.trans inf_le_right
  have hqq := TopCat.Presheaf.restrict_restrict (F := X.meromorphicPresheaf)
    hTJ (inf_le_left : q.domain ⊓ r.domain ≤ q.domain) q.toPresheaf
  have hrr := TopCat.Presheaf.restrict_restrict (F := X.meromorphicPresheaf)
    hTJ (inf_le_right : q.domain ⊓ r.domain ≤ r.domain) r.toPresheaf
  have heq : X.meromorphicPresheaf.map (homOfLE hTq).op q.toPresheaf =
      X.meromorphicPresheaf.map (homOfLE hTr).op r.toPresheaf :=
    hqq.symm.trans (heqT.trans hrr)
  rw [map_toPresheaf, map_toPresheaf] at heq
  have hrat := ratio_eventuallyEq_of_localization_eq
    (X.presheaf.map (homOfLE hTq).op q.numerator)
    (X.presheaf.map (homOfLE hTq).op q.denominator)
    (X.presheaf.map (homOfLE hTr).op r.numerator)
    (X.presheaf.map (homOfLE hTr).op r.denominator)
    (X.meromorphicSubmonoidPresheaf.map (homOfLE hTq).op q.denominator_regular)
    (X.meromorphicSubmonoidPresheaf.map (homOfLE hTr).op r.denominator_regular)
    heq hzT
  filter_upwards [hrat, nhdsWithin_le_nhds (T.isOpen.mem_nhds hzT),
    eventually_ne_center z x, eventually_ne_center z y] with w hwrat hwT hwx hwy
  rw [q.eq_away_center ⟨w, hTq hwT⟩ hwx, r.eq_away_center ⟨w, hTr hwT⟩ hwy]
  simpa only [ringSectionFun_apply _ hwT] using hwrat

end LocalSheafFraction

#print axioms exists_restriction_eq_of_sheafify_eq
#print axioms ratio_eventuallyEq_of_localization_eq
#print axioms LocalSheafFraction.eventuallyEq_of_toSheaf_overlap_eq

end

end MMeromorphicTest.SheafLocalBridge
