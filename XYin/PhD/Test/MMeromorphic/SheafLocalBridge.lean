import XYin.PhD.Test.MMeromorphic.Reference.ComplexPlane
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Direct meromorphy supplies local sections of the reference meromorphic sheaf

The input is the independently defined `MeromorphicAt` predicate. We construct a local fraction
of holomorphic sections, prove that its denominator is regular at every stalk, and then apply
the localization and sheafification maps from the cited reference construction.

This is a local comparison. Global gluing and an isomorphism with codiscrete equivalence classes
are separate assertions and are not assumed here.
-/

open CategoryTheory Opposite AlgebraicGeometry Filter Set TopologicalSpace
open scoped Topology nonZeroDivisors

namespace MMeromorphicTest.SheafLocalBridge

open MeromorphicFunction

noncomputable section

abbrev X := holomorphicLocallyRingedSpace

abbrev HolomorphicSection (U : Opens ComplexTopCat) := X.presheaf.obj (op U)

/-- Restrict a function analytic near every point of an open to a holomorphic section. -/
def analyticSection (U : Opens ComplexTopCat) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    HolomorphicSection U := by
  refine ⟨fun z ↦ f z, ?_⟩
  intro z
  refine ⟨U, U.isOpen, z.property, subset_rfl, f, ?_, hf z z.property⟩
  intro y hy
  rfl

@[simp]
lemma analyticSection_apply (U : Opens ComplexTopCat) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (z : U) : (analyticSection U f hf).val z = f z := rfl

/-- Restriction to an open does not change the germ of the original analytic function. -/
lemma ringSectionFun_analyticSection_eventuallyEq (U : Opens ComplexTopCat) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) {z : ℂ} (hz : z ∈ U) :
    ringSectionFun (analyticSection U f hf) =ᶠ[𝓝 z] f := by
  filter_upwards [U.isOpen.mem_nhds hz] with w hw
  simp [ringSectionFun_apply _ hw]

/-- An entire nonzero function has a nonzero holomorphic germ at every point. -/
lemma analyticSection_germ_ne_zero_of_entire (U : Opens ComplexTopCat) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : ∃ z, f z ≠ 0) (y : U) :
    X.presheaf.germ U (y : ℂ) y.property (analyticSection U f (hf.mono (subset_univ _))) ≠ 0 := by
  intro hzero
  have he := (germ_eq_zero_iff_eventuallyEq_zero y y.property
    (analyticSection U f (hf.mono (subset_univ _)))).mp hzero
  have hfzero : f =ᶠ[𝓝 (y : ℂ)] 0 :=
    (ringSectionFun_analyticSection_eventuallyEq U f (hf.mono (subset_univ _))
      y.property).symm.trans he
  have hglobal := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ (y : ℂ)) hfzero
  obtain ⟨z, hz⟩ := hne
  exact hz (hglobal (mem_univ z))

/-- The same nonzero entire function is a stalkwise regular denominator on every open. -/
lemma analyticSection_regular_of_entire (U : Opens ComplexTopCat) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : ∃ z, f z ≠ 0) :
    analyticSection U f (hf.mono (subset_univ _)) ∈
      X.meromorphicSubmonoidPresheaf.obj (op U) := by
  simp only [LocallyRingedSpace.meromorphicSubmonoidPresheaf,
    TopCat.Presheaf.submonoidPresheafOfStalk_obj, Submonoid.mem_iInf, Submonoid.mem_comap]
  intro y
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    (analyticSection_germ_ne_zero_of_entire U hf hne y)

/-- A local fraction of holomorphic sections whose denominator is stalkwise regular. -/
structure LocalSheafFraction (f : ℂ → ℂ) (x : ℂ) where
  domain : Opens ComplexTopCat
  point_mem : x ∈ domain
  numerator : HolomorphicSection domain
  denominator : HolomorphicSection domain
  denominator_regular : denominator ∈ X.meromorphicSubmonoidPresheaf.obj (op domain)
  eq_away_center : ∀ y : domain, (y : ℂ) ≠ x →
    f y = numerator.val y / denominator.val y

/-- Raw meromorphy gives a local sheaf fraction without assuming membership in any field. -/
theorem exists_localSheafFraction {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) :
    Nonempty (LocalSheafFraction f x) := by
  obtain ⟨n, ha⟩ := hf
  let a : ℂ → ℂ := fun z ↦ (z - x) ^ n • f z
  let b : ℂ → ℂ := fun z ↦ (z - x) ^ n
  obtain ⟨U, haU, hU, hxU⟩ := eventually_nhds_iff.mp ha.eventually_analyticAt
  let V : Opens ComplexTopCat := ⟨U, hU⟩
  have haV : AnalyticOnNhd ℂ a V := haU
  have hb : AnalyticOnNhd ℂ b univ :=
    fun z _ ↦ (analyticAt_id.fun_sub analyticAt_const).fun_pow n
  let sa := analyticSection V a haV
  let sb := analyticSection V b (hb.mono (subset_univ _))
  have hregular : sb ∈ X.meromorphicSubmonoidPresheaf.obj (op V) :=
    analyticSection_regular_of_entire V hb ⟨x + 1, by simp [b]⟩
  refine ⟨⟨V, hxU, sa, sb, hregular, ?_⟩⟩
  intro y hy
  change f y = ((y - x) ^ n * f y) / (y - x) ^ n
  exact (mul_div_cancel_left₀ (f y) (pow_ne_zero n (sub_ne_zero.mpr hy))).symm

namespace LocalSheafFraction

variable {f : ℂ → ℂ} {x : ℂ}

/-- Conversely, a certified local sheaf fraction has the original one-variable meromorphy. -/
theorem meromorphicAt (q : LocalSheafFraction f x) : MeromorphicAt f x := by
  have ha := analyticOnNhd_ringSectionFun q.numerator x q.point_mem
  have hb := analyticOnNhd_ringSectionFun q.denominator x q.point_mem
  apply (ha.meromorphicAt.div hb.meromorphicAt).congr
  filter_upwards [nhdsWithin_le_nhds (q.domain.isOpen.mem_nhds q.point_mem),
    self_mem_nhdsWithin] with z hzU hz
  have hzx : z ≠ x := by simpa using hz
  simpa [ringSectionFun_apply _ hzU] using (q.eq_away_center ⟨z, hzU⟩ hzx).symm

/-- First send the local fraction to the presheaf localization at regular denominators. -/
def toPresheaf (q : LocalSheafFraction f x) : X.meromorphicPresheaf.obj (op q.domain) := by
  change Localization (X.meromorphicSubmonoidPresheaf.obj (op q.domain))
  exact Localization.mk q.numerator ⟨q.denominator, q.denominator_regular⟩

/-- Sheafify the local fraction, obtaining a meromorphic section over its open neighborhood. -/
def toSheaf (q : LocalSheafFraction f x) : X.meromorphicSheaf.presheaf.obj (op q.domain) :=
  ((CategoryTheory.toSheafify (Opens.grothendieckTopology X.toTopCat)
    X.meromorphicPresheaf).app (op q.domain)) (q.toPresheaf)

end LocalSheafFraction

theorem meromorphicAt_iff_localSheafFraction {f : ℂ → ℂ} {x : ℂ} :
    MeromorphicAt f x ↔ Nonempty (LocalSheafFraction f x) :=
  ⟨exists_localSheafFraction, fun ⟨q⟩ ↦ q.meromorphicAt⟩

/-- A proof of the direct predicate concretely produces a local meromorphic sheaf section. -/
def localSheafFraction {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) :
    LocalSheafFraction f x := Classical.choice (exists_localSheafFraction hf)

example {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) :
    X.meromorphicSheaf.presheaf.obj (op (localSheafFraction hf).domain) :=
  (localSheafFraction hf).toSheaf

/-- An explicit fraction with a zero point value but a regular denominator germ. -/
def coordinatePoleFraction (x : ℂ) : LocalSheafFraction (fun z ↦ (z - x)⁻¹) x := by
  have hb : AnalyticOnNhd ℂ (fun z ↦ z - x) univ :=
    fun z _ ↦ analyticAt_id.fun_sub analyticAt_const
  let b := analyticSection ⊤ (fun z ↦ z - x) hb
  have hregular : b ∈ X.meromorphicSubmonoidPresheaf.obj (op ⊤) :=
    analyticSection_regular_of_entire ⊤ hb ⟨x + 1, by simp⟩
  refine ⟨⊤, mem_univ x, analyticSection ⊤ (fun _ ↦ 1) (fun _ _ ↦ analyticAt_const),
    b, hregular, ?_⟩
  intro y hy
  simp [b, analyticSection]

example (x : ℂ) : (coordinatePoleFraction x).denominator.val ⟨x, mem_univ x⟩ = 0 := by
  simp [coordinatePoleFraction, analyticSection]

example (x : ℂ) :
    X.meromorphicSheaf.presheaf.obj (op (coordinatePoleFraction x).domain) :=
  (coordinatePoleFraction x).toSheaf

#print axioms exists_localSheafFraction
#print axioms LocalSheafFraction.toSheaf
#print axioms meromorphicAt_iff_localSheafFraction

end

end MMeromorphicTest.SheafLocalBridge
