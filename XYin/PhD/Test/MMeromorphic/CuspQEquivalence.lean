import XYin.PhD.ModularFunctions.CuspGrowth
import XYin.PhD.ModularFunctions.Cusps

/-!
# Exact meromorphic q-germs and the existing cusp function

The independently tested existence of a meromorphic q-germ agrees with meromorphy of the
canonical cusp function. The exponential-growth corollary reuses the project's existing
analytic theorem and retains its explicit eventual-holomorphy hypothesis. No analytic
condition is defined by membership in a field.
-/

open Filter Function Set UpperHalfPlane
open scoped Topology Manifold

namespace MMeromorphicTest.CuspQ

/-- Imaginary infinity on the complex plane, uniformly in the real coordinate. -/
abbrev atImaginaryInfinity : Filter ℂ := comap Complex.im atTop

/-- An actual meromorphic q-germ reproduces all sufficiently high values of the raw function. -/
def HasMeromorphicQGerm (h : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ F : ℂ → ℂ, MeromorphicAt F 0 ∧
    f =ᶠ[atImaginaryInfinity] fun z ↦ F (Periodic.qParam h z)

/-- Existence of an exact q-germ forces the canonical cusp function to have that germ. -/
theorem HasMeromorphicQGerm.meromorphicAt_cuspFunction {h : ℝ} {f : ℂ → ℂ}
    (hh : 0 < h) (hf : HasMeromorphicQGerm h f) :
    MeromorphicAt (Periodic.cuspFunction h f) 0 := by
  obtain ⟨F, hF, heq⟩ := hf
  apply hF.congr
  filter_upwards [(Periodic.invQParam_tendsto hh).eventually heq,
    self_mem_nhdsWithin] with q hqeq (hq : q ≠ 0)
  rw [Periodic.cuspFunction_eq_of_nonzero _ _ hq]
  simpa only [Periodic.qParam_right_inv hh.ne' hq] using hqeq.symm

/-- Positive-period exact q-germs and meromorphy of the canonical cusp function are equivalent.
This comparison needs no normal-form or separate holomorphy assumption. -/
theorem hasMeromorphicQGerm_iff_meromorphicAt_cuspFunction {h : ℝ} {f : ℂ → ℂ}
    (hh : 0 < h) (hfper : Periodic f (h : ℂ)) :
    HasMeromorphicQGerm h f ↔ MeromorphicAt (Periodic.cuspFunction h f) 0 := by
  refine ⟨HasMeromorphicQGerm.meromorphicAt_cuspFunction hh, fun hf ↦ ?_⟩
  exact ⟨Periodic.cuspFunction h f, hf,
    Eventually.of_forall fun z ↦ (Periodic.eq_cuspFunction hh.ne' hfper z).symm⟩

/-- The same direct existence condition on upper-half-plane representatives. -/
def HasMeromorphicQGermOnH (h : ℝ) (f : ℍ → ℂ) : Prop :=
  ∃ F : ℂ → ℂ, MeromorphicAt F 0 ∧
    f =ᶠ[atImInfty] fun τ ↦ F (Periodic.qParam h τ)

/-- Passing between the upper half plane and its ambient extension preserves exact tail data. -/
theorem hasMeromorphicQGermOnH_iff {h : ℝ} {f : ℍ → ℂ} :
    HasMeromorphicQGermOnH h f ↔ HasMeromorphicQGerm h (f ∘ ofComplex) := by
  constructor
  · rintro ⟨F, hF, heq⟩
    refine ⟨F, hF, ?_⟩
    filter_upwards [tendsto_comap_im_ofComplex.eventually heq,
      preimage_mem_comap (Ioi_mem_atTop (0 : ℝ))] with z hz hzi
    simpa only [Function.comp_apply, ofComplex_apply_of_im_pos hzi] using hz
  · rintro ⟨F, hF, heq⟩
    refine ⟨F, hF, ?_⟩
    filter_upwards [tendsto_coe_atImInfty.eventually heq] with τ hτ
    simpa only [Function.comp_apply, ofComplex_apply] using hτ

/-- This is the upper-half-plane bridge to the independently defined canonical cusp function. -/
theorem hasMeromorphicQGermOnH_iff_meromorphicAt_cuspFunction {h : ℝ} {f : ℍ → ℂ}
    (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) (h : ℂ)) :
    HasMeromorphicQGermOnH h f ↔ MeromorphicAt (cuspFunction h f) 0 :=
  hasMeromorphicQGermOnH_iff.trans
    (hasMeromorphicQGerm_iff_meromorphicAt_cuspFunction hh hfper)

/-- Exponential growth is equivalent to the direct q-germ condition when the raw representative
is holomorphic sufficiently high in the upper half plane. The analytic theorem is reused. -/
theorem isOfExponentialGrowth_iff_hasMeromorphicQGermOnH {h : ℝ} {f : ℍ → ℂ}
    (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) (h : ℂ))
    (hfhol : ∀ᶠ τ in atImInfty, MDiffAt f τ) :
    IsOfExponentialGrowth f ↔ HasMeromorphicQGermOnH h f :=
  (isOfExponentialGrowth_iff_meromorphicAt_cuspFunction hh hfper hfhol).trans
    (hasMeromorphicQGermOnH_iff_meromorphicAt_cuspFunction hh hfper).symm

/-- A canonical normal representative needs no separate eventual-holomorphy hypothesis:
the existing normal-form growth theorem excludes poles on a sufficiently high tail. -/
theorem isOfExponentialGrowth_iff_hasMeromorphicQGermOnH_of_meromorphicNFOn
    {h : ℝ} {f : ℍ → ℂ} (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet)
    (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) (h : ℂ)) :
    IsOfExponentialGrowth f ↔ HasMeromorphicQGermOnH h f :=
  (isOfExponentialGrowth_iff_meromorphicAt_cuspFunction_of_meromorphicNFOn hf hh hfper).trans
    (hasMeromorphicQGermOnH_iff_meromorphicAt_cuspFunction hh hfper).symm

/-- A genuine cusp pole satisfies the direct condition. -/
example {h : ℝ} : HasMeromorphicQGermOnH h (fun τ ↦ (Periodic.qParam h τ)⁻¹) :=
  ⟨fun q ↦ q⁻¹, (MeromorphicAt.id 0).inv, Eventually.of_forall fun _ ↦ rfl⟩

example {h : ℝ} {f : ℍ → ℂ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) (h : ℂ))
    (hfhol : ∀ᶠ τ in atImInfty, MDiffAt f τ) (hfgrowth : IsOfExponentialGrowth f) :
    HasMeromorphicQGermOnH h f :=
  (isOfExponentialGrowth_iff_hasMeromorphicQGermOnH hh hfper hfhol).mp hfgrowth

example {h : ℝ} {f : ℍ → ℂ}
    (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet) (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) (h : ℂ)) (hfgrowth : IsOfExponentialGrowth f) :
    HasMeromorphicQGermOnH h f :=
  (isOfExponentialGrowth_iff_hasMeromorphicQGermOnH_of_meromorphicNFOn hf hh hfper).mp
    hfgrowth

#print axioms hasMeromorphicQGerm_iff_meromorphicAt_cuspFunction
#print axioms isOfExponentialGrowth_iff_hasMeromorphicQGermOnH
#print axioms isOfExponentialGrowth_iff_hasMeromorphicQGermOnH_of_meromorphicNFOn

end MMeromorphicTest.CuspQ
