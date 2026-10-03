import XYin.PhD.Test.MMeromorphic.Field
import XYin.PhD.Test.MMeromorphic.UpperHalfPlane

/-! Sanity checks for raw functions, normal forms, and the derived quotient field. -/

open Filter Topology Set UpperHalfPlane

namespace MMeromorphicTest.FieldChecks

noncomputable section

/-- The exceptional value permitted by `MeromorphicOn` really creates a nonzero spike. -/
def spike (z : ℂ) : ℂ := if z = 0 then 1 else 0

theorem spike_eventually_zero : spike =ᶠ[codiscreteWithin (univ : Set ℂ)] 0 := by
  filter_upwards [compl_singleton_mem_codiscreteWithin (s := univ) (0 : ℂ)] with z hz
  simp only [mem_compl_iff, mem_singleton_iff] at hz
  simp [spike, hz]

theorem spike_meromorphic : MeromorphicOn spike univ :=
  (MeromorphicOn.const (0 : ℂ)).congr_codiscreteWithin spike_eventually_zero.symm isOpen_univ

/-- Raw meromorphic functions have zero divisors under pointwise multiplication. -/
theorem raw_meromorphic_zero_divisors :
    ∃ f g : ℂ → ℂ, MeromorphicOn f univ ∧ MeromorphicOn g univ ∧
      f ≠ 0 ∧ g ≠ 0 ∧ f * g = 0 := by
  refine ⟨spike, 1 - spike, spike_meromorphic,
    (MeromorphicOn.const (1 : ℂ)).sub spike_meromorphic, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [spike] at this
  · intro h
    have := congrFun h 1
    simp [spike] at this
  · funext z
    by_cases hz : z = 0 <;> simp [spike, hz]

/-- The intended quotient discards the exceptional spike. -/
example : toGerm spike_meromorphic = 0 :=
  (toGerm_eq_zero_iff spike_meromorphic).mpr spike_eventually_zero

local instance : NeBot (codiscreteWithin (univ : Set ℂ)) :=
  codiscreteWithin_neBot_of_open univ isOpen_univ ⟨0, mem_univ 0⟩

local instance : Field (MeromorphicGerms (univ : Set ℂ)) :=
  meromorphicGermField univ isPreconnected_univ

example (f : MeromorphicGerms (univ : Set ℂ)) (hf : f ≠ 0) : f * f⁻¹ = 1 :=
  mul_inv_cancel₀ hf

example (f g : MeromorphicGerms (univ : Set ℂ)) (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 := mul_ne_zero hf hg

example {f : ℂ → ℂ} (hf : MeromorphicOn f univ) : toGerm hf.inv = (toGerm hf)⁻¹ :=
  toGerm_inv univ isPreconnected_univ hf

theorem spike_comp_constant_meromorphic :
    MeromorphicOn (spike ∘ fun _ : ℂ ↦ 0) univ := by
  simpa [spike, Function.comp_def] using
    (MeromorphicOn.const (𝕜 := ℂ) (U := univ) (1 : ℂ))

/-- Constant holomorphic pullback does not descend to the quotient by discrete exceptions. -/
theorem constant_pullback_does_not_preserve_zero_class :
    toGerm spike_meromorphic = 0 ∧ toGerm spike_comp_constant_meromorphic ≠ 0 := by
  refine ⟨(toGerm_eq_zero_iff spike_meromorphic).mpr spike_eventually_zero, ?_⟩
  have he : toGerm spike_comp_constant_meromorphic = 1 := by
    rw [← toGerm_one, toGerm_eq_iff]
    exact Eventually.of_forall fun z ↦ by simp [spike]
  rw [he]
  exact one_ne_zero

/-- First normal-form pole. -/
def poleA (z : ℂ) : ℂ := z⁻¹

/-- Second pole, chosen so that the two poles cancel to the constant one off zero. -/
def poleB (z : ℂ) : ℂ := z⁻¹ * (z - 1)

theorem poleA_nf : MeromorphicNFOn poleA univ := by
  intro z _
  exact (analyticAt_id (𝕜 := ℂ) (z := z)).meromorphicNFAt.inv

theorem poleB_nf : MeromorphicNFOn poleB univ := by
  intro z _
  by_cases hz : z = 0
  · subst z
    apply (meromorphicNFAt_mul_iff_left (f := poleA) (x := (0 : ℂ))
      (g := fun z : ℂ ↦ z - 1) (by fun_prop) (by simp)).mpr
    exact poleA_nf (mem_univ 0)
  · apply AnalyticAt.meromorphicNFAt
    exact (analyticAt_id.inv hz).mul (analyticAt_id.sub analyticAt_const)

theorem poles_cancel_punctured : poleA + poleB =ᶠ[𝓝[≠] (0 : ℂ)] 1 := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hn : z ≠ 0 := hz
  change z⁻¹ + z⁻¹ * (z - 1) = 1
  calc
    _ = z⁻¹ * z := by ring
    _ = 1 := inv_mul_cancel₀ hn

/-- Normal form is not closed under pointwise addition, even though meromorphicity is. -/
theorem normal_sum_not_normal : ¬MeromorphicNFAt (poleA + poleB) 0 := by
  intro h
  have he := (h.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (analyticAt_const (v := (1 : ℂ))).meromorphicNFAt).mp poles_cancel_punctured
  have := he.eq_of_nhds
  simp [poleA, poleB] at this

/-- The normalized sum restores the missing regular value at the cancelled poles. -/
theorem normalized_poles_sum_one :
    toMeromorphicNFOn (poleA + poleB) univ = (1 : ℂ → ℂ) := by
  have hf := poleA_nf.meromorphicOn.add poleB_nf.meromorphicOn
  have he : poleA + poleB =ᶠ[codiscreteWithin (univ : Set ℂ)] 1 := by
    filter_upwards [compl_singleton_mem_codiscreteWithin (s := univ) (0 : ℂ)] with z hz
    have hn : z ≠ 0 := hz
    change z⁻¹ + z⁻¹ * (z - 1) = 1
    calc
      _ = z⁻¹ * z := by ring
      _ = 1 := inv_mul_cancel₀ hn
  funext z
  have hp := (meromorphicNFOn_toMeromorphicNFOn (poleA + poleB) univ) (mem_univ z)
  have hq := (analyticAt_const (v := (1 : ℂ)) (x := z)).meromorphicNFAt
  have hg : toMeromorphicNFOn (poleA + poleB) univ =ᶠ[codiscreteWithin univ] 1 :=
    (toMeromorphicNFOn_eqOn_codiscrete hf).symm.trans he
  have hn := hp.meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    hq.meromorphicAt (mem_univ z) isOpen_univ.preperfect hg
  exact ((hp.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hq).mp hn).eq_of_nhds

local instance : Field (NormalMeromorphic (univ : Set ℂ)) :=
  normalField isOpen_univ isPreconnected_univ

example (f g : NormalMeromorphic (univ : Set ℂ)) :
    f + g = normalize isOpen_univ (f.property.meromorphicOn.add g.property.meromorphicOn) :=
  normal_add_eq_normalize isOpen_univ isPreconnected_univ f g

example (f : NormalMeromorphic (univ : Set ℂ)) (hf : f ≠ 0) : f * f⁻¹ = 1 :=
  mul_inv_cancel₀ hf

example : NormalMeromorphic (univ : Set ℂ) ≃+* MeromorphicGerms (univ : Set ℂ) :=
  normalRingEquiv isOpen_univ isPreconnected_univ

/-- The direct upper half-plane predicate produces a field element after proving the condition. -/
def upperHalfPlaneToGerm {f : ℍ → ℂ} (hf : UHP.Meromorphic f) :
    MeromorphicGerms {z : ℂ | 0 < z.im} := toGerm hf

example {f g : ℍ → ℂ} (hf : UHP.Meromorphic f) (hg : UHP.Meromorphic g) :
    upperHalfPlaneToGerm (UHP.add hf hg) =
      upperHalfPlaneToGerm hf + upperHalfPlaneToGerm hg := toGerm_add hf hg

#print axioms raw_meromorphic_zero_divisors
#print axioms normalized_poles_sum_one
#print axioms meromorphicGermField
#print axioms normalRingEquiv

end

end MMeromorphicTest.FieldChecks
