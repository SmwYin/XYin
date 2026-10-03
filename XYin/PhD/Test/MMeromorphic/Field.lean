import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.TransferInstance

/-!
# A field constructed from a meromorphic predicate

These experiments are independent of the project's existing modular function definitions.
The analytic input is `MeromorphicOn`; equivalence classes forget values on discrete subsets.
The field structure is a consequence of the predicate and connectedness, not its definition.
-/

open Filter Topology Set

namespace MMeromorphicTest

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] (U : Set 𝕜)

/-- The ring of classes represented by functions satisfying an independently given predicate. -/
def meromorphicGermRing : Subring (Germ (codiscreteWithin U) 𝕜) where
  carrier := {g | ∃ f : 𝕜 → 𝕜, MeromorphicOn f U ∧ Germ.ofFun f = g}
  zero_mem' := ⟨0, MeromorphicOn.const 0, Germ.coe_zero⟩
  one_mem' := ⟨1, MeromorphicOn.const 1, Germ.coe_one⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, Germ.coe_add f g⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, Germ.coe_neg f⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, Germ.coe_mul f g⟩

/-- The underlying type, before asserting that it is a field. -/
abbrev MeromorphicGerms := meromorphicGermRing U

variable {U}

/-- A meromorphicity proof sends a raw function into the ring of classes. -/
def toGerm {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) : MeromorphicGerms U :=
  ⟨Germ.ofFun f, f, hf, rfl⟩

theorem toGerm_eq_iff {f g : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) :
    toGerm hf = toGerm hg ↔ f =ᶠ[codiscreteWithin U] g := by
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

@[simp] theorem toGerm_add {f g : 𝕜 → 𝕜}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) :
    toGerm (hf.add hg) = toGerm hf + toGerm hg :=
  Subtype.ext (Germ.coe_add f g)

@[simp] theorem toGerm_mul {f g : 𝕜 → 𝕜}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) :
    toGerm (hf.mul hg) = toGerm hf * toGerm hg :=
  Subtype.ext (Germ.coe_mul f g)

@[simp] theorem toGerm_zero : toGerm (MeromorphicOn.const (𝕜 := 𝕜) (U := U) (0 : 𝕜)) = 0 :=
  Subtype.ext Germ.coe_zero

@[simp] theorem toGerm_one : toGerm (MeromorphicOn.const (𝕜 := 𝕜) (U := U) (1 : 𝕜)) = 1 :=
  Subtype.ext Germ.coe_one

theorem toGerm_eq_zero_iff {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) :
    toGerm hf = 0 ↔ f =ᶠ[codiscreteWithin U] 0 := by
  rw [← toGerm_zero]
  exact toGerm_eq_iff hf _

/-- A function locally equal to zero at every point gives the zero class. -/
theorem toGerm_eq_zero_of_order_top {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U)
    (h : ∀ z ∈ U, meromorphicOrderAt f z = ⊤) : toGerm hf = 0 := by
  rw [toGerm_eq_zero_iff, EventuallyEq, eventually_iff,
    mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro z hz
  exact (meromorphicOrderAt_eq_top_iff.mp (h z hz)).mono fun x hx ↦ Or.inl hx

/-- Connectedness rules out nontrivial components on which a meromorphic class vanishes. -/
theorem eventually_ne_zero_of_toGerm_ne_zero {f : 𝕜 → 𝕜}
    (hf : MeromorphicOn f U) (hU : IsPreconnected U) (h : toGerm hf ≠ 0) :
    ∀ᶠ z in codiscreteWithin U, f z ≠ 0 := by
  have hex : ∃ z ∈ U, meromorphicOrderAt f z ≠ ⊤ := by
    by_contra! hn
    exact h (toGerm_eq_zero_of_order_top hf hn)
  obtain ⟨z, hz, hn⟩ := hex
  exact MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero hf fun w hw ↦
    hf.meromorphicOrderAt_ne_top_of_isPreconnected hU hz hw hn

variable (U)

/-- Every nonempty open domain has a nontrivial codiscrete filter. -/
theorem codiscreteWithin_neBot_of_open (hU : IsOpen U) (hne : U.Nonempty) :
    NeBot (codiscreteWithin U) := by
  obtain ⟨z, hz⟩ := hne
  haveI : NeBot (𝓝[U \ {z}] z) :=
    accPt_principal_iff_nhdsWithin.mp (hU.preperfect z hz)
  exact neBot_of_le (le_iSup_of_le z (le_iSup_of_le hz le_rfl))

section FieldStructure

variable [NeBot (codiscreteWithin U)]

instance : Nontrivial (MeromorphicGerms U) := inferInstance

omit [NeBot (codiscreteWithin U)] in
/-- The inverse exists because the zero set of a nonzero connected-domain class is discrete. -/
theorem germ_isUnit_or_eq_zero (hU : IsPreconnected U) (a : MeromorphicGerms U) :
    IsUnit a ∨ a = 0 := by
  classical
  by_cases ha : a = 0
  · exact Or.inr ha
  · left
    obtain ⟨f, hf, heq⟩ := a.property
    have hae : a = toGerm hf := Subtype.ext heq.symm
    have hn : toGerm hf ≠ 0 := hae ▸ ha
    rw [isUnit_iff_exists_inv]
    refine ⟨toGerm hf.inv, ?_⟩
    rw [hae, ← toGerm_mul, ← toGerm_one, toGerm_eq_iff]
    exact (eventually_ne_zero_of_toGerm_ne_zero hf hU hn).mono fun z hz ↦
      mul_inv_cancel₀ hz

/-- The field structure is derived from `MeromorphicOn` and connectedness. -/
noncomputable abbrev meromorphicGermField (hU : IsPreconnected U) :
    Field (MeromorphicGerms U) :=
  Field.ofIsUnitOrEqZero (germ_isUnit_or_eq_zero U hU)

/-- The derived inverse agrees with the class of the ordinary pointwise inverse. -/
theorem toGerm_inv (hU : IsPreconnected U) {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) :
    letI := meromorphicGermField U hU
    toGerm hf.inv = (toGerm hf)⁻¹ := by
  letI := meromorphicGermField U hU
  by_cases ha : toGerm hf = 0
  · rw [ha, inv_zero, toGerm_eq_zero_iff]
    exact (toGerm_eq_zero_iff hf |>.mp ha).mono fun z hz ↦ by simp [hz]
  · apply eq_inv_of_mul_eq_one_right
    rw [← toGerm_mul, ← toGerm_one, toGerm_eq_iff]
    exact (eventually_ne_zero_of_toGerm_ne_zero hf hU ha).mono fun z hz ↦
      mul_inv_cancel₀ hz

end FieldStructure

section NormalForm

variable {U}

/-- Extend a function on the domain by zero, only for use by the local analytic API. -/
noncomputable def extendDomain (f : U → 𝕜) (z : 𝕜) : 𝕜 := by
  classical
  exact if hz : z ∈ U then f ⟨z, hz⟩ else 0

@[simp] theorem extendDomain_apply (f : U → 𝕜) (z : U) : extendDomain f z = f z := by
  simp [extendDomain, z.property]

/-- Normal form representatives are actual functions on `U`. -/
def NormalMeromorphic (U : Set 𝕜) :=
  {f : U → 𝕜 // MeromorphicNFOn (extendDomain f) U}

/-- The normal-form condition independently sends a representative to its class. -/
noncomputable def normalToGerm (f : NormalMeromorphic U) : MeromorphicGerms U :=
  toGerm f.property.meromorphicOn

theorem normalToGerm_injective (hU : Preperfect U) :
    Function.Injective (normalToGerm (U := U)) := by
  intro f g heq
  apply Subtype.ext
  funext z
  have he := (toGerm_eq_iff f.property.meromorphicOn g.property.meromorphicOn).mp heq
  have hn := (f.property z.property).meromorphicAt
    |>.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (g.property z.property).meromorphicAt z.property hU he
  have hv := ((f.property z.property).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (g.property z.property)).mp hn |>.eq_of_nhds
  simpa only [extendDomain_apply] using hv

/-- Normalization of a function already known to satisfy the meromorphic predicate. -/
noncomputable def normalize (hU : IsOpen U) {f : 𝕜 → 𝕜} (_hf : MeromorphicOn f U) :
    NormalMeromorphic U := by
  refine ⟨fun z ↦ toMeromorphicNFOn f U z, ?_⟩
  intro z hz
  have he : extendDomain (fun z : U ↦ toMeromorphicNFOn f U z) =ᶠ[𝓝 z]
      toMeromorphicNFOn f U := by
    filter_upwards [hU.mem_nhds hz] with w hw
    simp [extendDomain, hw]
  exact (meromorphicNFAt_congr he).mpr (meromorphicNFOn_toMeromorphicNFOn f U hz)

theorem normalToGerm_normalize (hU : IsOpen U) {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) :
    normalToGerm (normalize hU hf) = toGerm hf := by
  rw [normalToGerm, toGerm_eq_iff]
  filter_upwards [toMeromorphicNFOn_eqOn_codiscrete hf, self_mem_codiscreteWithin U] with z hz hzu
  simpa [normalize, extendDomain, hzu] using hz.symm

/-- Each codiscrete equivalence class has a unique normal-form representative on an open domain. -/
noncomputable def normalEquiv (hU : IsOpen U) : NormalMeromorphic U ≃ MeromorphicGerms U :=
  Equiv.ofBijective normalToGerm ⟨normalToGerm_injective hU.preperfect, by
    intro a
    obtain ⟨f, hf, heq⟩ := a.property
    exact ⟨normalize hU hf, (normalToGerm_normalize hU hf).trans (Subtype.ext heq)⟩⟩

@[simp] theorem normalEquiv_apply (hU : IsOpen U) (f : NormalMeromorphic U) :
    normalEquiv hU f = normalToGerm f := rfl

@[simp] theorem normalEquiv_normalize (hU : IsOpen U) {f : 𝕜 → 𝕜}
    (hf : MeromorphicOn f U) : normalEquiv hU (normalize hU hf) = toGerm hf :=
  normalToGerm_normalize hU hf

/-- Normal representatives form a field with transported, hence normalized, operations. -/
noncomputable abbrev normalField (hU : IsOpen U) (hc : IsPreconnected U)
    [NeBot (codiscreteWithin U)] : Field (NormalMeromorphic U) := by
  letI := meromorphicGermField U hc
  exact (normalEquiv hU).field

/-- The addition transported from classes is normalization of the pointwise sum. -/
theorem normal_add_eq_normalize (hU : IsOpen U) (hc : IsPreconnected U)
    [NeBot (codiscreteWithin U)] (f g : NormalMeromorphic U) :
    letI := normalField hU hc
    f + g = normalize hU (f.property.meromorphicOn.add g.property.meromorphicOn) := by
  letI := meromorphicGermField U hc
  letI := normalField hU hc
  apply (normalEquiv hU).injective
  rw [normalEquiv_normalize, toGerm_add f.property.meromorphicOn g.property.meromorphicOn]
  exact (normalEquiv hU).apply_symm_apply _

/-- The field on normal representatives and the field on classes are ring-isomorphic. -/
noncomputable def normalRingEquiv (hU : IsOpen U) (hc : IsPreconnected U)
    [NeBot (codiscreteWithin U)] :
    letI := meromorphicGermField U hc
    letI := normalField hU hc
    NormalMeromorphic U ≃+* MeromorphicGerms U := by
  letI := meromorphicGermField U hc
  letI := normalField hU hc
  exact { normalEquiv hU with
    map_add' := fun _ _ ↦ (normalEquiv hU).apply_symm_apply _
    map_mul' := fun _ _ ↦ (normalEquiv hU).apply_symm_apply _ }

/-- The multiplication transported from classes is normalization of the pointwise product. -/
theorem normal_mul_eq_normalize (hU : IsOpen U) (hc : IsPreconnected U)
    [NeBot (codiscreteWithin U)] (f g : NormalMeromorphic U) :
    letI := normalField hU hc
    f * g = normalize hU (f.property.meromorphicOn.mul g.property.meromorphicOn) := by
  letI := meromorphicGermField U hc
  letI := normalField hU hc
  apply (normalEquiv hU).injective
  rw [normalEquiv_normalize, toGerm_mul f.property.meromorphicOn g.property.meromorphicOn]
  exact (normalEquiv hU).apply_symm_apply _

/-- The inverse transported from classes is normalization of the pointwise inverse. -/
theorem normal_inv_eq_normalize (hU : IsOpen U) (hc : IsPreconnected U)
    [NeBot (codiscreteWithin U)] (f : NormalMeromorphic U) :
    letI := normalField hU hc
    f⁻¹ = normalize hU f.property.meromorphicOn.inv := by
  letI := meromorphicGermField U hc
  letI := normalField hU hc
  apply (normalEquiv hU).injective
  rw [normalEquiv_normalize, toGerm_inv U hc f.property.meromorphicOn]
  exact (normalEquiv hU).apply_symm_apply _

end NormalForm

end MMeromorphicTest
