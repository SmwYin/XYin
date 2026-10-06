/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.ModularFunctions.Basic
import XYin.PhD.ModularFunctions.FieldAction

/-!
# The field of modular functions

The field elements of modular functions for `Γ` form an additive subgroup of the meromorphic
function field on the upper half-plane, a subring if `Γ` has determinants in `{±1}`, and a
subfield if moreover `Γ` is discrete. We transport these structures to `ModularFunction Γ`.

Canonical representatives are not closed under pointwise addition and multiplication, since the
values at poles are normalized. The operations on `ModularFunction Γ` are therefore defined
through the meromorphic field: the sum of two modular functions is the modular function whose
field element is the sum of their field elements, and similarly for the other operations. The
canonical representative of a sum agrees with the pointwise sum away from a discrete set; the
canonical representatives of negatives and inverses are the pointwise ones.

## Main definitions and results

* `UpperHalfPlane.MeromorphicField.IsModular Γ a`: the canonical representative of `a` is
  invariant under `Γ` and has at most exponential growth at every cusp of `Γ`.
* `ModularFunction.ofMeromorphicField`: the modular function with a given field element.
* `ModularFunction.addSubgroup`, `ModularFunction.subring`, `ModularFunction.subfield`: the field
  elements of modular functions.
* `AddCommGroup`, `CommRing` and `Field` instances on `ModularFunction Γ`, and the ring
  homomorphism `ModularFunction.toMeromorphicFieldRingHom`.
* `ModularFunction.range_toMeromorphicField`: the field elements of modular functions for a
  discrete `Γ` with determinants in `{±1}` form the subfield `ModularFunction.subfield Γ`.
* `ModularFunction.precomp_toMeromorphicField`: field elements of modular functions are fixed by
  precomposition with integral elements of `Γ`.
* For `Γ` of determinant one, the `ℂ`-algebra structure on `ModularFunction Γ` and the algebra
  homomorphism `ModularFunction.toMeromorphicFieldAlgHom`.
-/

open Filter UpperHalfPlane Function
open scoped Topology Manifold MatrixGroups ModularForm

noncomputable section

namespace UpperHalfPlane

/-- The slash action preserves agreement away from discrete subsets of `ℍ`. -/
theorem slash_eventuallyEq_codiscrete {f g : ℍ → ℂ} (k : ℤ) (γ : GL (Fin 2) ℝ)
    (h : f =ᶠ[codiscrete ℍ] g) : f ∣[k] γ =ᶠ[codiscrete ℍ] g ∣[k] γ := by
  rw [EventuallyEq, eventually_codiscrete_iff_forall_eventually_nhdsNE] at h ⊢
  exact fun τ ↦ slash_eventuallyEq_nhdsNE k γ (h (γ • τ))

/-- A function in normal form which agrees away from a discrete set with a function invariant
under the weight-zero slash action of `γ` is itself invariant. -/
theorem slash_zero_eq_of_eventuallyEq_codiscrete {f g : ℍ → ℂ} {γ : GL (Fin 2) ℝ}
    (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet) (hfg : f =ᶠ[codiscrete ℍ] g)
    (hg : g ∣[(0 : ℤ)] γ = g) : f ∣[(0 : ℤ)] γ = f :=
  eq_of_meromorphicNFOn_of_eventuallyEq (meromorphicNFOn_slash_zero hf γ) hf
    ((slash_eventuallyEq_codiscrete 0 γ hfg).trans (by rw [hg]; exact hfg.symm))

/-- A function in normal form which agrees away from a discrete set with a function of
exponential growth, holomorphic near infinity, has exponential growth. -/
theorem IsOfExponentialGrowth.of_eventuallyEq_codiscrete {f g : ℍ → ℂ}
    (hg : IsOfExponentialGrowth g) (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet)
    (hgd : ∀ᶠ τ in atImInfty, MDiffAt g τ) (hfg : f =ᶠ[codiscrete ℍ] g) :
    IsOfExponentialGrowth f := by
  rw [EventuallyEq, eventually_codiscrete_iff_forall_eventually_nhdsNE] at hfg
  refine hg.congr ((eventually_analyticAt_of_eventually_mdifferentiableAt hgd).mono
    fun τ hτ ↦ ?_)
  exact (apply_eq_of_eventuallyEq_nhdsNE (hf τ.im_pos) hτ.meromorphicNFAt (hfg τ)).symm

end UpperHalfPlane

namespace OnePoint.IsOfExponentialGrowthAt

variable {c : OnePoint ℝ} {f g : ℍ → ℂ}

/-- The scaling transforms of a function in normal form with exponential growth at a cusp are
holomorphic near infinity. -/
theorem eventually_mdifferentiableAt (hc : c.IsOfExponentialGrowthAt f)
    (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet) {γ : GL (Fin 2) ℝ}
    (hγ : γ • ∞ = c) : ∀ᶠ τ in atImInfty, MDiffAt (f ∣[(0 : ℤ)] γ) τ :=
  eventually_mdifferentiableAt_of_meromorphicNFOn_of_exponential_bound
    (meromorphicNFOn_slash_zero hf γ) (hc γ hγ)

/-- A function in normal form which agrees away from a discrete set with a function of
exponential growth at a cusp, whose scaling transforms are holomorphic near infinity, has
exponential growth at that cusp. -/
theorem of_eventuallyEq_codiscrete (hg : c.IsOfExponentialGrowthAt g)
    (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet)
    (hgd : ∀ γ : GL (Fin 2) ℝ, γ • ∞ = c → ∀ᶠ τ in atImInfty, MDiffAt (g ∣[(0 : ℤ)] γ) τ)
    (hfg : f =ᶠ[codiscrete ℍ] g) : c.IsOfExponentialGrowthAt f := fun γ hγ ↦
  (hg γ hγ).of_eventuallyEq_codiscrete (meromorphicNFOn_slash_zero hf γ) (hgd γ hγ)
    (slash_eventuallyEq_codiscrete 0 γ hfg)

end OnePoint.IsOfExponentialGrowthAt

namespace UpperHalfPlane.MeromorphicField

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {a b : MeromorphicField}

/-- The canonical representative of `a` is a modular function for `Γ`: it is invariant under
the weight-zero slash action of `Γ` and has at most exponential growth at every cusp of `Γ`. -/
def IsModular (Γ : Subgroup (GL (Fin 2) ℝ)) (a : MeromorphicField) : Prop :=
  (∀ γ ∈ Γ, toFun a ∣[(0 : ℤ)] γ = toFun a) ∧
    ∀ c : OnePoint ℝ, IsCusp c Γ → c.IsOfExponentialGrowthAt (toFun a)

namespace IsModular

theorem zero : IsModular Γ (0 : MeromorphicField) := by
  rw [IsModular, toFun_zero]
  exact ⟨fun γ _ ↦ SlashAction.zero_slash _ _, fun c _ ↦ OnePoint.IsOfExponentialGrowthAt.const 0⟩

theorem neg (ha : IsModular Γ a) : IsModular Γ (-a) := by
  rw [IsModular, toFun_neg]
  exact ⟨fun γ hγ ↦ by rw [SlashAction.neg_slash, ha.1 γ hγ], fun c hc ↦ (ha.2 c hc).neg⟩

theorem add (ha : IsModular Γ a) (hb : IsModular Γ b) : IsModular Γ (a + b) := by
  have hNF := meromorphicNFOn_toFun (a + b)
  have hfg := toFun_add_eventuallyEq a b
  refine ⟨fun γ hγ ↦ slash_zero_eq_of_eventuallyEq_codiscrete hNF hfg ?_, fun c hc ↦ ?_⟩
  · rw [SlashAction.add_slash, ha.1 γ hγ, hb.1 γ hγ]
  · refine ((ha.2 c hc).add (hb.2 c hc)).of_eventuallyEq_codiscrete hNF (fun γ hγ ↦ ?_) hfg
    filter_upwards [(ha.2 c hc).eventually_mdifferentiableAt (meromorphicNFOn_toFun a) hγ,
      (hb.2 c hc).eventually_mdifferentiableAt (meromorphicNFOn_toFun b) hγ] with τ h₁ h₂
    rw [SlashAction.add_slash]
    exact h₁.add h₂

private theorem mul_slash_zero (g : GL (Fin 2) ℝ) (f f' : ℍ → ℂ) :
    (f * f') ∣[(0 : ℤ)] g = ((|g.det.val| : ℝ) : ℂ) • (f ∣[(0 : ℤ)] g * f' ∣[(0 : ℤ)] g) := by
  have h := ModularForm.mul_slash 0 0 g f f'
  rw [zero_add] at h
  rw [h]
  ext τ
  simp [Complex.real_smul]

theorem one [Γ.HasDetPlusMinusOne] : IsModular Γ (1 : MeromorphicField) := by
  rw [IsModular, toFun_one]
  refine ⟨fun γ hγ ↦ funext fun τ ↦ ?_, fun c _ ↦ OnePoint.IsOfExponentialGrowthAt.const 1⟩
  simp [ModularForm.slash_apply, Subgroup.HasDetPlusMinusOne.abs_det hγ,
    -Matrix.GeneralLinearGroup.val_det_apply]

theorem mul [Γ.HasDetPlusMinusOne] (ha : IsModular Γ a) (hb : IsModular Γ b) :
    IsModular Γ (a * b) := by
  have hNF := meromorphicNFOn_toFun (a * b)
  have hfg := toFun_mul_eventuallyEq a b
  refine ⟨fun γ hγ ↦ slash_zero_eq_of_eventuallyEq_codiscrete hNF hfg ?_, fun c hc ↦ ?_⟩
  · rw [mul_slash_zero, ha.1 γ hγ, hb.1 γ hγ, Subgroup.HasDetPlusMinusOne.abs_det hγ,
      Complex.ofReal_one, one_smul]
  · refine ((ha.2 c hc).mul (hb.2 c hc)).of_eventuallyEq_codiscrete hNF (fun γ hγ ↦ ?_) hfg
    filter_upwards [(ha.2 c hc).eventually_mdifferentiableAt (meromorphicNFOn_toFun a) hγ,
      (hb.2 c hc).eventually_mdifferentiableAt (meromorphicNFOn_toFun b) hγ] with τ h₁ h₂
    rw [mul_slash_zero]
    exact (h₁.mul h₂).const_smul _

theorem inv [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] (ha : IsModular Γ a) :
    IsModular Γ a⁻¹ := by
  rw [IsModular, toFun_inv]
  refine ⟨fun γ hγ ↦ ?_, fun c hc ↦ ?_⟩
  · rw [ModularForm.inv_slash_zero, ha.1 γ hγ, ← sq_abs,
      Subgroup.HasDetPlusMinusOne.abs_det hγ, one_pow, inv_one, one_smul]
  · exact OnePoint.IsOfExponentialGrowthAt.inv ⟨toFun a, ha.1⟩ (meromorphicNFOn_toFun a) hc
      (ha.2 c hc)

end IsModular

end UpperHalfPlane.MeromorphicField

namespace ModularFunction

open MeromorphicField

variable {Γ : Subgroup (GL (Fin 2) ℝ)}

/-!
### Modular functions and their field elements
-/

/-- The modular function whose field element is `a`. -/
def ofMeromorphicField (a : MeromorphicField) (ha : IsModular Γ a) : ModularFunction Γ where
  toFun := MeromorphicField.toFun a
  slash_action_eq' := ha.1
  meromorphic' := mmeromorphicNF_iff.2 (MeromorphicField.meromorphicNFOn_toFun a)
  bdd_at_cusps' hc := ha.2 _ hc

@[simp]
theorem coe_ofMeromorphicField (a : MeromorphicField) (ha : IsModular Γ a) :
    ⇑(ofMeromorphicField a ha) = MeromorphicField.toFun a :=
  rfl

@[simp]
theorem toMeromorphicField_ofMeromorphicField (a : MeromorphicField) (ha : IsModular Γ a) :
    (ofMeromorphicField a ha).toMeromorphicField = a :=
  toMeromorphicField_eq_iff.2 rfl

/-- The field element of a modular function is modular. -/
theorem isModular_toMeromorphicField (f : ModularFunction Γ) :
    IsModular Γ f.toMeromorphicField := by
  rw [IsModular, toFun_toMeromorphicField]
  exact ⟨f.slash_action_eq', fun _ hc ↦ f.bdd_at_cusps hc⟩

@[simp]
theorem ofMeromorphicField_toMeromorphicField (f : ModularFunction Γ) :
    ofMeromorphicField f.toMeromorphicField f.isModular_toMeromorphicField = f :=
  ext fun τ ↦ by simp

/-- An element of the meromorphic field is modular iff it is the field element of a modular
function. -/
theorem isModular_iff_exists {a : MeromorphicField} :
    IsModular Γ a ↔ ∃ f : ModularFunction Γ, f.toMeromorphicField = a :=
  ⟨fun ha ↦ ⟨ofMeromorphicField a ha, toMeromorphicField_ofMeromorphicField a ha⟩,
    fun ⟨f, hf⟩ ↦ hf ▸ f.isModular_toMeromorphicField⟩

/-!
### Subgroups, subrings and subfields of field elements
-/

variable (Γ) in
/-- The field elements of modular functions for `Γ`, as an additive subgroup of the meromorphic
field. -/
def addSubgroup : AddSubgroup MeromorphicField where
  carrier := {a | IsModular Γ a}
  zero_mem' := .zero
  add_mem' := .add
  neg_mem' := .neg

theorem mem_addSubgroup_iff {a : MeromorphicField} : a ∈ addSubgroup Γ ↔ IsModular Γ a :=
  Iff.rfl

variable (Γ) in
/-- The field elements of modular functions for `Γ`, as a subring of the meromorphic field. -/
def subring [Γ.HasDetPlusMinusOne] : Subring MeromorphicField where
  __ := addSubgroup Γ
  one_mem' := .one
  mul_mem' := .mul

theorem mem_subring_iff [Γ.HasDetPlusMinusOne] {a : MeromorphicField} :
    a ∈ subring Γ ↔ IsModular Γ a :=
  Iff.rfl

variable (Γ) in
/-- The field elements of modular functions for `Γ`, as a subfield of the meromorphic field. -/
def subfield [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] : Subfield MeromorphicField where
  __ := subring Γ
  inv_mem' _ := .inv

theorem mem_subfield_iff [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] {a : MeromorphicField} :
    a ∈ subfield Γ ↔ IsModular Γ a :=
  Iff.rfl

/-- The field elements of modular functions form the subfield `ModularFunction.subfield Γ`. -/
theorem range_toMeromorphicField [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] :
    Set.range (toMeromorphicField (Γ := Γ)) = subfield Γ := by
  ext a
  exact isModular_iff_exists.symm

/-!
### The additive group structure
-/

instance : Zero (ModularFunction Γ) :=
  ⟨ofMeromorphicField 0 .zero⟩

instance : Add (ModularFunction Γ) :=
  ⟨fun f g ↦ ofMeromorphicField _ (f.isModular_toMeromorphicField.add
    g.isModular_toMeromorphicField)⟩

instance : Neg (ModularFunction Γ) :=
  ⟨fun f ↦ ofMeromorphicField _ f.isModular_toMeromorphicField.neg⟩

instance : Sub (ModularFunction Γ) :=
  ⟨fun f g ↦ ofMeromorphicField (f.toMeromorphicField - g.toMeromorphicField)
    ((addSubgroup Γ).sub_mem f.isModular_toMeromorphicField g.isModular_toMeromorphicField)⟩

instance : SMul ℕ (ModularFunction Γ) :=
  ⟨fun n f ↦ ofMeromorphicField (n • f.toMeromorphicField)
    ((addSubgroup Γ).nsmul_mem f.isModular_toMeromorphicField n)⟩

instance : SMul ℤ (ModularFunction Γ) :=
  ⟨fun n f ↦ ofMeromorphicField (n • f.toMeromorphicField)
    ((addSubgroup Γ).zsmul_mem f.isModular_toMeromorphicField n)⟩

@[simp]
theorem toMeromorphicField_zero : (0 : ModularFunction Γ).toMeromorphicField = 0 :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_add (f g : ModularFunction Γ) :
    (f + g).toMeromorphicField = f.toMeromorphicField + g.toMeromorphicField :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_neg (f : ModularFunction Γ) :
    (-f).toMeromorphicField = -f.toMeromorphicField :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_sub (f g : ModularFunction Γ) :
    (f - g).toMeromorphicField = f.toMeromorphicField - g.toMeromorphicField :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_nsmul (n : ℕ) (f : ModularFunction Γ) :
    (n • f).toMeromorphicField = n • f.toMeromorphicField :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_zsmul (n : ℤ) (f : ModularFunction Γ) :
    (n • f).toMeromorphicField = n • f.toMeromorphicField :=
  toMeromorphicField_ofMeromorphicField _ _

instance : AddCommGroup (ModularFunction Γ) :=
  toMeromorphicField_injective.addCommGroup _ toMeromorphicField_zero toMeromorphicField_add
    toMeromorphicField_neg toMeromorphicField_sub (fun _ _ ↦ toMeromorphicField_nsmul _ _)
    (fun _ _ ↦ toMeromorphicField_zsmul _ _)

/-- The zero modular function is the zero function. -/
@[simp]
theorem coe_zero : ⇑(0 : ModularFunction Γ) = 0 :=
  toFun_zero

@[simp]
theorem coe_neg (f : ModularFunction Γ) : ⇑(-f) = -⇑f := by
  change MeromorphicField.toFun _ = _
  rw [toFun_neg, toFun_toMeromorphicField]

/-- The canonical representative of a sum agrees with the pointwise sum away from a discrete
subset of `ℍ`. -/
theorem coe_add_eventuallyEq (f g : ModularFunction Γ) : ⇑(f + g) =ᶠ[codiscrete ℍ] ⇑f + ⇑g := by
  simpa only [toFun_toMeromorphicField] using
    toFun_add_eventuallyEq f.toMeromorphicField g.toMeromorphicField

/-!
### The ring structure
-/

section Ring

variable [Γ.HasDetPlusMinusOne]

instance : One (ModularFunction Γ) :=
  ⟨ofMeromorphicField 1 .one⟩

instance : Mul (ModularFunction Γ) :=
  ⟨fun f g ↦ ofMeromorphicField _ (f.isModular_toMeromorphicField.mul
    g.isModular_toMeromorphicField)⟩

instance : Pow (ModularFunction Γ) ℕ :=
  ⟨fun f n ↦ ofMeromorphicField (f.toMeromorphicField ^ n)
    ((subring Γ).pow_mem f.isModular_toMeromorphicField n)⟩

instance : NatCast (ModularFunction Γ) :=
  ⟨fun n ↦ ofMeromorphicField n (natCast_mem (subring Γ) n)⟩

instance : IntCast (ModularFunction Γ) :=
  ⟨fun n ↦ ofMeromorphicField n (intCast_mem (subring Γ) n)⟩

@[simp]
theorem toMeromorphicField_one : (1 : ModularFunction Γ).toMeromorphicField = 1 :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_mul (f g : ModularFunction Γ) :
    (f * g).toMeromorphicField = f.toMeromorphicField * g.toMeromorphicField :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_pow (f : ModularFunction Γ) (n : ℕ) :
    (f ^ n).toMeromorphicField = f.toMeromorphicField ^ n :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_natCast (n : ℕ) :
    (n : ModularFunction Γ).toMeromorphicField = n :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_intCast (n : ℤ) :
    (n : ModularFunction Γ).toMeromorphicField = n :=
  toMeromorphicField_ofMeromorphicField _ _

instance : CommRing (ModularFunction Γ) :=
  toMeromorphicField_injective.commRing _ toMeromorphicField_zero toMeromorphicField_one
    toMeromorphicField_add toMeromorphicField_mul toMeromorphicField_neg toMeromorphicField_sub
    (fun _ _ ↦ toMeromorphicField_nsmul _ _) (fun _ _ ↦ toMeromorphicField_zsmul _ _)
    toMeromorphicField_pow toMeromorphicField_natCast toMeromorphicField_intCast

/-- The unit modular function is the constant function one. -/
@[simp]
theorem coe_one : ⇑(1 : ModularFunction Γ) = 1 :=
  toFun_one

/-- The canonical representative of a product agrees with the pointwise product away from a
discrete subset of `ℍ`. -/
theorem coe_mul_eventuallyEq (f g : ModularFunction Γ) : ⇑(f * g) =ᶠ[codiscrete ℍ] ⇑f * ⇑g := by
  simpa only [toFun_toMeromorphicField] using
    toFun_mul_eventuallyEq f.toMeromorphicField g.toMeromorphicField

variable (Γ) in
/-- The field element of a modular function, as a ring homomorphism. -/
def toMeromorphicFieldRingHom : ModularFunction Γ →+* MeromorphicField where
  toFun := toMeromorphicField
  map_one' := toMeromorphicField_one
  map_mul' := toMeromorphicField_mul
  map_zero' := toMeromorphicField_zero
  map_add' := toMeromorphicField_add

@[simp]
theorem toMeromorphicFieldRingHom_apply (f : ModularFunction Γ) :
    toMeromorphicFieldRingHom Γ f = f.toMeromorphicField :=
  rfl

theorem toMeromorphicFieldRingHom_injective :
    Function.Injective (toMeromorphicFieldRingHom Γ) :=
  toMeromorphicField_injective

theorem range_toMeromorphicFieldRingHom :
    (toMeromorphicFieldRingHom Γ).range = subring Γ := by
  ext a
  exact isModular_iff_exists.symm

end Ring

/-!
### The field structure
-/

section Field

variable [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne]

instance : Inv (ModularFunction Γ) :=
  ⟨fun f ↦ ofMeromorphicField _ f.isModular_toMeromorphicField.inv⟩

instance : Div (ModularFunction Γ) :=
  ⟨fun f g ↦ ofMeromorphicField (f.toMeromorphicField / g.toMeromorphicField)
    ((subfield Γ).div_mem f.isModular_toMeromorphicField g.isModular_toMeromorphicField)⟩

instance : Pow (ModularFunction Γ) ℤ :=
  ⟨fun f n ↦ ofMeromorphicField (f.toMeromorphicField ^ n)
    ((subfield Γ).zpow_mem f.isModular_toMeromorphicField n)⟩

instance : NNRatCast (ModularFunction Γ) :=
  ⟨fun q ↦ ofMeromorphicField q (SubfieldClass.nnratCast_mem (subfield Γ) q)⟩

instance : RatCast (ModularFunction Γ) :=
  ⟨fun q ↦ ofMeromorphicField q (SubfieldClass.ratCast_mem (subfield Γ) q)⟩

instance : SMul ℚ≥0 (ModularFunction Γ) :=
  ⟨fun q f ↦ ofMeromorphicField (q • f.toMeromorphicField)
    (SubfieldClass.nnqsmul_mem (subfield Γ) q f.isModular_toMeromorphicField)⟩

instance : SMul ℚ (ModularFunction Γ) :=
  ⟨fun q f ↦ ofMeromorphicField (q • f.toMeromorphicField)
    (SubfieldClass.qsmul_mem (subfield Γ) q f.isModular_toMeromorphicField)⟩

@[simp]
theorem toMeromorphicField_inv (f : ModularFunction Γ) :
    f⁻¹.toMeromorphicField = f.toMeromorphicField⁻¹ :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_div (f g : ModularFunction Γ) :
    (f / g).toMeromorphicField = f.toMeromorphicField / g.toMeromorphicField :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_zpow (f : ModularFunction Γ) (n : ℤ) :
    (f ^ n).toMeromorphicField = f.toMeromorphicField ^ n :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_nnratCast (q : ℚ≥0) :
    (q : ModularFunction Γ).toMeromorphicField = q :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_ratCast (q : ℚ) :
    (q : ModularFunction Γ).toMeromorphicField = q :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_nnqsmul (q : ℚ≥0) (f : ModularFunction Γ) :
    (q • f).toMeromorphicField = q • f.toMeromorphicField :=
  toMeromorphicField_ofMeromorphicField _ _

@[simp]
theorem toMeromorphicField_qsmul (q : ℚ) (f : ModularFunction Γ) :
    (q • f).toMeromorphicField = q • f.toMeromorphicField :=
  toMeromorphicField_ofMeromorphicField _ _

instance : Field (ModularFunction Γ) :=
  toMeromorphicField_injective.field _ toMeromorphicField_zero toMeromorphicField_one
    toMeromorphicField_add toMeromorphicField_mul toMeromorphicField_neg toMeromorphicField_sub
    toMeromorphicField_inv toMeromorphicField_div (fun _ _ ↦ toMeromorphicField_nsmul _ _)
    (fun _ _ ↦ toMeromorphicField_zsmul _ _) (fun _ _ ↦ toMeromorphicField_nnqsmul _ _)
    (fun _ _ ↦ toMeromorphicField_qsmul _ _) toMeromorphicField_pow toMeromorphicField_zpow
    toMeromorphicField_natCast toMeromorphicField_intCast toMeromorphicField_nnratCast
    toMeromorphicField_ratCast

/-- The reciprocal of a modular function is the pointwise reciprocal. -/
@[simp]
theorem coe_inv (f : ModularFunction Γ) : ⇑f⁻¹ = (⇑f)⁻¹ := by
  change MeromorphicField.toFun _ = _
  rw [toFun_inv, toFun_toMeromorphicField]

theorem fieldRange_toMeromorphicFieldRingHom :
    (toMeromorphicFieldRingHom Γ).fieldRange = subfield Γ := by
  ext a
  exact isModular_iff_exists.symm

end Field

/-!
### Invariance under precomposition
-/

/-- Precomposition by an integral element of `Γ` fixes the field element of a modular function
for `Γ`. -/
theorem precomp_toMeromorphicField (f : ModularFunction Γ) {δ : SL(2, ℤ)}
    (hδ : (δ : GL (Fin 2) ℝ) ∈ Γ) :
    precomp δ f.toMeromorphicField = f.toMeromorphicField := by
  refine toFun_injective ?_
  rw [toFun_precomp, toFun_toMeromorphicField]
  exact funext (ModularForm.SL_slash_zero_eq_iff.1 (f.slash_action_eq' _ hδ))

/-!
### The algebra structure over `ℂ`
-/

section Algebra

variable [Γ.HasDetOne]

/-- Constants are modular for groups of determinant one. -/
theorem _root_.UpperHalfPlane.MeromorphicField.IsModular.algebraMap (c : ℂ) :
    IsModular Γ (algebraMap ℂ MeromorphicField c) := by
  rw [IsModular, toFun_algebraMap_complex]
  refine ⟨fun γ hγ ↦ funext fun τ ↦ ?_, fun _ _ ↦ OnePoint.IsOfExponentialGrowthAt.const c⟩
  simp [ModularForm.slash_apply, σ, Subgroup.HasDetOne.det_eq hγ]

/-- Constant modular functions. -/
def constRingHom : ℂ →+* ModularFunction Γ where
  toFun c := ofMeromorphicField _ (IsModular.algebraMap c)
  map_one' := toMeromorphicField_injective (by simp)
  map_mul' _ _ := toMeromorphicField_injective (by simp)
  map_zero' := toMeromorphicField_injective (by simp)
  map_add' _ _ := toMeromorphicField_injective (by simp)

instance : Algebra ℂ (ModularFunction Γ) := constRingHom.toAlgebra

@[simp]
theorem toMeromorphicField_algebraMap (c : ℂ) :
    (algebraMap ℂ (ModularFunction Γ) c).toMeromorphicField = algebraMap ℂ MeromorphicField c :=
  toMeromorphicField_ofMeromorphicField _ (IsModular.algebraMap c)

@[simp]
theorem toMeromorphicField_smul (c : ℂ) (f : ModularFunction Γ) :
    (c • f).toMeromorphicField = c • f.toMeromorphicField := by
  rw [Algebra.smul_def, toMeromorphicField_mul, toMeromorphicField_algebraMap, ← Algebra.smul_def]

/-- Constant modular functions are constant functions. -/
@[simp]
theorem coe_algebraMap (c : ℂ) : ⇑(algebraMap ℂ (ModularFunction Γ) c) = fun _ ↦ c :=
  toFun_algebraMap_complex c

variable (Γ) in
/-- The field element of a modular function, as a `ℂ`-algebra homomorphism. -/
def toMeromorphicFieldAlgHom : ModularFunction Γ →ₐ[ℂ] MeromorphicField where
  __ := toMeromorphicFieldRingHom Γ
  commutes' := toMeromorphicField_algebraMap

@[simp]
theorem toMeromorphicFieldAlgHom_apply (f : ModularFunction Γ) :
    toMeromorphicFieldAlgHom Γ f = f.toMeromorphicField :=
  rfl

end Algebra

end ModularFunction
