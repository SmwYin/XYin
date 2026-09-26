/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import XYin.PhD.ModularFunctions.MeromorphicField
import XYin.PhD.ModularFunctions.NormalFormSlash

/-!
# Holomorphic functions and the modular group action on meromorphic functions

Holomorphic functions on the upper half-plane form a subring of the pointwise function ring
and embed in the field of meromorphic germs. Precomposition by `SL₂(ℤ)` descends to an
automorphism of this field because its action preserves punctured neighborhoods.

## Main definitions and results

* `UpperHalfPlane.HolomorphicFunction`: holomorphic functions on `ℍ`, a `ℂ`-algebra and a domain.
* `UpperHalfPlane.MeromorphicField.holomorphicToMeromorphic`: the embedding into the meromorphic
  field.
* `UpperHalfPlane.MeromorphicField.precomp δ`: precomposition by `δ ∈ SL₂(ℤ)`, a ring
  automorphism of the meromorphic field, with `toFun_precomp`, `precomp_one` and `precomp_mul`.
-/

open Function MatrixGroups
open scoped Manifold

noncomputable section

namespace UpperHalfPlane

/-- The subring of holomorphic functions on the upper half-plane. -/
def holomorphicFunctions : Subring (ℍ → ℂ) where
  carrier := {f | MDiff f}
  zero_mem' := mdifferentiable_const
  one_mem' := mdifferentiable_const
  add_mem' := fun hf hg ↦ hf.add hg
  neg_mem' := fun hf ↦ hf.neg
  mul_mem' := fun hf hg ↦ hf.mul hg

/-- A holomorphic function on the upper half-plane. -/
abbrev HolomorphicFunction := holomorphicFunctions

/-- Holomorphic functions are determined by their values. -/
@[ext]
theorem HolomorphicFunction.ext {f g : HolomorphicFunction} (h : ∀ τ, f.1 τ = g.1 τ) : f = g :=
  Subtype.ext (funext h)

/-- The embedding of constants into the holomorphic functions. -/
def HolomorphicFunction.constRingHom : ℂ →+* HolomorphicFunction where
  toFun z := ⟨fun _ ↦ z, mdifferentiable_const⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Holomorphic functions form a `ℂ`-algebra, with constants acting by multiplication. -/
instance : Algebra ℂ HolomorphicFunction := HolomorphicFunction.constRingHom.toAlgebra

/-- The algebra map from `ℂ` sends a scalar to the constant function. -/
@[simp]
theorem HolomorphicFunction.coe_algebraMap (c : ℂ) :
    ((algebraMap ℂ HolomorphicFunction c : HolomorphicFunction) : ℍ → ℂ) = fun _ ↦ c :=
  rfl

namespace MeromorphicField

/-- Holomorphic functions embed in the field of meromorphic germs. -/
def holomorphicToMeromorphic : HolomorphicFunction →+* MeromorphicField where
  toFun f := MeromorphicField.ofHolomorphic f f.property
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The canonical representative of a holomorphic germ is its original function. -/
@[simp]
theorem toFun_holomorphicToMeromorphic (f : HolomorphicFunction) :
    MeromorphicField.toFun (holomorphicToMeromorphic f) = f :=
  MeromorphicField.toFun_ofHolomorphic f f.property

theorem holomorphicToMeromorphic_injective : Function.Injective holomorphicToMeromorphic :=
  injective_of_toFun_eq Subtype.val_injective toFun_holomorphicToMeromorphic

instance : Algebra HolomorphicFunction MeromorphicField := holomorphicToMeromorphic.toAlgebra

/-- The embedding of holomorphic functions preserves their values everywhere. -/
@[simp]
theorem toFun_algebraMap (f : HolomorphicFunction) :
    toFun (algebraMap HolomorphicFunction MeromorphicField f) = f :=
  toFun_holomorphicToMeromorphic f

/-- The embedding of a holomorphic function is the element defined by the function. -/
theorem algebraMap_eq_ofMeromorphic (f : HolomorphicFunction) :
    algebraMap HolomorphicFunction MeromorphicField f =
      ofMeromorphic f.1 f.2.meromorphicNFOn_comp_ofComplex.meromorphicOn :=
  rfl

instance : IsScalarTower ℂ HolomorphicFunction MeromorphicField :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance : NoZeroDivisors HolomorphicFunction :=
  holomorphicToMeromorphic_injective.noZeroDivisors holomorphicToMeromorphic
    holomorphicToMeromorphic.map_zero holomorphicToMeromorphic.map_mul

/-- Holomorphic functions on the connected upper half-plane form a domain. -/
instance : IsDomain HolomorphicFunction :=
  holomorphicToMeromorphic_injective.isDomain holomorphicToMeromorphic

private def smulComplex (delta : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (↑(delta • (ofComplex z : ℍ)) : ℂ)

private theorem smulComplex_tendsto (delta : SL(2, ℤ)) :
    Filter.Tendsto (smulComplex delta) (Filter.codiscreteWithin upperHalfPlaneSet)
      (Filter.codiscreteWithin upperHalfPlaneSet) := by
  intro s hs
  apply Filter.eventually_codiscreteWithin_of_forall_eventually_nhdsNE
  intro z hz
  have hs' := (Filter.eventually_codiscreteWithin_iff_forall_eventually_nhdsNE
    isOpen_upperHalfPlaneSet).mp hs (smulComplex delta z) (delta • ofComplex z).im_pos
  have han := (⟨z, hz⟩ : ℍ).analyticAt_smul (sl2_det_pos delta)
  have hne := (⟨z, hz⟩ : ℍ).deriv_smul_ne_zero (sl2_det_pos delta)
  exact (han.differentiableAt.hasDerivAt.tendsto_nhdsNE hne).eventually hs'

private theorem meromorphicOn_comp_smulComplex {f : ℂ → ℂ}
    (hf : MeromorphicOn f upperHalfPlaneSet) (delta : SL(2, ℤ)) :
    MeromorphicOn (f ∘ smulComplex delta) upperHalfPlaneSet := fun z hz ↦
  (hf (smulComplex delta z) (delta • ofComplex z).im_pos).comp_analyticAt
    (g := smulComplex delta) (x := z) ((⟨z, hz⟩ : ℍ).analyticAt_smul (sl2_det_pos delta))

/-- Precomposition by an integral matrix preserves meromorphy on the upper half-plane. -/
theorem meromorphicOn_comp_sl2_smul {f : ℍ → ℂ}
    (hf : MeromorphicOn (f ∘ ofComplex) upperHalfPlaneSet) (delta : SL(2, ℤ)) :
    MeromorphicOn ((fun τ ↦ f (delta • τ)) ∘ ofComplex) upperHalfPlaneSet := by
  convert meromorphicOn_comp_smulComplex hf delta using 1
  funext z
  simp [smulComplex]

private def precompGerm (delta : SL(2, ℤ)) :
    Filter.Germ (Filter.codiscreteWithin upperHalfPlaneSet) ℂ →+*
      Filter.Germ (Filter.codiscreteWithin upperHalfPlaneSet) ℂ where
  toFun a := a.compTendsto (smulComplex delta) (smulComplex_tendsto delta)
  map_one' := rfl
  map_mul' a b := Filter.Germ.inductionOn₂ a b fun _ _ ↦ rfl
  map_zero' := rfl
  map_add' a b := Filter.Germ.inductionOn₂ a b fun _ _ ↦ rfl

private def precompHom (delta : SL(2, ℤ)) : MeromorphicField →+* MeromorphicField where
  toFun a := ⟨precompGerm delta a.1, by
    obtain ⟨f, hf, hfa⟩ := MeromorphicOn.mem_germRing_iff.mp a.2
    refine MeromorphicOn.mem_germRing_iff.mpr
      ⟨f ∘ smulComplex delta, meromorphicOn_comp_smulComplex hf delta, ?_⟩
    rw [← hfa]
    rfl⟩
  map_one' := Subtype.ext (precompGerm delta).map_one
  map_mul' a b := Subtype.ext ((precompGerm delta).map_mul a.1 b.1)
  map_zero' := Subtype.ext (precompGerm delta).map_zero
  map_add' a b := Subtype.ext ((precompGerm delta).map_add a.1 b.1)

private theorem precompHom_inv (delta : SL(2, ℤ)) (a : MeromorphicField) :
    precompHom delta⁻¹ (precompHom delta a) = a := by
  apply Subtype.ext
  obtain ⟨f, hf, hfa⟩ := MeromorphicOn.mem_germRing_iff.mp a.2
  change precompGerm delta⁻¹ (precompGerm delta a.1) = a.1
  rw [← hfa]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [Filter.self_mem_codiscreteWithin upperHalfPlaneSet] with z hz
  simp [smulComplex, Function.comp_def, ofComplex_apply_of_im_pos hz]

/-- Precomposition of meromorphic germs by an element of `SL₂(ℤ)`. -/
def precomp (delta : SL(2, ℤ)) : MeromorphicField ≃+* MeromorphicField where
  __ := precompHom delta
  invFun := precompHom delta⁻¹
  left_inv := precompHom_inv delta
  right_inv a := by simpa using precompHom_inv delta⁻¹ a

/-- Precomposition of the element defined by a meromorphic function is defined by the
precomposed function. -/
theorem precomp_ofMeromorphic (delta : SL(2, ℤ)) {f : ℍ → ℂ}
    (hf : MeromorphicOn (f ∘ ofComplex) upperHalfPlaneSet) :
    precomp delta (ofMeromorphic f hf) =
      ofMeromorphic (fun τ ↦ f (delta • τ)) (meromorphicOn_comp_sl2_smul hf delta) := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards with z
  simp [smulComplex]

/-- Canonical representatives of precomposed elements are precomposed canonical
representatives. -/
@[simp]
theorem toFun_precomp (delta : SL(2, ℤ)) (a : MeromorphicField) :
    toFun (precomp delta a) = fun τ ↦ toFun a (delta • τ) := by
  have hNF := meromorphicNFOn_slash_zero (meromorphicNFOn_toFun a) delta
  rw [← ModularForm.SL_slash, ModularForm.SL_slash_zero_eq] at hNF
  conv_lhs => rw [← ofMeromorphic_toFun a, precomp_ofMeromorphic]
  exact toFun_ofMeromorphic hNF

@[simp]
theorem precomp_one : precomp 1 = RingEquiv.refl MeromorphicField :=
  RingEquiv.ext fun a ↦ toFun_injective (by simp)

/-- Precomposition is a right action: precomposing by `δ₁ * δ₂` precomposes first by `δ₁` and
then by `δ₂`. -/
theorem precomp_mul (delta₁ delta₂ : SL(2, ℤ)) :
    precomp (delta₁ * delta₂) = (precomp delta₁).trans (precomp delta₂) :=
  RingEquiv.ext fun a ↦ toFun_injective (by simp [mul_smul])

theorem precomp_symm (delta : SL(2, ℤ)) : (precomp delta).symm = precomp delta⁻¹ :=
  RingEquiv.ext fun _ ↦ rfl

/-- Precomposition agrees with composition of holomorphic representatives. -/
@[simp]
theorem precomp_algebraMap (delta : SL(2, ℤ)) (f : HolomorphicFunction) :
    precomp delta (algebraMap HolomorphicFunction MeromorphicField f) =
      algebraMap HolomorphicFunction MeromorphicField
        ⟨fun tau ↦ f.1 (delta • tau), f.property.comp (sl2_mdifferentiable delta)⟩ :=
  precomp_ofMeromorphic delta _

/-- Precomposition of a holomorphic function which transforms into another one. -/
theorem precomp_algebraMap_eq_of_forall (delta : SL(2, ℤ)) (f g : HolomorphicFunction)
    (h : ∀ τ, f.1 (delta • τ) = g.1 τ) :
    precomp delta (algebraMap HolomorphicFunction MeromorphicField f) =
      algebraMap HolomorphicFunction MeromorphicField g := by
  rw [precomp_algebraMap]
  exact congrArg _ (HolomorphicFunction.ext h)

end MeromorphicField

end UpperHalfPlane
