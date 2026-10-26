/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.ModularFunctions.MeromorphicField
import XYin.PhD.ModularFunctions.ManifoldMeromorphic
import XYin.PhD.ModularFunctions.Cusps
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms

/-!
# Modular functions

A modular function is a weight-zero slash-invariant function which is meromorphic in normal
form on the upper half-plane and has at most exponential growth at every cusp.
The analytic condition is the independent predicate `MMeromorphicNF` on the function itself;
its element of the meromorphic function field is constructed afterwards. As in `ModularForm`,
growth is uniform on a sufficiently high half-plane and is tested after every scaling
transformation.
The definition of growth does not choose a period or cusp width.

Canonical representatives remove arbitrary values at removable singularities and assign zero
at poles. The ambient field operations are operations on codiscrete equivalence classes;
their canonical representatives need not be pointwise sums or products at poles.

## Main definitions

* `ModularFunction Γ`: modular functions for a subgroup `Γ` of `GL₂(ℝ)`.
* `ModularFunction.toMeromorphicField`: the element of the meromorphic field represented by a
  modular function.
* `ModularFunction.ofLevelOneCuspData`, `ModularFunction.ofLevelOneHolomorphic`: constructors of
  level-one modular functions from invariance and meromorphy of the period-one cusp expansion.

The ring and field structures on `ModularFunction Γ` are in
`XYin.PhD.ModularFunctions.Algebra`.
-/

open UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

noncomputable section

/-- A weight-zero modular function, realized as a canonical meromorphic representative with
at most exponential growth at all cusps. -/
structure ModularFunction (Γ : Subgroup (GL (Fin 2) ℝ)) extends SlashInvariantForm Γ 0 where
  /-- The underlying function is meromorphic in normal form in manifold charts. -/
  meromorphic' : MMeromorphicNF toFun
  /-- Every cusp transform grows at most exponentially, uniformly in its real part. -/
  bdd_at_cusps' {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsExpBoundedAt toFun 0

namespace ModularFunction

variable {Γ : Subgroup (GL (Fin 2) ℝ)}

instance : FunLike (ModularFunction Γ) ℍ ℂ where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.ext' h

instance : SlashInvariantFormClass (ModularFunction Γ) Γ 0 where
  slash_action_eq f := f.slash_action_eq'

@[simp]
theorem toSlashInvariantForm_coe (f : ModularFunction Γ) :
    (f.toSlashInvariantForm : ℍ → ℂ) = f := rfl

@[simp]
theorem coe_mk (f : SlashInvariantForm Γ 0) (h₁ h₂) :
    ⇑(ModularFunction.mk f h₁ h₂) = f := rfl

@[ext]
theorem ext {f g : ModularFunction Γ} (h : ∀ τ, f τ = g τ) : f = g := DFunLike.ext f g h

/-- The ambient meromorphic function field element represented by a modular function. -/
def toMeromorphicField (f : ModularFunction Γ) : MeromorphicField :=
  MeromorphicField.ofMeromorphic f (mmeromorphicNF_iff.1 f.meromorphic').meromorphicOn

/-- The field element's canonical representative is exactly the bundled function. -/
@[simp]
theorem toFun_toMeromorphicField (f : ModularFunction Γ) :
    MeromorphicField.toFun f.toMeromorphicField = f :=
  MeromorphicField.toFun_ofMeromorphic (mmeromorphicNF_iff.1 f.meromorphic')

/-- The analytic predicate is imposed directly on the underlying function. -/
theorem meromorphicNF (f : ModularFunction Γ) : MMeromorphicNF f := f.meromorphic'

/-- Modular functions have meromorphic normal form throughout the upper half-plane. -/
theorem meromorphicNFOn (f : ModularFunction Γ) :
    MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet :=
  mmeromorphicNF_iff.1 f.meromorphic'

/-- In particular, a modular function is meromorphic at every point of the upper half-plane. -/
theorem meromorphicOn (f : ModularFunction Γ) :
    MeromorphicOn (f ∘ ofComplex) upperHalfPlaneSet := f.meromorphicNFOn.meromorphicOn

/-- The field element of a modular function is characterized by its canonical representative. -/
theorem toMeromorphicField_eq_iff {f : ModularFunction Γ} {a : MeromorphicField} :
    f.toMeromorphicField = a ↔ (f : ℍ → ℂ) = MeromorphicField.toFun a := by
  rw [← f.toFun_toMeromorphicField]
  exact MeromorphicField.toFun_injective.eq_iff.symm

/-- The field element of a modular function is the element defined by the function. -/
theorem toMeromorphicField_eq_ofMeromorphic (f : ModularFunction Γ) :
    f.toMeromorphicField = MeromorphicField.ofMeromorphic f f.meromorphicOn :=
  toMeromorphicField_eq_iff.2 (MeromorphicField.toFun_ofMeromorphic f.meromorphicNFOn).symm

/-- Canonical representatives identify modular functions with their ambient field elements. -/
theorem toMeromorphicField_injective :
    Function.Injective (toMeromorphicField (Γ := Γ)) :=
  MeromorphicField.injective_of_toFun_eq DFunLike.coe_injective toFun_toMeromorphicField

/-- The growth condition of a modular function at a specified cusp. -/
theorem bdd_at_cusps (f : ModularFunction Γ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsExpBoundedAt f 0 := f.bdd_at_cusps' hc

/-- A modular function is meromorphic at every cusp, in the usual q-coordinate sense. -/
theorem meromorphic_at_cusps [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne]
    (f : ModularFunction Γ) {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsMeromorphicAt f :=
  (OnePoint.isExpBoundedAt_zero_iff_isMeromorphicAt f.toSlashInvariantForm
    f.meromorphicNFOn hc).mp (f.bdd_at_cusps hc)

/-- Meromorphy in any chosen positive-period chart of a cusp. -/
theorem meromorphicAt_cuspFunction (f : ModularFunction Γ) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) {g : GL (Fin 2) ℝ} (hg : g • OnePoint.infty = c)
    {h : ℝ} (hh : 0 < h) (hper : Function.Periodic ((f ∣[(0 : ℤ)] g) ∘ ofComplex) h) :
    MeromorphicAt (cuspFunction h (f ∣[(0 : ℤ)] g)) 0 :=
  (OnePoint.isExpBoundedAt_zero_iff_meromorphicAt_cuspFunction
    f.meromorphicNFOn hg hh hper).mp (f.bdd_at_cusps hc)

end ModularFunction

/-!
## Level-one modular functions
-/

/-- A function invariant under the weight-zero slash action of `SL₂(ℤ)` has period one. -/
theorem UpperHalfPlane.periodic_comp_ofComplex_of_slashInvariant {f : ℍ → ℂ}
    (hinv : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) : Function.Periodic (f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex
    (⟨f, by rintro _ ⟨γ, rfl⟩; exact hinv γ⟩ : SlashInvariantForm 𝒮ℒ 0) (by simp)

namespace ModularFunction

/-- Construct a level-one modular function from its canonical meromorphic representative,
invariance, and meromorphy of its period-one cusp expansion. -/
def ofLevelOneCuspData (f : ℍ → ℂ) (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet)
    (hinv : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hcusp : MeromorphicAt (cuspFunction 1 f) 0) :
    ModularFunction 𝒮ℒ where
  toFun := f
  slash_action_eq' := by
    rintro _ ⟨γ, rfl⟩
    exact hinv γ
  meromorphic' := mmeromorphicNF_iff.2 hf
  bdd_at_cusps' hc := OnePoint.isOfExponentialGrowthAt_of_forall_SL2Z (fun γ ↦ by
    rw [hinv γ]
    exact isOfExponentialGrowth_of_meromorphicAt_cuspFunction one_pos
      (periodic_comp_ofComplex_of_slashInvariant hinv) hcusp) hc

@[simp]
theorem coe_ofLevelOneCuspData (f : ℍ → ℂ)
    (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet)
    (hinv : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hcusp : MeromorphicAt (cuspFunction 1 f) 0) :
    (ofLevelOneCuspData f hf hinv hcusp : ℍ → ℂ) = f := rfl

/-- Construct a level-one modular function from a holomorphic invariant function whose
period-one cusp expansion is meromorphic. -/
def ofLevelOneHolomorphic (f : ℍ → ℂ) (hf : MDiff f)
    (hinv : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hcusp : MeromorphicAt (cuspFunction 1 f) 0) :
    ModularFunction 𝒮ℒ :=
  ofLevelOneCuspData f hf.meromorphicNFOn_comp_ofComplex hinv hcusp

@[simp]
theorem coe_ofLevelOneHolomorphic (f : ℍ → ℂ) (hf : MDiff f)
    (hinv : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hcusp : MeromorphicAt (cuspFunction 1 f) 0) :
    (ofLevelOneHolomorphic f hf hinv hcusp : ℍ → ℂ) = f := rfl

/-- The field element of a holomorphic level-one modular function is its holomorphic germ. -/
theorem toMeromorphicField_ofLevelOneHolomorphic (f : ℍ → ℂ) (hf : MDiff f)
    (hinv : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hcusp : MeromorphicAt (cuspFunction 1 f) 0) :
    (ofLevelOneHolomorphic f hf hinv hcusp).toMeromorphicField =
      MeromorphicField.ofHolomorphic f hf :=
  toMeromorphicField_eq_iff.2 (MeromorphicField.toFun_ofHolomorphic f hf).symm

end ModularFunction
