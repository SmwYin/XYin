/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.ModularFunctions.ManifoldMeromorphic
import Mathlib.NumberTheory.ModularForms.Basic
import XYin.PhD.ModularFunctions.MeromorphicField
import XYin.PhD.ModularFunctions.Cusps

/-!
# Test: manifold-level meromorphy and the definition of modular functions

This isolated prototype records a bundled-class interface and checks it against the production
manifold and cusp predicates. Its namespace keeps it separate from the production bundle.

## Contents

1. `MMeromorphicAt`, `MMeromorphicNFAt`, `MMeromorphic`, `MMeromorphicNF`, `mmeromorphicOrderAt`:
   meromorphy of `f : M → ℂ` on a space charted over `ℂ`, read in the preferred chart at each
   point, in the style of `MDifferentiableAt`.
2. On `ℍ` the preferred chart is the inclusion into `ℂ` and its inverse is `ofComplex`, so
   `UpperHalfPlane.mmeromorphicNF_iff` reads
   `MMeromorphicNF f ↔ MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet`,
   the analogue of `UpperHalfPlane.mdifferentiable_iff`.
3. `OnePoint.IsExpBoundedAt c f k`: at most exponential growth at a cusp, in every weight,
   mirroring `OnePoint.IsBoundedAt`. At weight `0` it is the repository's
   `OnePoint.IsOfExponentialGrowthAt`.
4. `ModularFunction Γ`, extending `SlashInvariantForm Γ 0` exactly as `ModularForm` does, with
   `ModularFunctionClass`, the map to the meromorphic function field, and constructors from
   modular forms, from any bundled class, and from constants.
5. Sanity checks.
-/

open UpperHalfPlane Filter
open scoped Manifold MatrixGroups ModularForm Topology

noncomputable section

/-! The independent manifold predicates and the all-weight growth API are now production
modules. This remaining prototype adds a `ModularFunctionClass` interface. -/

namespace ModularFunctionPrototype

/-! ## 4. Modular functions -/

variable (Γ : Subgroup (GL (Fin 2) ℝ))

/-- Modular functions for `Γ`: weight-zero slash-invariant functions on `ℍ` which are meromorphic
in normal form and have at most exponential growth at every cusp of `Γ`. Compare `ModularForm`,
where the analytic field is `MDiff toFun` and the cusp field is `c.IsBoundedAt toFun k`. -/
structure ModularFunction extends SlashInvariantForm Γ 0 where
  meromorphicNF' : MMeromorphicNF toFun
  expBounded_at_cusps' {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsExpBoundedAt toFun 0

/-- The `SlashInvariantForm` associated to a `ModularFunction`. -/
add_decl_doc ModularFunction.toSlashInvariantForm

/-- `ModularFunctionClass F Γ` says that `F` is a type of bundled functions that extend
`SlashInvariantFormClass` by requiring meromorphy in normal form and at most exponential growth
at all cusps. -/
class ModularFunctionClass (F : Type*) (Γ : outParam (Subgroup (GL (Fin 2) ℝ)))
    [FunLike F ℍ ℂ] : Prop extends SlashInvariantFormClass F Γ 0 where
  meromorphicNF (f : F) : MMeromorphicNF (f : ℍ → ℂ)
  expBounded_at_cusps (f : F) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsExpBoundedAt (f : ℍ → ℂ) 0

variable {Γ}

namespace ModularFunction

instance funLike : FunLike (ModularFunction Γ) ℍ ℂ where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr; exact DFunLike.ext' h

instance instModularFunctionClass : ModularFunctionClass (ModularFunction Γ) Γ where
  slash_action_eq f := f.slash_action_eq'
  meromorphicNF f := f.meromorphicNF'
  expBounded_at_cusps f := f.expBounded_at_cusps'

@[simp]
theorem toSlashInvariantForm_coe (f : ModularFunction Γ) :
    (f.toSlashInvariantForm : ℍ → ℂ) = f := rfl

@[simp]
theorem coe_mk (f : SlashInvariantForm Γ 0) (h₁ h₂) : ⇑(ModularFunction.mk f h₁ h₂) = f := rfl

@[ext]
theorem ext {f g : ModularFunction Γ} (h : ∀ τ, f τ = g τ) : f = g := DFunLike.ext f g h

theorem meromorphicNF (f : ModularFunction Γ) : MMeromorphicNF f := f.meromorphicNF'

theorem meromorphicNFOn (f : ModularFunction Γ) :
    MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet :=
  mmeromorphicNF_iff.1 f.meromorphicNF'

theorem expBounded_at_cusps (f : ModularFunction Γ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsExpBoundedAt f 0 :=
  f.expBounded_at_cusps' hc

/-! ### The meromorphic function field -/

/-- The element of the meromorphic function field on `ℍ` represented by a modular function. -/
def toMeromorphicField (f : ModularFunction Γ) : MeromorphicField :=
  MeromorphicField.ofMeromorphic f f.meromorphicNFOn.meromorphicOn

/-- The canonical representative of the field element is the function itself. -/
@[simp]
theorem toFun_toMeromorphicField (f : ModularFunction Γ) :
    MeromorphicField.toFun f.toMeromorphicField = f :=
  MeromorphicField.toFun_ofMeromorphic f.meromorphicNFOn

theorem toMeromorphicField_injective : Function.Injective (toMeromorphicField (Γ := Γ)) := by
  intro f g h
  ext τ
  rw [← toFun_toMeromorphicField f, ← toFun_toMeromorphicField g, h]

/-! ### Constructors -/

/-- Any type of bundled modular functions maps to `ModularFunction Γ`. -/
def ofClass {F : Type*} [FunLike F ℍ ℂ] [ModularFunctionClass F Γ] (f : F) :
    ModularFunction Γ where
  toFun := f
  slash_action_eq' := SlashInvariantFormClass.slash_action_eq f
  meromorphicNF' := ModularFunctionClass.meromorphicNF f
  expBounded_at_cusps' := ModularFunctionClass.expBounded_at_cusps f

@[simp]
theorem coe_ofClass {F : Type*} [FunLike F ℍ ℂ] [ModularFunctionClass F Γ] (f : F) :
    ⇑(ofClass f : ModularFunction Γ) = f := rfl

/-- A modular form of weight `0` is a modular function. -/
def ofModularForm (f : ModularForm Γ 0) : ModularFunction Γ where
  toSlashInvariantForm := f.toSlashInvariantForm
  meromorphicNF' := f.holo'.mmeromorphicNF
  expBounded_at_cusps' hc := (f.bdd_at_cusps' hc).isExpBoundedAt

@[simp]
theorem coe_ofModularForm (f : ModularForm Γ 0) : ⇑(ofModularForm f) = f := rfl

/-- Constant modular functions, for groups of determinant one. -/
def const [Γ.HasDetOne] (x : ℂ) : ModularFunction Γ where
  toSlashInvariantForm := SlashInvariantForm.const x
  meromorphicNF' := mdifferentiable_const.mmeromorphicNF
  expBounded_at_cusps' _ := OnePoint.isExpBoundedAt_const x

@[simp]
theorem coe_const [Γ.HasDetOne] (x : ℂ) : ⇑(const x : ModularFunction Γ) = fun _ ↦ x := rfl

/-- Restrict a modular function to a subgroup. -/
def restrict {Γ' : Subgroup (GL (Fin 2) ℝ)} (f : ModularFunction Γ) (h : Γ' ≤ Γ) :
    ModularFunction Γ' where
  toFun := f
  slash_action_eq' γ hγ := f.slash_action_eq' γ (h hγ)
  meromorphicNF' := f.meromorphicNF'
  expBounded_at_cusps' hc := f.expBounded_at_cusps' (hc.mono h)

@[simp]
theorem coe_restrict {Γ' : Subgroup (GL (Fin 2) ℝ)} (f : ModularFunction Γ) (h : Γ' ≤ Γ) :
    ⇑(f.restrict h) = f := rfl

/-! ### The q-expansion form of the cusp condition -/

/-- For discrete `Γ` of determinant `±1`, a modular function is meromorphic at every cusp in the
q-expansion sense: after any scaling matrix, some positive period exists and the cusp function is
meromorphic at `q = 0`. -/
theorem meromorphic_at_cusps [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne]
    (f : ModularFunction Γ) {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsMeromorphicAt f :=
  (OnePoint.isOfExponentialGrowthAt_iff_isMeromorphicAt f.toSlashInvariantForm
    f.meromorphicNFOn hc).1 (f.expBounded_at_cusps hc)

end ModularFunction

/-- Modular forms of weight `0` are modular functions, as a class. -/
instance (priority := 100) ModularFormClass.toModularFunctionClass {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ 0] : ModularFunctionClass F Γ where
  toSlashInvariantFormClass := inferInstance
  meromorphicNF f := (ModularFormClass.holo f).mmeromorphicNF
  expBounded_at_cusps f := fun hc ↦ (ModularFormClass.bdd_at_cusps f hc).isExpBoundedAt

/-! ## 5. Sanity checks -/

section Checks

-- The preferred chart of `ℍ` and its inverse are the inclusion and `ofComplex`.
example (τ : ℍ) : (chartAt ℂ τ).symm = ofComplex := rfl
example (τ : ℍ) : extChartAt 𝓘(ℂ) τ τ = (τ : ℂ) := extChartAt_apply_eq_coe τ

-- Theorem B next to its `MDiff` model.
example (f : ℍ → ℂ) : MDiff f ↔ DifferentiableOn ℂ (f ∘ ofComplex) upperHalfPlaneSet :=
  mdifferentiable_iff
example (f : ℍ → ℂ) : MMeromorphicNF f ↔ MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet :=
  mmeromorphicNF_iff

-- On the model space `ℂ` the chart is the identity, so nothing new is being defined there.
example (f : ℂ → ℂ) (x : ℂ) : MMeromorphicNFAt f x ↔ MeromorphicNFAt f x := by
  simp [MMeromorphicNFAt]

-- Holomorphic functions are meromorphic in normal form; conversely when there are no poles.
example (f : ℍ → ℂ) (hf : MDiff f) : MMeromorphicNF f := hf.mmeromorphicNF
example (f : ℍ → ℂ) : MDiff f ↔ MMeromorphicNF f ∧ ∀ τ, 0 ≤ mmeromorphicOrderAt f τ :=
  mdifferentiable_iff_mmeromorphicNF

-- Weight `0` of the cusp predicate is the repository's growth condition, definitionally.
example (c : OnePoint ℝ) (f : ℍ → ℂ) : c.IsExpBoundedAt f 0 ↔ c.IsOfExponentialGrowthAt f :=
  Iff.rfl

-- Modular forms and cusp forms of weight `0` are modular functions, as elements and as a class.
example (f : ModularForm Γ 0) : ModularFunction Γ := ModularFunction.ofModularForm f
example : ModularFunctionClass (ModularForm Γ 0) Γ := inferInstance
example : ModularFunctionClass (CuspForm Γ 0) Γ := inferInstance
example (f : ModularForm Γ 0) (τ : ℍ) : ModularFunction.ofModularForm f τ = f τ := rfl
example (f : CuspForm Γ 0) : ModularFunction Γ := ModularFunction.ofClass f

-- Constants, for determinant-one groups, e.g. `𝒮ℒ`.
example (x : ℂ) : ModularFunction 𝒮ℒ := ModularFunction.const x

-- The field element has the function as its canonical representative, injectively.
example (f : ModularFunction Γ) : MeromorphicField.toFun f.toMeromorphicField = f := by simp
example : Function.Injective (ModularFunction.toMeromorphicField (Γ := Γ)) :=
  ModularFunction.toMeromorphicField_injective

-- The instances needed for the q-expansion form of the cusp condition exist for `𝒮ℒ`.
example (f : ModularFunction 𝒮ℒ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : c.IsMeromorphicAt f :=
  f.meromorphic_at_cusps hc

end Checks

end ModularFunctionPrototype

end
