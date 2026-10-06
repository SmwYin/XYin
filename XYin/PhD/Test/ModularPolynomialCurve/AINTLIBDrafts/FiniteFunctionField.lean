/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.ForMathlib.DominantFunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite native function-field pullbacks

A finite dominant morphism of integral schemes induces a finite module
extension for the literal `functionFieldAlgebra`. The proof selects a
nonempty affine target open, uses the finite section-ring map on its
preimage, and applies the checked fraction-ring base-change equivalence.
The native germ square supplies the scalar tower on both function fields.

`functionFieldMap_finite` packages the result as finiteness of the actual
function-field ring homomorphism. The API needs no Noetherian, flatness,
relative-dimension, genus, or elliptic-curve-model hypotheses. The examples
check the actual algebra module on an identity map, a finite affine map,
and the identity ring-hom API. Quotient-specific applications are separate.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A finite dominant map of integral schemes induces a finite native function-field algebra. -/
theorem moduleFinite_functionField (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] :
    let _ := functionFieldAlgebra f
    Module.Finite Y.functionField X.functionField := by
  classical
  let : Algebra Y.functionField X.functionField := functionFieldAlgebra f
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (x := genericPoint Y) (U := ⊤) (by trivial)
  have : Nonempty U := ⟨⟨genericPoint Y, hyU⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨genericPoint X, genericPoint_mem_preimage f U⟩⟩
  let R : Type u := ↑Γ(Y, U)
  let B : Type u := ↑Γ(X, f ⁻¹ᵁ U)
  let : Algebra R B := (f.app U).hom.toAlgebra
  let : Algebra R X.functionField :=
    ((X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom).toAlgebra
  have : IsScalarTower R B X.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R Y.functionField X.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change X.germToFunctionField (f ⁻¹ᵁ U) (f.app U r) =
      f.functionFieldMap (Y.germToFunctionField U r)
    exact (congrArg (fun m : Γ(Y, U) ⟶ X.functionField ↦ m r)
      (functionFieldMap_comp_germToFunctionField f U)).symm
  have : IsFractionRing R Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  have : IsFractionRing B X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ U) (hU.preimage f)
  have : Module.Finite R B := f.finite_app U hU
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  have : FaithfulSMul R B :=
    (faithfulSMul_iff_algebraMap_injective R B).mpr (f.app_injective U)
  have : Algebra.IsAlgebraic R B := Algebra.IsAlgebraic.of_finite R B
  exact Module.Finite.equiv
    (Algebra.IsAlgebraic.isBaseChange_of_isFractionRing R B
      Y.functionField X.functionField).equiv

/-- The literal dominant function-field pullback is a finite ring homomorphism. -/
theorem functionFieldMap_finite (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] : f.functionFieldMap.hom.Finite :=
  moduleFinite_functionField f

example (X : Scheme.{u}) [IsIntegral X] :
    let alg : Algebra X.functionField X.functionField := functionFieldAlgebra (𝟙 X)
    @Module.Finite X.functionField X.functionField _ _ alg.toModule :=
  moduleFinite_functionField (X := X) (Y := X) (𝟙 X)

example (R B : CommRingCat.{u}) [IsDomain R] [IsDomain B] (φ : R ⟶ B)
    (hfin : φ.hom.Finite) [IsDominant (Spec.map φ)] :
    let _ : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).mpr hfin
    let _ := functionFieldAlgebra (Spec.map φ)
    Module.Finite (Spec R).functionField (Spec B).functionField := by
  have : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).mpr hfin
  exact moduleFinite_functionField (Spec.map φ)

example (X : Scheme.{u}) [IsIntegral X] :
    (𝟙 X : X ⟶ X).functionFieldMap.hom.Finite :=
  functionFieldMap_finite (𝟙 X)

#print axioms moduleFinite_functionField
#print axioms functionFieldMap_finite
#print axioms functionFieldAlgebra
#print axioms functionFieldMap_comp_germToFunctionField
#print axioms functionField_isFractionRing_of_isAffineOpen
#print axioms IsFinite.finite_app
#print axioms IsAffineOpen.preimage
#print axioms IsSchemeTheoreticallyDominant.of_isDominant
#print axioms Scheme.Hom.app_injective
#print axioms IsFinite.SpecMap_iff

end AlgebraicGeometry

#print axioms Algebra.IsAlgebraic.isBaseChange_of_isFractionRing
#print axioms Algebra.IsAlgebraic.of_finite
#print axioms Module.Finite.base_change
#print axioms Module.Finite.equiv
#print axioms IsBaseChange.equiv
#print axioms IsScalarTower.of_algebraMap_eq
