/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.ForMathlib.DominantFunctionField
public import ModularCurves.ForMathlib.FinrankComp
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Finite flat scheme rank and the actual function-field degree

A finite flat dominant morphism of integral schemes has fibre rank equal
at every target point to the degree of its literal native function-field
pullback. A nonempty affine neighbourhood of that point supplies two
fraction fields. The native germ square establishes the scalar tower, and
the actual affine pullback compares scheme rank with the fraction-field
rank theorem. No Noetherian, genus, or elliptic-model hypothesis is needed.

The examples check the actual identity-induced module and a finite flat
map of affine spectra. Quotient-specific ranks and genus are separate.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Finite flat scheme rank equals the degree of the actual function-field pullback. -/
theorem Scheme.Hom.finrank_eq_functionField_finrank (f : X ⟶ Y)
    [IsFinite f] [Flat f] [IsDominant f] [IsIntegral X] [IsIntegral Y] (y : Y) :
    let _ := functionFieldAlgebra f
    f.finrank y = Module.finrank Y.functionField X.functionField := by
  classical
  let : Algebra Y.functionField X.functionField := functionFieldAlgebra f
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (x := y) (U := ⊤) (by trivial)
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
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
  have hflat : (f.app U).hom.Flat := by
    rw [f.app_eq_appLE]
    exact f.flat_appLE hU (hU.preimage f) le_rfl
  have : Module.Flat R B := hflat
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  have : FaithfulSMul R B :=
    (faithfulSMul_iff_algebraMap_injective R B).mpr (f.app_injective U)
  have : IsAffine U.toScheme := hU
  have : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  have : IsIso U.toSpecΓ := by
    change IsIso hU.isoSpec.hom
    infer_instance
  have : IsIso (f ⁻¹ᵁ U).toSpecΓ := by
    change IsIso (hU.preimage f).isoSpec.hom
    infer_instance
  have : IsFinite (Spec.map (f.app U)) := (IsFinite.SpecMap_iff _).mpr (f.finite_app U hU)
  have : Flat (Spec.map (f.app U)) := Flat.SpecMap_iff.mpr hflat
  have hsquare : IsPullback (f ⁻¹ᵁ U).toSpecΓ (f ∣_ U)
      (Spec.map (f.app U)) U.toSpecΓ :=
    .of_horiz_isIso ⟨Scheme.Opens.toSpecΓ_naturality f U⟩
  let v : U := ⟨y, hyU⟩
  have hrank := Scheme.Hom.finrank_of_isPullback _ _ _ _ hsquare v
  have hfield := ModularCurves.finrank_SpecMap_eq_functionField_finrank
    R B Y.functionField X.functionField (U.toSpecΓ v)
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap R B)) = Spec.map (f.app U) := rfl
  rw [hmap] at hfield
  calc
    f.finrank y = (f ∣_ U).finrank v :=
      (Scheme.Hom.finrank_morphismRestrict f U v).symm
    _ = (Spec.map (f.app U)).finrank (U.toSpecΓ v) := hrank
    _ = Module.finrank Y.functionField X.functionField := hfield

example (X : Scheme.{u}) [IsIntegral X] (x : X) :
    let alg : Algebra X.functionField X.functionField := functionFieldAlgebra (𝟙 X)
    (𝟙 X : X ⟶ X).finrank x =
      @Module.finrank X.functionField X.functionField _ _ alg.toModule :=
  Scheme.Hom.finrank_eq_functionField_finrank (𝟙 X) x

example (R B : CommRingCat.{u}) [IsDomain R] [IsDomain B] (φ : R ⟶ B)
    (hfin : φ.hom.Finite) (hflat : φ.hom.Flat) [IsDominant (Spec.map φ)] (p : Spec R) :
    let _ : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).mpr hfin
    let _ : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hflat
    let _ := functionFieldAlgebra (Spec.map φ)
    (Spec.map φ).finrank p = Module.finrank (Spec R).functionField (Spec B).functionField := by
  have : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).mpr hfin
  have : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hflat
  exact Scheme.Hom.finrank_eq_functionField_finrank (Spec.map φ) p

#print axioms Scheme.Hom.finrank_eq_functionField_finrank
#print axioms functionFieldMap_comp_germToFunctionField
#print axioms functionField_isFractionRing_of_isAffineOpen
#print axioms Scheme.Hom.finrank_of_isPullback
#print axioms Scheme.Hom.finrank_morphismRestrict
#print axioms ModularCurves.finrank_SpecMap_eq_functionField_finrank
#print axioms Scheme.Opens.toSpecΓ_naturality
#print axioms IsFinite.finite_app
#print axioms Scheme.Hom.flat_appLE
#print axioms Scheme.Hom.app_injective

end AlgebraicGeometry
