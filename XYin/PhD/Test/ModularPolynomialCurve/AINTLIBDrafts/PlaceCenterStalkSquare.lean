/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.GenericPointOverBase
public import ModularCurves.Vendored.RiemannRoch.Place

/-!
# Actual centre-stalk square of a generic lift

For an irreducible scheme and an actual morphism from a local ring spectrum,
a genuine generic-lift equation forces its centre-stalk map to commute with
the canonical generic-stalk algebra map. Spec faithfulness and the native
monomorphism from a stalk spectrum prove the square; no ring square is assumed.

This statement needs neither properness, closedness nor DVR hypotheses.
The generic-stalk client has the same irreducibility assumption. The intrinsic
place client additionally requires integrality to obtain a genuine field and
keeps its constants independently defined through the structure map.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IrreducibleSpace X]

theorem stalkClosedPointTo_comp_functionField
    {R : CommRingCat.{u}} [IsLocalRing R]
    (l : Spec R ⟶ X) (j : R ⟶ X.functionField)
    (hgeneric : Spec.map j ≫ l = X.fromSpecStalk (genericPoint X)) :
    j.hom.comp (Scheme.stalkClosedPointTo l).hom =
      algebraMap (X.presheaf.stalk (l (IsLocalRing.closedPoint R))) X.functionField := by
  let c := l (IsLocalRing.closedPoint R)
  let hspec : genericPoint X ⤳ c := (genericPoint_spec X).specializes trivial
  let δ := X.presheaf.stalkSpecializes hspec
  change ((Scheme.stalkClosedPointTo l) ≫ j).hom = δ.hom
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk c)).mp
  calc
    Spec.map ((Scheme.stalkClosedPointTo l) ≫ j) ≫ X.fromSpecStalk c =
        Spec.map j ≫ (Spec.map (Scheme.stalkClosedPointTo l) ≫ X.fromSpecStalk c) := by
      rw [Spec.map_comp, Category.assoc]
    _ = Spec.map j ≫ l := by rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    _ = X.fromSpecStalk (genericPoint X) := hgeneric
    _ = Spec.map δ ≫ X.fromSpecStalk c :=
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hspec).symm

example (x : X) :
    (algebraMap (X.presheaf.stalk x) X.functionField).comp
      (Scheme.stalkClosedPointTo (X.fromSpecStalk x)).hom =
    algebraMap (X.presheaf.stalk
      ((X.fromSpecStalk x) (IsLocalRing.closedPoint (X.presheaf.stalk x)))) X.functionField := by
  apply stalkClosedPointTo_comp_functionField
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk
    ((genericPoint_spec X).specializes trivial)

example [IsIntegral X] {k : Type u} [Field k] (π : X ⟶ Spec (.of k)) :
    let _ := π.functionFieldBaseAlgebra
    ∀ (v : FunctionField.Place k X.functionField)
      (l : Spec (.of v.toValuationSubring) ⟶ X),
      Spec.map (CommRingCat.ofHom (algebraMap v.toValuationSubring X.functionField)) ≫ l =
        X.fromSpecStalk (genericPoint X) →
      (algebraMap v.toValuationSubring X.functionField).comp (Scheme.stalkClosedPointTo l).hom =
      algebraMap (X.presheaf.stalk
        (l (IsLocalRing.closedPoint v.toValuationSubring))) X.functionField := by
  let _ := π.functionFieldBaseAlgebra
  dsimp only
  intro v l hgeneric
  exact stalkClosedPointTo_comp_functionField l _ hgeneric

#print axioms stalkClosedPointTo_comp_functionField
#print axioms Scheme.stalkClosedPointTo
#print axioms Scheme.Spec_stalkClosedPointTo_fromSpecStalk
#print axioms Scheme.SpecMap_stalkSpecializes_fromSpecStalk
#print axioms Scheme.stalkClosedPointTo_fromSpecStalk
#print axioms Spec.faithful
#print axioms stalkFunctionFieldAlgebra
#print axioms CategoryTheory.cancel_mono

end AlgebraicGeometry
