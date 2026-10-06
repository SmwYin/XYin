/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.GenericPointOverBase
public import ModularCurves.Vendored.RiemannRoch.Place
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Proper extension of an intrinsic place

For an integral scheme proper over a field, every intrinsic place admits a
morphism from its actual valuation spectrum extending the canonical generic
point. Both triangles are stated with the literal geometric constant algebra,
independently defined through the structure map and generic germ.

The proof uses the actual proper valuative criterion. No finite residue,
closed-centre, smoothness, genus or place-bijection premise is introduced.
The generic and native elliptic-curve examples exercise both interfaces.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

theorem exists_properPlaceLift (π : X ⟶ Spec (.of k)) [IsProper π] :
    let _ := π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k X.functionField,
      ∃ l : Spec (.of v.toValuationSubring) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap v.toValuationSubring X.functionField)) ≫ l =
          X.fromSpecStalk (genericPoint X) ∧
        l ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k v.toValuationSubring)) := by
  let _ := π.functionFieldBaseAlgebra
  dsimp only
  intro v
  let V := v.toValuationSubring
  let j : CommRingCat.of V ⟶ X.functionField :=
    CommRingCat.ofHom (algebraMap V X.functionField)
  let c : CommRingCat.of k ⟶ CommRingCat.of V :=
    CommRingCat.ofHom (algebraMap k V)
  have hscalar : c ≫ j = CommRingCat.ofHom π.functionFieldConstants := rfl
  have hcomp : Spec.map j ≫ Spec.map c =
      Spec.map (CommRingCat.ofHom π.functionFieldConstants) := by
    exact (Spec.map_comp c j).symm.trans (congrArg Spec.map hscalar)
  have hsq : CommSq (X.fromSpecStalk (genericPoint X))
      (Spec.map (CommRingCat.ofHom (algebraMap V X.functionField))) π
      (Spec.map (CommRingCat.ofHom (algebraMap k V))) := by
    constructor
    change X.fromSpecStalk (genericPoint X) ≫ π = Spec.map j ≫ Spec.map c
    exact (fromSpecFunctionField_comp_structureMap π).trans hcomp.symm
  let S : ValuativeCommSq π :=
    { R := V
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap k V))
      commSq := hsq }
  have hval : ValuativeCriterion π := by
    have hproper : IsProper π := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hproper
    exact hproper.1.1.1
  obtain ⟨l, hl₁, hl₂⟩ := ((ValuativeCriterion.existence hval) S).exists_lift
  exact ⟨l, hl₁, hl₂⟩

example (π : X ⟶ Spec (.of k)) [IsProper π] :
    let _ := π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k X.functionField,
      ∃ l : Spec (.of v.toValuationSubring) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap v.toValuationSubring X.functionField)) ≫ l =
          X.fromSpecStalk (genericPoint X) := by
  let _ := π.functionFieldBaseAlgebra
  dsimp only
  intro v
  obtain ⟨l, hgeneric, _⟩ := exists_properPlaceLift π v
  exact ⟨l, hgeneric⟩

example (E : ModularCurves.EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField,
      ∃ l : Spec (.of v.toValuationSubring) ⟶ E.E,
        Spec.map (CommRingCat.ofHom (algebraMap v.toValuationSubring E.E.functionField)) ≫ l =
          E.E.fromSpecStalk (genericPoint E.E) ∧
        l ≫ E.π = Spec.map (CommRingCat.ofHom (algebraMap k v.toValuationSubring)) :=
  exists_properPlaceLift E.π

#print axioms exists_properPlaceLift
#print axioms fromSpecFunctionField_comp_structureMap
#print axioms IsProper.eq_valuativeCriterion
#print axioms ValuativeCriterion.existence
#print axioms CategoryTheory.CommSq.HasLift.exists_lift
#print axioms FunctionField.Place.algebraValuationSubring
#print axioms ValuationSubring.algebraMap_apply
#print axioms ValuativeCommSq

end AlgebraicGeometry
