/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.ProperPlaceLift
public import AINTLIBDrafts.FiniteFieldPointClosed

/-!
# Closed centres of proper lifts with finite residue

For a separated integral scheme over a field, an actual lift of an intrinsic
place has closed centre whenever its genuine residue field is finite over the
base. The actual residue-spectrum morphism and its canonical scalar triangle
identify this centre with the closed image of a finite field-valued point.

Properness then supplies a lift with both literal triangles and closed centre.
The residue finiteness premise stays explicit. No place recovery, bijection,
normality, smoothness or genus conclusion is asserted here.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

theorem isClosed_placeLift_center (π : X ⟶ Spec (.of k)) [IsSeparated π] :
    let _ := π.functionFieldBaseAlgebra
    ∀ (v : FunctionField.Place k X.functionField), Module.Finite k v.residueField →
      ∀ (l : Spec (.of v.toValuationSubring) ⟶ X),
        l ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k v.toValuationSubring)) →
        IsClosed {l (IsLocalRing.closedPoint v.toValuationSubring)} := by
  let _ := π.functionFieldBaseAlgebra
  dsimp only
  intro v hfinite l hl
  let _ := hfinite
  let V := v.toValuationSubring
  let c : CommRingCat.of k ⟶ CommRingCat.of V :=
    CommRingCat.ofHom (algebraMap k V)
  let q : CommRingCat.of V ⟶ CommRingCat.of v.residueField :=
    CommRingCat.ofHom (IsLocalRing.residue V)
  let r : Spec (.of v.residueField) ⟶ Spec (.of V) := Spec.map q
  let e : Spec (.of v.residueField) ⟶ X := r ≫ l
  have hscalar : c ≫ q = CommRingCat.ofHom (algebraMap k v.residueField) := rfl
  have he : e ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k v.residueField)) := by
    change (Spec.map q ≫ l) ≫ π = _
    rw [Category.assoc, hl]
    exact (Spec.map_comp c q).symm.trans (congrArg Spec.map hscalar)
  let x : Spec (.of v.residueField) := IsLocalRing.closedPoint v.residueField
  have hpoint : r x = IsLocalRing.closedPoint V :=
    IsLocalRing.PrimeSpectrum.comap_residue V x
  have hcenter : e x = l (IsLocalRing.closedPoint V) := by
    change l (r x) = _
    rw [hpoint]
  have hclosed := isClosed_image_of_finite_field π e he x
  rw [hcenter] at hclosed
  exact hclosed

theorem exists_properPlaceLift_closed_center (π : X ⟶ Spec (.of k)) [IsProper π] :
    let _ := π.functionFieldBaseAlgebra
    ∀ (v : FunctionField.Place k X.functionField), Module.Finite k v.residueField →
      ∃ l : Spec (.of v.toValuationSubring) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap v.toValuationSubring X.functionField)) ≫ l =
          X.fromSpecStalk (genericPoint X) ∧
        l ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k v.toValuationSubring)) ∧
        IsClosed {l (IsLocalRing.closedPoint v.toValuationSubring)} := by
  let _ := π.functionFieldBaseAlgebra
  dsimp only
  intro v hfinite
  obtain ⟨l, hgeneric, hbase⟩ := exists_properPlaceLift π v
  exact ⟨l, hgeneric, hbase, isClosed_placeLift_center π v hfinite l hbase⟩

example (π : X ⟶ Spec (.of k)) [IsSeparated π] :
    let _ := π.functionFieldBaseAlgebra
    ∀ (v : FunctionField.Place k X.functionField), Module.Finite k v.residueField →
      ∀ (l : Spec (.of v.toValuationSubring) ⟶ X),
        l ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k v.toValuationSubring)) →
        IsClosed {l (IsLocalRing.closedPoint v.toValuationSubring)} :=
  isClosed_placeLift_center π

example (E : ModularCurves.EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    ∀ (v : FunctionField.Place k E.E.functionField), Module.Finite k v.residueField →
      ∃ l : Spec (.of v.toValuationSubring) ⟶ E.E,
        Spec.map (CommRingCat.ofHom (algebraMap v.toValuationSubring E.E.functionField)) ≫ l =
          E.E.fromSpecStalk (genericPoint E.E) ∧
        l ≫ E.π = Spec.map (CommRingCat.ofHom (algebraMap k v.toValuationSubring)) ∧
        IsClosed {l (IsLocalRing.closedPoint v.toValuationSubring)} :=
  exists_properPlaceLift_closed_center E.π

#print axioms isClosed_placeLift_center
#print axioms exists_properPlaceLift_closed_center
#print axioms isClosed_image_of_finite_field
#print axioms exists_properPlaceLift
#print axioms IsLocalRing.PrimeSpectrum.comap_residue
#print axioms IsLocalRing.ResidueField.algebraMap_eq
#print axioms FunctionField.Place.algebraValuationSubring
#print axioms Spec.map_comp
#print axioms Scheme.Hom.comp_apply

end AlgebraicGeometry
