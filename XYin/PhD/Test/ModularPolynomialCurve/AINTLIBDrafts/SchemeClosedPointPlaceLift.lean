/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.SchemeClosedPointPlace
public import AINTLIBDrafts.DVRPlaceAlgEquiv
public import AINTLIBDrafts.StalkPointOverBase

/-!
# Canonical lift of an actual closed-point place

For an integral smooth curve of relative dimension one, its closed-point
stalk is canonically isomorphic over the original constants to the actual
place valuation ring. The positive ring equivalence defines a spectrum lift
through the native stalk point. Its generic triangle, actual centre and
geometric base triangle are proved, without any assumed centre or lift square.
No properness, residue-finiteness, injectivity or place-bijection premise is used.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularPolynomialCurveTest.AINTLIB.LocalValuation

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (π : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 π]

noncomputable def closedPointStalkAlgEquiv (x : X) (hx : IsClosed {x}) :
    let _ := π.functionFieldBaseAlgebra
    let _ := π.stalkBaseAlgebra x
    X.presheaf.stalk x ≃ₐ[k] (closedPointPlace π x hx).toValuationSubring := by
  let _ := π.functionFieldBaseAlgebra
  let _ := π.stalkBaseAlgebra x
  let _ := isScalarTower_stalkBaseAlgebra π x
  have hdvr : IsDiscreteValuationRing (X.presheaf.stalk x) := by
    obtain ⟨_, h⟩ := closedPoint_stalk_isDiscreteValuationRing π x hx
    exact h
  let _ := hdvr
  exact FunctionField.Place.ofDiscreteValuationRingAlgEquiv
    k (X.presheaf.stalk x) X.functionField

noncomputable def closedPointPlaceLift (x : X) (hx : IsClosed {x}) :
    let _ := π.functionFieldBaseAlgebra
    Spec (.of (closedPointPlace π x hx).toValuationSubring) ⟶ X := by
  let _ := π.functionFieldBaseAlgebra
  let _ := π.stalkBaseAlgebra x
  exact Spec.map (CommRingCat.ofHom (closedPointStalkAlgEquiv π x hx).toRingHom) ≫
    X.fromSpecStalk x

theorem closedPointPlaceLift_generic (x : X) (hx : IsClosed {x}) :
    let _ := π.functionFieldBaseAlgebra
    Spec.map (CommRingCat.ofHom
      (algebraMap (closedPointPlace π x hx).toValuationSubring X.functionField)) ≫
      closedPointPlaceLift π x hx = X.fromSpecStalk (genericPoint X) := by
  let _ := π.functionFieldBaseAlgebra
  let _ := π.stalkBaseAlgebra x
  let e := closedPointStalkAlgEquiv π x hx
  have hs : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom
      (algebraMap (closedPointPlace π x hx).toValuationSubring X.functionField) =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
    ext a
    rfl
  change Spec.map _ ≫ (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk x) = _
  rw [← Category.assoc, ← Spec.map_comp, hs]
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk
    ((genericPoint_spec X).specializes trivial)

theorem closedPointPlaceLift_center (x : X) (hx : IsClosed {x}) :
    let _ := π.functionFieldBaseAlgebra
    closedPointPlaceLift π x hx
      (IsLocalRing.closedPoint (closedPointPlace π x hx).toValuationSubring) = x := by
  let _ := π.functionFieldBaseAlgebra
  let _ := π.stalkBaseAlgebra x
  let e := closedPointStalkAlgEquiv π x hx
  let a : CommRingCat.of (X.presheaf.stalk x) ⟶
      CommRingCat.of (closedPointPlace π x hx).toValuationSubring :=
    CommRingCat.ofHom e.toRingHom
  have : IsLocalHom a.hom := IsLocalHom.of_surjective _ e.surjective
  let c : Spec (.of (closedPointPlace π x hx).toValuationSubring) :=
    IsLocalRing.closedPoint (closedPointPlace π x hx).toValuationSubring
  let d : Spec (.of (X.presheaf.stalk x)) := IsLocalRing.closedPoint (X.presheaf.stalk x)
  have hc : Spec.map a c = d := Spec_closedPoint
  change X.fromSpecStalk x (Spec.map a c) = x
  exact (congrArg (X.fromSpecStalk x) hc).trans
    (Scheme.fromSpecStalk_closedPoint (X := X) (x := x))

theorem closedPointPlaceLift_comp_structureMap (x : X) (hx : IsClosed {x}) :
    let _ := π.functionFieldBaseAlgebra
    closedPointPlaceLift π x hx ≫ π = Spec.map (CommRingCat.ofHom
      (algebraMap k (closedPointPlace π x hx).toValuationSubring)) := by
  let _ := π.functionFieldBaseAlgebra
  let _ := π.stalkBaseAlgebra x
  let e := closedPointStalkAlgEquiv π x hx
  have hs : CommRingCat.ofHom (algebraMap k (X.presheaf.stalk x)) ≫
      CommRingCat.ofHom e.toRingHom = CommRingCat.ofHom
      (algebraMap k (closedPointPlace π x hx).toValuationSubring) := by
    ext c
    exact congrArg
      (fun z : (closedPointPlace π x hx).toValuationSubring => (z : X.functionField))
      (e.commutes c)
  change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk x) ≫ π = _
  rw [Category.assoc, fromSpecStalk_comp_structureMap]
  exact (Spec.map_comp _ _).symm.trans (congrArg Spec.map hs)

example (E : EllipticCurve (Spec (.of k))) (x : E.E) (hx : IsClosed {x}) :
    let _ := E.π.functionFieldBaseAlgebra
    Spec.map (CommRingCat.ofHom
      (algebraMap (closedPointPlace E.π x hx).toValuationSubring E.E.functionField)) ≫
      closedPointPlaceLift E.π x hx = E.E.fromSpecStalk (genericPoint E.E) :=
  closedPointPlaceLift_generic E.π x hx

example (E : EllipticCurve (Spec (.of k))) (x : E.E) (hx : IsClosed {x}) :
    let _ := E.π.functionFieldBaseAlgebra
    closedPointPlaceLift E.π x hx
      (IsLocalRing.closedPoint (closedPointPlace E.π x hx).toValuationSubring) = x :=
  closedPointPlaceLift_center E.π x hx

#print axioms closedPointStalkAlgEquiv
#print axioms closedPointPlaceLift
#print axioms closedPointPlaceLift_generic
#print axioms closedPointPlaceLift_center
#print axioms closedPointPlaceLift_comp_structureMap
#print axioms FunctionField.Place.ofDiscreteValuationRingAlgEquiv
#print axioms closedPoint_stalk_isDiscreteValuationRing
#print axioms isScalarTower_stalkBaseAlgebra
#print axioms Scheme.SpecMap_stalkSpecializes_fromSpecStalk
#print axioms Scheme.fromSpecStalk_closedPoint
#print axioms Spec_closedPoint
#print axioms IsLocalHom.of_surjective
#print axioms fromSpecStalk_comp_structureMap
#print axioms AlgEquiv.commutes

end ModularPolynomialCurveTest.AINTLIB.LocalValuation
