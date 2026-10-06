/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.SchemeClosedPointPlace
public import AINTLIBDrafts.PlaceCenterStalkSquare
public import AINTLIBDrafts.ProperPlaceClosedCenter
public import AINTLIBDrafts.DVRPlaceRecovery

/-!
# Recovering an intrinsic place at the actual lift centre

For an integral smooth curve of relative dimension one, a genuine generic
lift with closed centre recovers the original place from that centre's actual
stalk DVR. The proved stalk-field square puts every literal stalk image in the
place, and native DVR-place recovery then gives equality.

Properness and finite residue yield a closed-point representation. Constants
stay independently geometric. Residue finiteness remains explicit; no
all-place finiteness, point injectivity, bijection or genus is asserted here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularPolynomialCurveTest.AINTLIB.LocalValuation

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (π : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 π]

theorem closedPointPlace_eq_of_generic_lift :
    let _ := π.functionFieldBaseAlgebra
    ∀ (v : FunctionField.Place k X.functionField)
      (l : Spec (.of v.toValuationSubring) ⟶ X),
      Spec.map (CommRingCat.ofHom (algebraMap v.toValuationSubring X.functionField)) ≫ l =
        X.fromSpecStalk (genericPoint X) →
      ∀ hx : IsClosed {l (IsLocalRing.closedPoint v.toValuationSubring)},
      closedPointPlace π (l (IsLocalRing.closedPoint v.toValuationSubring)) hx = v := by
  let _ := π.functionFieldBaseAlgebra
  dsimp only
  intro v l hgeneric hx
  let x := l (IsLocalRing.closedPoint v.toValuationSubring)
  let _ := π.stalkBaseAlgebra x
  let _ := isScalarTower_stalkBaseAlgebra π x
  have hdvr : IsDiscreteValuationRing (X.presheaf.stalk x) := by
    obtain ⟨_, h⟩ := closedPoint_stalk_isDiscreteValuationRing π x hx
    exact h
  let _ := hdvr
  change FunctionField.Place.ofDiscreteValuationRing k (X.presheaf.stalk x) X.functionField = v
  apply FunctionField.Place.ofDiscreteValuationRing_eq_of_algebraMap_mem
  intro a
  have hsquare := stalkClosedPointTo_comp_functionField l
    (CommRingCat.ofHom (algebraMap v.toValuationSubring X.functionField)) hgeneric
  have ha := congrArg (fun f : X.presheaf.stalk x →+* X.functionField ↦ f a) hsquare
  rw [← ha]
  exact ((Scheme.stalkClosedPointTo l).hom a).property

theorem exists_closedPointPlace_eq [IsProper π] :
    let _ := π.functionFieldBaseAlgebra
    ∀ (v : FunctionField.Place k X.functionField), Module.Finite k v.residueField →
      ∃ (x : X) (hx : IsClosed {x}), closedPointPlace π x hx = v := by
  let _ := π.functionFieldBaseAlgebra
  dsimp only
  intro v hfinite
  obtain ⟨l, hgeneric, _, hx⟩ := exists_properPlaceLift_closed_center π v hfinite
  exact ⟨l (IsLocalRing.closedPoint v.toValuationSubring), hx,
    closedPointPlace_eq_of_generic_lift π v l hgeneric hx⟩

example (E : EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    ∀ (v : FunctionField.Place k E.E.functionField)
      (l : Spec (.of v.toValuationSubring) ⟶ E.E),
      Spec.map (CommRingCat.ofHom (algebraMap v.toValuationSubring E.E.functionField)) ≫ l =
        E.E.fromSpecStalk (genericPoint E.E) →
      ∀ hx : IsClosed {l (IsLocalRing.closedPoint v.toValuationSubring)},
      closedPointPlace E.π (l (IsLocalRing.closedPoint v.toValuationSubring)) hx = v :=
  closedPointPlace_eq_of_generic_lift E.π

example (E : EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    ∀ (v : FunctionField.Place k E.E.functionField), Module.Finite k v.residueField →
      ∃ (x : E.E) (hx : IsClosed {x}), closedPointPlace E.π x hx = v :=
  exists_closedPointPlace_eq E.π

#print axioms closedPointPlace_eq_of_generic_lift
#print axioms exists_closedPointPlace_eq
#print axioms closedPointPlace
#print axioms stalkClosedPointTo_comp_functionField
#print axioms closedPoint_stalk_isDiscreteValuationRing
#print axioms Scheme.Hom.stalkBaseAlgebra
#print axioms isScalarTower_stalkBaseAlgebra
#print axioms FunctionField.Place.ofDiscreteValuationRing_eq_of_algebraMap_mem
#print axioms FunctionField.Place.ofDiscreteValuationRing
#print axioms exists_properPlaceLift_closed_center
#print axioms ValuationSubring.algebraMap_apply
#print axioms Scheme.Hom.functionFieldBaseAlgebra

end ModularPolynomialCurveTest.AINTLIB.LocalValuation
