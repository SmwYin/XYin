/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.SchemeClosedPointPlaceLift
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Injectivity of actual closed-point places

On an integral smooth curve of relative dimension one with separated structure
map, equal intrinsic closed-point places give the same closed point. Rewriting
the equality in a local lift predicate puts both canonical lifts over the same
literal valuation ring. Genuine valuative uniqueness and the proved centres
then imply point equality. No properness, finite-residue or genus premise is used.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularPolynomialCurveTest.AINTLIB.LocalValuation

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (π : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 π] [IsSeparated π]

theorem closedPointPlace_injective (x : X) (hx : IsClosed {x})
    (y : X) (hy : IsClosed {y}) :
    let _ := π.functionFieldBaseAlgebra
    closedPointPlace π x hx = closedPointPlace π y hy → x = y := by
  let _ := π.functionFieldBaseAlgebra
  dsimp only
  intro h
  let LiftAt (v : FunctionField.Place k X.functionField) (z : X) : Prop :=
    ∃ l : Spec (.of v.toValuationSubring) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap v.toValuationSubring X.functionField)) ≫ l =
        X.fromSpecStalk (genericPoint X) ∧
      l ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k v.toValuationSubring)) ∧
      l (IsLocalRing.closedPoint v.toValuationSubring) = z
  have hdata (z : X) (hz : IsClosed {z}) : LiftAt (closedPointPlace π z hz) z :=
    ⟨closedPointPlaceLift π z hz, closedPointPlaceLift_generic π z hz,
      closedPointPlaceLift_comp_structureMap π z hz, closedPointPlaceLift_center π z hz⟩
  have hydata : LiftAt (closedPointPlace π x hx) y := by
    rw [h]
    exact hdata y hy
  obtain ⟨lx, hlxg, hlxb, hxc⟩ := hdata x hx
  obtain ⟨ly, hlyg, hlyb, hyc⟩ := hydata
  let v := closedPointPlace π x hx
  let V := v.toValuationSubring
  let j : CommRingCat.of V ⟶ X.functionField :=
    CommRingCat.ofHom (algebraMap V X.functionField)
  let c : CommRingCat.of k ⟶ CommRingCat.of V := CommRingCat.ofHom (algebraMap k V)
  have hsq : CommSq (X.fromSpecStalk (genericPoint X)) (Spec.map j) π (Spec.map c) := by
    constructor
    change X.fromSpecStalk (genericPoint X) ≫ π = Spec.map j ≫ Spec.map c
    rw [← hlxg, Category.assoc, hlxb]
    rfl
  let S : ValuativeCommSq π :=
    { R := V
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Spec.map c
      commSq := hsq }
  let Lx : S.commSq.LiftStruct := ⟨lx, hlxg, hlxb⟩
  let Ly : S.commSq.LiftStruct := ⟨ly, hlyg, hlyb⟩
  have : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion π S
  have hl := congrArg (fun L : S.commSq.LiftStruct => L.l) (Subsingleton.elim Lx Ly)
  change lx = ly at hl
  let t : Spec (.of V) := IsLocalRing.closedPoint V
  have ht := congrArg (fun l : Spec (.of V) ⟶ X => l t) hl
  exact hxc.symm.trans (ht.trans hyc)

example (E : EllipticCurve (Spec (.of k))) (x : E.E) (hx : IsClosed {x})
    (y : E.E) (hy : IsClosed {y}) :
    let _ := E.π.functionFieldBaseAlgebra
    closedPointPlace E.π x hx = closedPointPlace E.π y hy → x = y :=
  closedPointPlace_injective E.π x hx y hy

example (W : WeierstrassCurve k) [W.IsElliptic]
    (x : (modelEllipticCurve W).E) (hx : IsClosed {x})
    (y : (modelEllipticCurve W).E) (hy : IsClosed {y}) :
    let _ := (modelEllipticCurve W).π.functionFieldBaseAlgebra
    closedPointPlace (modelEllipticCurve W).π x hx =
      closedPointPlace (modelEllipticCurve W).π y hy → x = y :=
  closedPointPlace_injective (modelEllipticCurve W).π x hx y hy

#print axioms closedPointPlace_injective
#print axioms closedPointPlaceLift
#print axioms closedPointPlaceLift_generic
#print axioms closedPointPlaceLift_comp_structureMap
#print axioms closedPointPlaceLift_center
#print axioms IsSeparated.valuativeCriterion
#print axioms ValuativeCommSq
#print axioms CommSq.LiftStruct
#print axioms FunctionField.Place.algebraValuationSubring

end ModularPolynomialCurveTest.AINTLIB.LocalValuation
