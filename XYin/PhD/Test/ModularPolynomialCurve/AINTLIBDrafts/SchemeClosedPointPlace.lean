/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.ClosedPointStalkDVR
public import AINTLIBDrafts.StalkBaseAlgebra
public import AINTLIBDrafts.DVRPlace
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientRelativeDimension
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientIntegral

/-!
# Actual smooth-curve closed points as intrinsic RR places

A closed point of an integral smooth curve over any field defines a place
of its literal function field, with independently geometric base constants.
The actual stalk DVR, germ-defined stalk scalars and true fraction-field
tower supply the constructor. Membership is precisely the image of the
canonical stalk-to-function-field map.

The native elliptic curve and actual étale-subgroup quotient examples use
proved integral and relative-dimension-one inputs. No additional DVR,
constant-field, normality, genus, place bijection or model premise is added.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularPolynomialCurveTest.AINTLIB.LocalValuation

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (π : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 π]

noncomputable def closedPointPlace (x : X) (hx : IsClosed {x}) :
    let _ := π.functionFieldBaseAlgebra
    FunctionField.Place k X.functionField := by
  let _ := π.functionFieldBaseAlgebra
  let _ := π.stalkBaseAlgebra x
  let _ := isScalarTower_stalkBaseAlgebra π x
  have hdvr : IsDiscreteValuationRing (X.presheaf.stalk x) := by
    obtain ⟨_, h⟩ := closedPoint_stalk_isDiscreteValuationRing π x hx
    exact h
  let _ := hdvr
  exact FunctionField.Place.ofDiscreteValuationRing k (X.presheaf.stalk x) X.functionField

theorem mem_closedPointPlace_iff (x : X) (hx : IsClosed {x}) (z : X.functionField) :
    let _ := π.functionFieldBaseAlgebra
    z ∈ closedPointPlace π x hx ↔
      ∃ a : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField a = z := by
  let _ := π.functionFieldBaseAlgebra
  let _ := π.stalkBaseAlgebra x
  let _ := isScalarTower_stalkBaseAlgebra π x
  have hdvr : IsDiscreteValuationRing (X.presheaf.stalk x) := by
    obtain ⟨_, h⟩ := closedPoint_stalk_isDiscreteValuationRing π x hx
    exact h
  let _ := hdvr
  exact FunctionField.Place.mem_ofDiscreteValuationRing_iff
    k (X.presheaf.stalk x) X.functionField z

example (E : EllipticCurve (Spec (.of k))) (y : E.E) (hy : IsClosed {y})
    (a : E.E.presheaf.stalk y) :
    let _ := E.π.functionFieldBaseAlgebra
    algebraMap (E.E.presheaf.stalk y) E.E.functionField a ∈ closedPointPlace E.π y hy := by
  let _ := E.π.functionFieldBaseAlgebra
  exact (mem_closedPointPlace_iff E.π y hy _).mpr ⟨a, rfl⟩

example {E : EllipticCurve (Spec (.of k))} (G : E.FiniteLocallyFreeSubgroup)
    [Etale G.π] (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)
    (y : G.gluedQuotient N hkill) (hy : IsClosed {y}) (c : k) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
      G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    (G.gluedQuotientS N hkill).functionFieldConstants c ∈
      closedPointPlace (G.gluedQuotientS N hkill) y hy := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
    G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  exact (closedPointPlace (G.gluedQuotientS N hkill) y hy).triv_on_k c

#print axioms closedPointPlace
#print axioms mem_closedPointPlace_iff
#print axioms closedPoint_stalk_isDiscreteValuationRing
#print axioms Scheme.Hom.stalkBaseAlgebra
#print axioms isScalarTower_stalkBaseAlgebra
#print axioms FunctionField.Place.ofDiscreteValuationRing
#print axioms FunctionField.Place.mem_ofDiscreteValuationRing_iff
#print axioms stalkFunctionFieldAlgebra
#print axioms Scheme.Hom.functionFieldBaseAlgebra
#print axioms EllipticCurve.FiniteLocallyFreeSubgroup.gluedQuotient_isIntegral
#print axioms EllipticCurve.FiniteLocallyFreeSubgroup.gluedQuotientS_smoothOfRelativeDimension_one

end ModularPolynomialCurveTest.AINTLIB.LocalValuation
