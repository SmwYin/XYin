/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.SchemeClosedPointPlace
public import AINTLIBDrafts.StalkFunctionFieldSquare
public import AINTLIBDrafts.DVRPlaceLocalUnramifiedValuation
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Actual closed-point place valuations under an unramified scheme map

For integral smooth curves of relative dimension one over a field, a dominant
formally unramified locally finite-type map compares the intrinsic valuations
at a closed source point and its closed image. Both structure maps specify
their constants independently; this pointwise valuation identity does not
require an over-base compatibility equation.

The actual stalk map and native function-field map determine the coefficient
algebras. Their proved germ square supplies the fraction-field scalar tower,
and actual closed-point DVRs supply the generic DVR valuation comparison.
The identity and étale examples verify the same literal maps. Image closedness
is explicit here; actual finite-quotient specialization is a separate step.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularPolynomialCurveTest.AINTLIB.LocalValuation

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (πX : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 πX]
  (πY : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 πY]

/-- Actual closed-point places compare through the literal stalk and function-field maps. -/
theorem closedPointPlace_valuation_functionFieldMap (f : X ⟶ Y) [IsDominant f]
    [FormallyUnramified f] [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed {x}) (hfx : IsClosed {f x}) (z : Y.functionField) :
    let _ := πY.functionFieldBaseAlgebra
    let _ := πX.functionFieldBaseAlgebra
    (closedPointPlace πY (f x) hfx).valuation z =
      (closedPointPlace πX x hx).valuation (f.functionFieldMap.hom z) := by
  let _ := πY.functionFieldBaseAlgebra
  let _ := πX.functionFieldBaseAlgebra
  let _ := πY.stalkBaseAlgebra (f x)
  let _ := πX.stalkBaseAlgebra x
  let _ := isScalarTower_stalkBaseAlgebra πY (f x)
  let _ := isScalarTower_stalkBaseAlgebra πX x
  have : IsDiscreteValuationRing (Y.presheaf.stalk (f x)) := by
    obtain ⟨_, h⟩ := closedPoint_stalk_isDiscreteValuationRing πY (f x) hfx
    exact h
  have : IsDiscreteValuationRing (X.presheaf.stalk x) := by
    obtain ⟨_, h⟩ := closedPoint_stalk_isDiscreteValuationRing πX x hx
    exact h
  let _ := functionFieldAlgebra f
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk (f x)) X.functionField :=
    ((algebraMap (X.presheaf.stalk x) X.functionField).comp (f.stalkMap x).hom).toAlgebra
  have : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rfl
  have : IsScalarTower (Y.presheaf.stalk (f x)) Y.functionField X.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    exact (congrArg (fun g : Y.presheaf.stalk (f x) →+* X.functionField ↦ g a)
      (functionFieldMap_comp_stalkFunctionFieldAlgebra f x)).symm
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    f.toLRSHom.prop x
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f x
  change (FunctionField.Place.ofDiscreteValuationRing k
      (Y.presheaf.stalk (f x)) Y.functionField).valuation z =
    (FunctionField.Place.ofDiscreteValuationRing k
      (X.presheaf.stalk x) X.functionField).valuation (f.functionFieldMap.hom z)
  exact FunctionField.Place.ofDiscreteValuationRing_valuation_algebraMap_of_formallyUnramified
    k (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) Y.functionField X.functionField z

example (x : X) (hx : IsClosed {x}) (z : X.functionField) :
    let _ := πX.functionFieldBaseAlgebra
    (closedPointPlace πX x hx).valuation z =
      (closedPointPlace πX x hx).valuation ((𝟙 X : X ⟶ X).functionFieldMap.hom z) :=
  closedPointPlace_valuation_functionFieldMap πX πX (𝟙 X) x hx hx z

example (f : X ⟶ Y) [IsDominant f] [Etale f]
    (x : X) (hx : IsClosed {x}) (hfx : IsClosed {f x}) (z : Y.functionField) :
    let _ := πY.functionFieldBaseAlgebra
    let _ := πX.functionFieldBaseAlgebra
    (closedPointPlace πY (f x) hfx).valuation z =
      (closedPointPlace πX x hx).valuation (f.functionFieldMap.hom z) :=
  closedPointPlace_valuation_functionFieldMap πX πY f x hx hfx z

#print axioms closedPointPlace_valuation_functionFieldMap
#print axioms closedPointPlace
#print axioms Scheme.Hom.stalkBaseAlgebra
#print axioms isScalarTower_stalkBaseAlgebra
#print axioms closedPoint_stalk_isDiscreteValuationRing
#print axioms functionFieldMap_comp_stalkFunctionFieldAlgebra
#print axioms functionFieldAlgebra
#print axioms stalkFunctionFieldAlgebra
#print axioms LocallyOfFiniteType.stalkMap
#print axioms FormallyUnramified.stalkMap
#print axioms RingHom.essFiniteType_algebraMap
#print axioms RingHom.formallyUnramified_algebraMap
#print axioms FunctionField.Place.ofDiscreteValuationRing_valuation_algebraMap_of_formallyUnramified
#print axioms IsScalarTower.of_algebraMap_eq

end ModularPolynomialCurveTest.AINTLIB.LocalValuation
