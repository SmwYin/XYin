/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.NativeCoordinateFractionField
public import AINTLIBDrafts.FunctionFieldBaseAlgebra
public import ModularCurves.Vendored.RiemannRoch.EllipticCurve.Instances

/-!
# Polynomial scalars on the actual native function field

The actual chosen-model coordinate embedding gives polynomial scalars on a
native elliptic curve's function field over any field. The coordinate tower
uses the existing Weierstrass constructor. The base tower proves compatibility
with the independent geometric `E.π.functionFieldBaseAlgebra`.

The two examples check an actual model and its constant-polynomial map.
No global instance, characteristic or algebraic-closure restriction is added.
Rational-function scalars, a FunctionField instance, separability, full
constants, genus, and a quotient model are outside this module's scope.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open scoped Polynomial

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

/-- Polynomial scalars come from the actual coordinate-ring embedding. -/
@[reducible] noncomputable def nativeFieldPolynomialAlgebra
    (E : EllipticCurve (Spec (.of k))) : Algebra k[X] E.E.functionField :=
  let _ := nativeFieldCoordinateAlgebra E
  (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.algebraPolynomial E.E.functionField

/-- The native polynomial algebra factors through the chosen coordinate ring. -/
theorem nativeFieldPolynomial_coordinateTower (E : EllipticCurve (Spec (.of k))) :
    let _ := nativeFieldCoordinateAlgebra E
    let _ := nativeFieldPolynomialAlgebra E
    IsScalarTower k[X] (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing
      E.E.functionField := by
  let _ := nativeFieldCoordinateAlgebra E
  exact (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.algebraPolynomial_isScalarTower
    E.E.functionField

/-- Polynomial constants equal the independently specified geometric constants. -/
theorem nativeFieldPolynomial_baseTower (E : EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    let _ := nativeFieldPolynomialAlgebra E
    IsScalarTower k k[X] E.E.functionField := by
  let _ := E.π.functionFieldBaseAlgebra
  let _ := nativeFieldCoordinateAlgebra E
  let _ := nativeFieldPolynomialAlgebra E
  let _ := nativeFieldCoordinate_isScalarTower E
  let _ := nativeFieldPolynomial_coordinateTower E
  apply IsScalarTower.of_algebraMap_eq
  intro r
  rw [IsScalarTower.algebraMap_apply k
      (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing E.E.functionField,
    IsScalarTower.algebraMap_apply k[X]
      (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing E.E.functionField,
    ← IsScalarTower.algebraMap_apply k k[X]
      (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing]

example (W : WeierstrassCurve k) [W.IsElliptic] :
    let E : EllipticCurve (Spec (.of k)) := modelEllipticCurve W
    let _ := E.π.functionFieldBaseAlgebra
    let _ := nativeFieldPolynomialAlgebra E
    IsScalarTower k k[X] E.E.functionField :=
  nativeFieldPolynomial_baseTower (modelEllipticCurve W)

example (E : EllipticCurve (Spec (.of k))) (r : k) :
    let _ := nativeFieldPolynomialAlgebra E
    algebraMap k[X] E.E.functionField (Polynomial.C r) = E.π.functionFieldConstants r := by
  let _ := E.π.functionFieldBaseAlgebra
  let _ := nativeFieldPolynomialAlgebra E
  let _ := nativeFieldPolynomial_baseTower E
  change algebraMap k[X] E.E.functionField (Polynomial.C r) = E.π.functionFieldConstants r
  rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply k k[X] E.E.functionField]
  rfl

#print axioms nativeFieldPolynomialAlgebra
#print axioms nativeFieldPolynomial_coordinateTower
#print axioms nativeFieldPolynomial_baseTower
#print axioms nativeFieldCoordinateRingHom
#print axioms nativeFieldCoordinate_isScalarTower
#print axioms Scheme.Hom.functionFieldBaseAlgebra
#print axioms WeierstrassCurve.Affine.algebraPolynomial
#print axioms WeierstrassCurve.Affine.algebraPolynomial_isScalarTower
#print axioms IsScalarTower.of_algebraMap_eq
#print axioms IsScalarTower.algebraMap_apply

end ModularCurves.YZeroCoarseJ
