/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.NativeRatFuncScalars

/-!
# Finiteness and separability of the native rational-function extension

The actual chosen-coordinate fraction field, polynomial embedding and
rational-function lift identify the native elliptic field as a FunctionField.
The same scalar pack proves separability over that actual RatFunc algebra by
the existing Weierstrass theorem, in every characteristic.

The two examples check an actual model and the native separability interface.
The scalars remain those of the retained geometric comparison; no global
instances or additional hypotheses are introduced. Full constants, genus,
and a quotient model require separate results.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open scoped Polynomial RatFunc

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

/-- The actual native field is finite over its actual rational-function scalar algebra. -/
theorem nativeField_functionField (E : EllipticCurve (Spec (.of k))) :
    let _ := nativeFieldRatFuncAlgebra E
    _root_.FunctionField k E.E.functionField := by
  let _ := nativeFieldCoordinateAlgebra E
  let _ := nativeFieldCoordinate_isFractionRing E
  let _ := nativeFieldPolynomialAlgebra E
  let _ := nativeFieldPolynomial_coordinateTower E
  let _ := nativeFieldRatFuncAlgebra E
  let _ := nativeFieldRatFunc_polynomialTower E
  exact (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.functionField E.E.functionField

/-- The native rational-function extension is separable in every characteristic. -/
theorem nativeField_isSeparable (E : EllipticCurve (Spec (.of k))) :
    let _ := nativeFieldRatFuncAlgebra E
    Algebra.IsSeparable k⟮X⟯ E.E.functionField := by
  let _ := nativeFieldCoordinateAlgebra E
  let _ := nativeFieldCoordinate_isFractionRing E
  let _ := nativeFieldPolynomialAlgebra E
  let _ := nativeFieldPolynomial_coordinateTower E
  let _ := nativeFieldRatFuncAlgebra E
  let _ := nativeFieldRatFunc_polynomialTower E
  exact (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.isSeparable E.E.functionField

example (W : WeierstrassCurve k) [W.IsElliptic] :
    let E : EllipticCurve (Spec (.of k)) := modelEllipticCurve W
    let _ := nativeFieldRatFuncAlgebra E
    _root_.FunctionField k E.E.functionField :=
  nativeField_functionField (modelEllipticCurve W)

example (E : EllipticCurve (Spec (.of k))) :
    let _ := nativeFieldRatFuncAlgebra E
    Algebra.IsSeparable k⟮X⟯ E.E.functionField :=
  nativeField_isSeparable E

#print axioms nativeField_functionField
#print axioms nativeField_isSeparable
#print axioms nativeFieldCoordinate_isFractionRing
#print axioms nativeFieldPolynomial_coordinateTower
#print axioms nativeFieldRatFuncAlgebra
#print axioms nativeFieldRatFunc_polynomialTower
#print axioms WeierstrassCurve.Affine.functionField
#print axioms WeierstrassCurve.Affine.isSeparable
#print axioms fieldWeierstrassModel_isElliptic

end ModularCurves.YZeroCoarseJ
