/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.NativePolynomialScalars

/-!
# Rational-function scalars on the actual native field

The Weierstrass lift of the retained actual polynomial embedding gives a
rational-function algebra on the native elliptic function field. Its
polynomial tower uses the same coordinate fraction-ring representation.
Its base-field tower agrees with the independent geometric projection
algebra, through the already proved polynomial base tower.

The actual model and rational-constant examples check these interfaces.
No global instances or characteristic restrictions are added. FunctionField,
separability, full constants, genus, and quotient models are separate results.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open scoped Polynomial RatFunc

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

/-- Rational-function scalars lift the actual native polynomial embedding. -/
@[reducible] noncomputable def nativeFieldRatFuncAlgebra
    (E : EllipticCurve (Spec (.of k))) : Algebra k⟮X⟯ E.E.functionField :=
  let _ := nativeFieldCoordinateAlgebra E
  let _ := nativeFieldCoordinate_isFractionRing E
  let _ := nativeFieldPolynomialAlgebra E
  let _ := nativeFieldPolynomial_coordinateTower E
  (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.algebraRatFunc E.E.functionField

/-- The rational-function lift agrees with the original polynomial embedding. -/
theorem nativeFieldRatFunc_polynomialTower (E : EllipticCurve (Spec (.of k))) :
    let _ := nativeFieldPolynomialAlgebra E
    let _ := nativeFieldRatFuncAlgebra E
    IsScalarTower k[X] k⟮X⟯ E.E.functionField := by
  let _ := nativeFieldCoordinateAlgebra E
  let _ := nativeFieldCoordinate_isFractionRing E
  let _ := nativeFieldPolynomialAlgebra E
  let _ := nativeFieldPolynomial_coordinateTower E
  exact (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.algebraRatFunc_isScalarTower
    E.E.functionField

/-- The lifted scalars still use the independent geometric base-field algebra. -/
theorem nativeFieldRatFunc_baseTower (E : EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    let _ := nativeFieldRatFuncAlgebra E
    IsScalarTower k k⟮X⟯ E.E.functionField := by
  let _ := E.π.functionFieldBaseAlgebra
  let _ := nativeFieldPolynomialAlgebra E
  let _ := nativeFieldRatFuncAlgebra E
  let _ := nativeFieldPolynomial_baseTower E
  let _ := nativeFieldRatFunc_polynomialTower E
  apply IsScalarTower.of_algebraMap_eq
  intro r
  rw [IsScalarTower.algebraMap_apply k k[X] E.E.functionField,
    IsScalarTower.algebraMap_apply k[X] k⟮X⟯ E.E.functionField,
    ← IsScalarTower.algebraMap_apply k k[X] k⟮X⟯]

example (W : WeierstrassCurve k) [W.IsElliptic] :
    let E : EllipticCurve (Spec (.of k)) := modelEllipticCurve W
    let _ := nativeFieldPolynomialAlgebra E
    let _ := nativeFieldRatFuncAlgebra E
    IsScalarTower k[X] k⟮X⟯ E.E.functionField :=
  nativeFieldRatFunc_polynomialTower (modelEllipticCurve W)

example (E : EllipticCurve (Spec (.of k))) (r : k) :
    let _ := nativeFieldRatFuncAlgebra E
    algebraMap k⟮X⟯ E.E.functionField (algebraMap k k⟮X⟯ r) = E.π.functionFieldConstants r := by
  let _ := E.π.functionFieldBaseAlgebra
  let _ := nativeFieldRatFuncAlgebra E
  let _ := nativeFieldRatFunc_baseTower E
  change algebraMap k⟮X⟯ E.E.functionField (algebraMap k k⟮X⟯ r) = E.π.functionFieldConstants r
  rw [← IsScalarTower.algebraMap_apply k k⟮X⟯ E.E.functionField]
  rfl

#print axioms nativeFieldRatFuncAlgebra
#print axioms nativeFieldRatFunc_polynomialTower
#print axioms nativeFieldRatFunc_baseTower
#print axioms nativeFieldCoordinate_isFractionRing
#print axioms nativeFieldPolynomial_coordinateTower
#print axioms nativeFieldPolynomial_baseTower
#print axioms WeierstrassCurve.Affine.algebraRatFunc
#print axioms WeierstrassCurve.Affine.algebraRatFunc_isScalarTower
#print axioms WeierstrassCurve.Affine.algebraMap_polynomial_injective
#print axioms IsFractionRing.lift_algebraMap
#print axioms IsScalarTower.of_algebraMap_eq
#print axioms IsScalarTower.algebraMap_apply

end ModularCurves.YZeroCoarseJ
