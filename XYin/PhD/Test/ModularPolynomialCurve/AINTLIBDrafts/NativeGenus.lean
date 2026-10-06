/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.NativeFullConstantField
public import ModularCurves.Vendored.RiemannRoch.CoordinateFree.RiemannRoch

/-!
# Intrinsic genus of the actual native elliptic field

The statement uses only the independently defined geometric projection
algebra. The proven native coordinate fraction-field, polynomial and
rational-function scalars, finiteness, separability and full constants
supply the clean intrinsic-to-chart comparison and elliptic genus count.

The theorem holds over every field. The actual-model example and the
literal geometric constant-germ example exercise the stated base algebra.
No quotient genus or quotient elliptic-curve model is assumed or asserted.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open scoped Polynomial RatFunc

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

/-- The intrinsic genus of the native elliptic field over its geometric constants is one. -/
theorem nativeField_genus_eq_one (E : EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    FunctionField.genus k E.E.functionField = 1 := by
  let _ := E.π.functionFieldBaseAlgebra
  let _ := nativeFieldCoordinateAlgebra E
  let _ := nativeFieldCoordinate_isFractionRing E
  let _ := nativeFieldPolynomialAlgebra E
  let _ := nativeFieldPolynomial_coordinateTower E
  let _ := nativeFieldRatFuncAlgebra E
  let _ := nativeFieldRatFunc_polynomialTower E
  let _ := nativeField_functionField E
  let _ := nativeField_isSeparable E
  let _ := nativeFieldPolynomial_baseTower E
  let _ := nativeField_isFullConstantField E
  exact (FunctionField.genus_eq_genusChart k E.E.functionField).trans
    (WeierstrassCurve.Affine.Chart.genus_eq_one
      (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine E.E.functionField)

example (W : WeierstrassCurve k) [W.IsElliptic] :
    let E : EllipticCurve (Spec (.of k)) := modelEllipticCurve W
    let _ := E.π.functionFieldBaseAlgebra
    FunctionField.genus k E.E.functionField = 1 :=
  nativeField_genus_eq_one (modelEllipticCurve W)

example (E : EllipticCurve (Spec (.of k))) :
    let _ : Algebra k E.E.functionField :=
      ((E.E.germToFunctionField ⊤).hom.comp
        (E.π.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)).toAlgebra
    FunctionField.genus k E.E.functionField = 1 :=
  nativeField_genus_eq_one E

#print axioms nativeField_genus_eq_one
#print axioms FunctionField.genus
#print axioms FunctionField.genus_eq_genusChart
#print axioms WeierstrassCurve.Affine.Chart.genus_eq_one
#print axioms nativeField_isFullConstantField
#print axioms nativeField_functionField
#print axioms nativeField_isSeparable
#print axioms nativeFieldCoordinate_isFractionRing
#print axioms nativeFieldPolynomial_baseTower
#print axioms nativeFieldRatFunc_polynomialTower
#print axioms Scheme.Hom.functionFieldBaseAlgebra
#print axioms fieldWeierstrassModel_isElliptic

end ModularCurves.YZeroCoarseJ
