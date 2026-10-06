/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.NativeFunctionFieldStructure
public import ModularCurves.EllipticCurve.FibreConstantField

/-!
# Full constants of the actual native elliptic field

The native field uses the independently specified geometric projection
algebra. Its actual coordinate fraction-ring and polynomial/RatFunc scalar
pack supplies the finite and separable extension data for the clean native
Weierstrass full-constant-field theorem.

The actual model and constant-reflection examples check this base algebra.
The result holds over every field without additional hypotheses or global
instances. Genus and quotient elliptic-curve upgrades remain separate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open scoped Polynomial RatFunc

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

/-- Algebraic elements of the actual native field are its geometric base constants. -/
theorem nativeField_isFullConstantField (E : EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    FunctionField.IsFullConstantField k E.E.functionField := by
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
  exact FibreRR.isFullConstantField
    (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine E.E.functionField

example (W : WeierstrassCurve k) [W.IsElliptic] :
    let E : EllipticCurve (Spec (.of k)) := modelEllipticCurve W
    let _ := E.π.functionFieldBaseAlgebra
    FunctionField.IsFullConstantField k E.E.functionField :=
  nativeField_isFullConstantField (modelEllipticCurve W)

example (E : EllipticCurve (Spec (.of k))) (x : E.E.functionField) :
    let _ := E.π.functionFieldBaseAlgebra
    IsAlgebraic k x → ∃ c : k, x = E.π.functionFieldConstants c := by
  let _ := E.π.functionFieldBaseAlgebra
  let _ := nativeField_isFullConstantField E
  exact fun hx ↦ FunctionField.IsFullConstantField.algebraic_mem x hx

#print axioms nativeField_isFullConstantField
#print axioms ModularCurves.FibreRR.isFullConstantField
#print axioms nativeFieldCoordinate_isFractionRing
#print axioms nativeFieldPolynomial_coordinateTower
#print axioms nativeFieldPolynomial_baseTower
#print axioms nativeFieldRatFunc_polynomialTower
#print axioms nativeField_functionField
#print axioms nativeField_isSeparable
#print axioms Scheme.Hom.functionFieldBaseAlgebra
#print axioms FunctionField.IsFullConstantField.algebraic_mem
#print axioms fieldWeierstrassModel_isElliptic

end ModularCurves.YZeroCoarseJ
