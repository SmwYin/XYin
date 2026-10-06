/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.NativeFieldFunctionFieldAlgEquiv
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The native field as a fraction field of the chosen coordinate ring

For a native elliptic curve over an arbitrary field, the inverse of the
retained comparison embeds the chosen affine coordinate ring into the actual
native function field. The coordinate algebra is a reducible definition of
that literal map. Its scalar tower agrees with the independently defined
geometric constants of the original structure morphism.

The inverse field comparison is linear over this coordinate ring and hence
transfers its fraction-field property. The two examples check an actual native
model and the coordinate constants. The source constant algebra is unchanged;
polynomial and rational-function scalars, full constants, genus, and quotient
models require further proofs and are not asserted here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

/-- The chosen affine coordinate ring embeds into the actual native function field. -/
noncomputable def nativeFieldCoordinateRingHom (E : EllipticCurve (Spec (.of k))) :
    (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing →+*
      E.E.functionField :=
  let _ : Algebra k E.E.functionField := E.π.functionFieldConstants.toAlgebra
  (nativeFieldFunctionFieldAlgEquiv E).symm.toRingHom.comp
    (algebraMap (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing
      (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.FunctionField)

/-- The coordinate algebra is the algebra of that literal embedding. -/
@[reducible] noncomputable def nativeFieldCoordinateAlgebra
    (E : EllipticCurve (Spec (.of k))) :
    Algebra (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing
      E.E.functionField :=
  (nativeFieldCoordinateRingHom E).toAlgebra

/-- The coordinate algebra agrees with the independently defined geometric constants. -/
theorem nativeFieldCoordinate_isScalarTower (E : EllipticCurve (Spec (.of k))) :
    let _ : Algebra k E.E.functionField := E.π.functionFieldConstants.toAlgebra
    let _ := nativeFieldCoordinateAlgebra E
    IsScalarTower k (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing
      E.E.functionField := by
  let _ : Algebra k E.E.functionField := E.π.functionFieldConstants.toAlgebra
  let _ := nativeFieldCoordinateAlgebra E
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change E.π.functionFieldConstants r = (nativeFieldFunctionFieldAlgEquiv E).symm
    (algebraMap (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing
      (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.FunctionField
        (algebraMap k (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing r))
  rw [← IsScalarTower.algebraMap_apply k
    (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing
    (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.FunctionField]
  exact ((nativeFieldFunctionFieldAlgEquiv E).symm.commutes r).symm

/-- The actual inverse field comparison is linear over the chosen coordinate ring. -/
noncomputable def nativeFieldCoordinateAlgEquiv (E : EllipticCurve (Spec (.of k))) :
    let _ := nativeFieldCoordinateAlgebra E
    (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.FunctionField ≃ₐ[
      (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing] E.E.functionField :=
  let _ : Algebra k E.E.functionField := E.π.functionFieldConstants.toAlgebra
  let _ := nativeFieldCoordinateAlgebra E
  AlgEquiv.ofRingEquiv (f := (nativeFieldFunctionFieldAlgEquiv E).symm.toRingEquiv) fun _ ↦ rfl

/-- The native field is a fraction field of the actual chosen coordinate ring. -/
theorem nativeFieldCoordinate_isFractionRing (E : EllipticCurve (Spec (.of k))) :
    let _ := nativeFieldCoordinateAlgebra E
    IsFractionRing (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing
      E.E.functionField := by
  let _ := nativeFieldCoordinateAlgebra E
  exact IsFractionRing.of_algEquiv (nativeFieldCoordinateAlgEquiv E)

example (W : WeierstrassCurve k) [W.IsElliptic] :
    let E : EllipticCurve (Spec (.of k)) := modelEllipticCurve W
    let _ := nativeFieldCoordinateAlgebra E
    IsFractionRing (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing
      E.E.functionField :=
  nativeFieldCoordinate_isFractionRing (modelEllipticCurve W)

example (E : EllipticCurve (Spec (.of k))) (r : k) :
    nativeFieldCoordinateRingHom E
      (algebraMap k (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing r) =
        E.π.functionFieldConstants r := by
  let _ : Algebra k E.E.functionField := E.π.functionFieldConstants.toAlgebra
  let _ := nativeFieldCoordinateAlgebra E
  let _ := nativeFieldCoordinate_isScalarTower E
  exact (IsScalarTower.algebraMap_apply k
    (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.CoordinateRing E.E.functionField r).symm

#print axioms nativeFieldCoordinateRingHom
#print axioms nativeFieldCoordinateAlgebra
#print axioms nativeFieldCoordinate_isScalarTower
#print axioms nativeFieldCoordinateAlgEquiv
#print axioms nativeFieldCoordinate_isFractionRing
#print axioms nativeFieldFunctionFieldAlgEquiv
#print axioms IsScalarTower.of_algebraMap_eq
#print axioms IsFractionRing.of_algEquiv
#print axioms AlgEquiv.ofRingEquiv

end ModularCurves.YZeroCoarseJ
