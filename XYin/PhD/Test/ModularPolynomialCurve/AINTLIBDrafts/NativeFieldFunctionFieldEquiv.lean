/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.NativeFieldWeierstrassModel
public import ModularCurves.ForMathlib.DominantFunctionField

/-!
# The native function field and its chosen Weierstrass function field

For a native elliptic curve over an arbitrary field, the inverse of its
retained scheme model isomorphism induces the actual function-field pullback.
Composing that ring isomorphism with the existing projective-model bridge
gives a ring equivalence to the chosen Weierstrass function field.

The two computation formulas identify the maps with the literal native
`functionFieldMap` by definitional equality. No algebraic closure,
characteristic restriction, quotient model, or genus premise is assumed.
The examples use an actual native model and the forward pullback formula.

This module proves a ring equivalence. Compatibility with independently
specified constants, an algebra equivalence, and genus transfer require
separate proofs and are not asserted here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

/-- The native model inverse induces the literal native function-field map. -/
theorem nativeFieldModelIso_functionFieldMap (E : EllipticCurve (Spec (.of k))) :
    (EllipticCurve.functionFieldIsoOfOpenImmersion (nativeFieldModelIso E).inv).hom =
      (nativeFieldModelIso E).inv.functionFieldMap := rfl

/-- The actual native function field is the chosen Weierstrass model's function field. -/
noncomputable def nativeFieldFunctionFieldEquiv (E : EllipticCurve (Spec (.of k))) :
    E.E.functionField ≃+*
      (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.FunctionField :=
  let i := EllipticCurve.functionFieldIsoOfOpenImmersion (nativeFieldModelIso E).inv
  i.commRingCatIsoToRingEquiv.trans
    (EllipticCurve.projModelFunctionFieldEquiv (fieldWeierstrassModel E.toEllipticCurveGeom))

/-- The forward ring hom is the actual inverse-model pullback followed by the model bridge. -/
theorem nativeFieldFunctionFieldEquiv_toRingHom (E : EllipticCurve (Spec (.of k))) :
    (nativeFieldFunctionFieldEquiv E).toRingHom =
      (EllipticCurve.projModelFunctionFieldEquiv
        (fieldWeierstrassModel E.toEllipticCurveGeom)).toRingHom.comp
          (nativeFieldModelIso E).inv.functionFieldMap.hom := rfl

example (W : WeierstrassCurve k) [W.IsElliptic] :
    Nonempty ((modelEllipticCurve W).E.functionField ≃+*
      (fieldWeierstrassModel (modelEllipticCurve W).toEllipticCurveGeom).toAffine.FunctionField) :=
  ⟨nativeFieldFunctionFieldEquiv (modelEllipticCurve W)⟩

example (E : EllipticCurve (Spec (.of k))) (s : E.E.functionField) :
    nativeFieldFunctionFieldEquiv E s =
      EllipticCurve.projModelFunctionFieldEquiv
        (fieldWeierstrassModel E.toEllipticCurveGeom)
          ((nativeFieldModelIso E).inv.functionFieldMap s) := rfl

#print axioms nativeFieldModelIso_functionFieldMap
#print axioms nativeFieldFunctionFieldEquiv
#print axioms nativeFieldFunctionFieldEquiv_toRingHom
#print axioms nativeFieldModelIso
#print axioms EllipticCurve.functionFieldIsoOfOpenImmersion
#print axioms EllipticCurve.projModelFunctionFieldEquiv
#print axioms Scheme.Hom.functionFieldMap
#print axioms EllipticCurve.isIntegral_of_field

end ModularCurves.YZeroCoarseJ
