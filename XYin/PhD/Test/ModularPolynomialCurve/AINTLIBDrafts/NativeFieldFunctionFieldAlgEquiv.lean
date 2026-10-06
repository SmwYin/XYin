/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.NativeFieldFunctionFieldEquiv
public import AINTLIBDrafts.FunctionFieldConstantsNaturality
public import AINTLIBDrafts.ProjModelFunctionFieldConstants

/-!
# The native function-field comparison over geometric constants

For a native elliptic curve over an arbitrary field, the structure map and
generic germ independently define its geometric constants. The actual
inverse-model pullback, the constant naturality square, and the projective
model's constant formula prove that the retained RingEquiv preserves them.

The resulting AlgEquiv uses the source algebra
`E.π.functionFieldConstants.toAlgebra` explicitly in its type and body.
Its underlying RingEquiv and forward RingHom are definitionally the retained
native comparison. No global instance, arbitrary transported scalar map,
algebraic-closedness, characteristic restriction, or quotient model is used.

The four examples exercise the actual native model, the literal native
constant germ, the actual model AlgEquiv, and scalar commutation. Genus,
fraction-field scalar towers, and quotient elliptic-curve upgrades are
separate statements and are not asserted by this module.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

/-- The inverse of the actual native model iso is over the original field. -/
theorem nativeFieldModelIso_inv_over (E : EllipticCurve (Spec (.of k))) :
    (nativeFieldModelIso E).inv ≫ E.π =
      projModelπ (fieldWeierstrassModel E.toEllipticCurveGeom) := by
  rw [← nativeFieldModelIso_over E]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The native ring equivalence preserves constants defined independently from E's projection. -/
theorem nativeFieldFunctionFieldEquiv_comp_constants (E : EllipticCurve (Spec (.of k))) :
    (nativeFieldFunctionFieldEquiv E).toRingHom.comp E.π.functionFieldConstants =
      algebraMap k (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.FunctionField := by
  have h := functionFieldMap_comp_functionFieldConstants (nativeFieldModelIso E).inv E.π
  rw [nativeFieldModelIso_inv_over] at h
  rw [nativeFieldFunctionFieldEquiv_toRingHom, RingHom.comp_assoc, h]
  exact projModelFunctionFieldEquiv_comp_constants
    (fieldWeierstrassModel E.toEllipticCurveGeom)

example (W : WeierstrassCurve k) [W.IsElliptic] :
    (nativeFieldFunctionFieldEquiv (modelEllipticCurve W)).toRingHom.comp
        (modelEllipticCurve W).π.functionFieldConstants =
      algebraMap k
        (fieldWeierstrassModel (modelEllipticCurve W).toEllipticCurveGeom).toAffine.FunctionField :=
  nativeFieldFunctionFieldEquiv_comp_constants (modelEllipticCurve W)

example (E : EllipticCurve (Spec (.of k))) (r : k) :
    nativeFieldFunctionFieldEquiv E
        (E.E.germToFunctionField ⊤ (E.π.appTop ((Scheme.ΓSpecIso (.of k)).inv r))) =
      algebraMap k (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.FunctionField r := by
  change nativeFieldFunctionFieldEquiv E (E.π.functionFieldConstants r) = _
  exact RingHom.congr_fun (nativeFieldFunctionFieldEquiv_comp_constants E) r

#print axioms nativeFieldModelIso_inv_over
#print axioms nativeFieldFunctionFieldEquiv_comp_constants
#print axioms nativeFieldFunctionFieldEquiv_toRingHom
#print axioms functionFieldMap_comp_functionFieldConstants
#print axioms Scheme.Hom.functionFieldConstants
#print axioms projModelFunctionFieldEquiv_comp_constants
#print axioms projModelConstantRingHom
#print axioms nativeFieldModelIso_over
#print axioms nativeFieldFunctionFieldEquiv
#print axioms RingHom.comp_assoc


/-- The native comparison over the independently specified geometric constant algebra. -/
noncomputable def nativeFieldFunctionFieldAlgEquiv (E : EllipticCurve (Spec (.of k))) :
    let _ : Algebra k E.E.functionField := E.π.functionFieldConstants.toAlgebra
    E.E.functionField ≃ₐ[k]
      (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.FunctionField :=
  let _ : Algebra k E.E.functionField := E.π.functionFieldConstants.toAlgebra
  AlgEquiv.ofRingEquiv (f := nativeFieldFunctionFieldEquiv E) fun r ↦
    RingHom.congr_fun (nativeFieldFunctionFieldEquiv_comp_constants E) r

/-- Packaging the constant-compatible comparison preserves the underlying ring equivalence. -/
theorem nativeFieldFunctionFieldAlgEquiv_toRingEquiv (E : EllipticCurve (Spec (.of k))) :
    let _ : Algebra k E.E.functionField := E.π.functionFieldConstants.toAlgebra
    (nativeFieldFunctionFieldAlgEquiv E).toRingEquiv = nativeFieldFunctionFieldEquiv E := rfl

/-- Packaging preserves the literal forward ring homomorphism. -/
theorem nativeFieldFunctionFieldAlgEquiv_toRingHom (E : EllipticCurve (Spec (.of k))) :
    let _ : Algebra k E.E.functionField := E.π.functionFieldConstants.toAlgebra
    (nativeFieldFunctionFieldAlgEquiv E).toRingHom =
      (nativeFieldFunctionFieldEquiv E).toRingHom := rfl

example (W : WeierstrassCurve k) [W.IsElliptic] :
    let E : EllipticCurve (Spec (.of k)) := modelEllipticCurve W
    let _ : Algebra k E.E.functionField := E.π.functionFieldConstants.toAlgebra
    Nonempty (E.E.functionField ≃ₐ[k]
      (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.FunctionField) :=
  ⟨nativeFieldFunctionFieldAlgEquiv (modelEllipticCurve W)⟩

example (E : EllipticCurve (Spec (.of k))) (r : k) :
    let _ : Algebra k E.E.functionField := E.π.functionFieldConstants.toAlgebra
    nativeFieldFunctionFieldAlgEquiv E (algebraMap k E.E.functionField r) =
      algebraMap k (fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.FunctionField r := by
  let _ : Algebra k E.E.functionField := E.π.functionFieldConstants.toAlgebra
  exact (nativeFieldFunctionFieldAlgEquiv E).commutes r

#print axioms nativeFieldFunctionFieldAlgEquiv
#print axioms nativeFieldFunctionFieldAlgEquiv_toRingEquiv
#print axioms nativeFieldFunctionFieldAlgEquiv_toRingHom
#print axioms AlgEquiv.ofRingEquiv

end ModularCurves.YZeroCoarseJ
