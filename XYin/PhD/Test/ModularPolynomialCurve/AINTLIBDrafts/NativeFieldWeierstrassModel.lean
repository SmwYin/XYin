/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.FieldGeometricJ
public import ModularCurves.EllipticCurve.MulByHomDegree
public import ModularCurves.EllipticCurve.IntegralOverField
public import ModularCurves.EllipticCurve.AdditionBaseChange

/-!
# A native elliptic curve's chosen Weierstrass model over a field

For a native elliptic curve over `Spec k`, its existing top local presentation
and the coefficient isomorphism `Γ(Spec k, ⊤) ≃ k` give an actual scheme
isomorphism with the projective model of the chosen field Weierstrass curve.
The structure-map formula proves that this isomorphism is over the original
`Spec k`.

The construction uses the existing pointed local presentation and the literal
coefficient base-change pullback square. It assumes only that `k` is a field;
no algebraic closure, characteristic restriction, quotient model, or genus
hypothesis is introduced. The example applies the construction to an actual
native `modelEllipticCurve`.

The printed primitive checks include the existing projective-model
function-field bridge and native integrality helper. This module does not
construct a native function-field equivalence, prove compatibility with
constant scalars on function fields, compute a genus, or upgrade a subgroup
quotient to an elliptic curve.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ModularCurves

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

/-- The actual native elliptic curve is isomorphic to its chosen field model. -/
noncomputable def nativeFieldModelIso (E : EllipticCurve (Spec (.of k))) :
    E.E ≅ projModel (fieldWeierstrassModel E.toEllipticCurveGeom) := by
  let P := fieldTopPresentation E.toEllipticCurveGeom
  have : IsIso (fieldTopAffineOpen (k := k)).1.ι := by
    change IsIso ((⊤ : (Spec (.of k)).Opens).ι)
    rw [← Scheme.topIso_hom]
    infer_instance
  have : IsIso (pullback.fst E.π (fieldTopAffineOpen (k := k)).1.ι) := inferInstance
  let σ : Γ(Spec (.of k), (⊤ : (Spec (.of k)).Opens)) →+* k :=
    (Scheme.ΓSpecIso (.of k)).hom.hom
  have : IsIso (Spec.map (CommRingCat.ofHom σ)) := by
    change IsIso (Spec.map (Scheme.ΓSpecIso (.of k)).hom)
    infer_instance
  let f := projModelBaseChangeOf σ P.W
    (fieldWeierstrassModel E.toEllipticCurveGeom) rfl
  have : IsIso f :=
    (isPullback_projModelBaseChangeOf σ P.W
      (fieldWeierstrassModel E.toEllipticCurveGeom) rfl).isIso_fst_of_isIso
  exact (asIso (pullback.fst E.π (fieldTopAffineOpen (k := k)).1.ι)).symm ≪≫
    P.e ≪≫ (asIso f).symm

/-- The chosen global model iso preserves the original structure map. -/
theorem nativeFieldModelIso_over (E : EllipticCurve (Spec (.of k))) :
    (nativeFieldModelIso E).hom ≫ projModelπ (fieldWeierstrassModel E.toEllipticCurveGeom) =
      E.π := by
  let P := fieldTopPresentation E.toEllipticCurveGeom
  let σ : Γ(Spec (.of k), (⊤ : (Spec (.of k)).Opens)) →+* k :=
    (Scheme.ΓSpecIso (.of k)).hom.hom
  have : IsIso (fieldTopAffineOpen (k := k)).1.ι := by
    change IsIso ((⊤ : (Spec (.of k)).Opens).ι)
    rw [← Scheme.topIso_hom]
    infer_instance
  have : IsIso (pullback.fst E.π (fieldTopAffineOpen (k := k)).1.ι) := inferInstance
  have : IsIso (Spec.map (CommRingCat.ofHom σ)) := by
    change IsIso (Spec.map (Scheme.ΓSpecIso (.of k)).hom)
    infer_instance
  let f := projModelBaseChangeOf σ P.W
    (fieldWeierstrassModel E.toEllipticCurveGeom) rfl
  have : IsIso f :=
    (isPullback_projModelBaseChangeOf σ P.W
      (fieldWeierstrassModel E.toEllipticCurveGeom) rfl).isIso_fst_of_isIso
  have hbase : (fieldTopAffineOpen (k := k)).2.isoSpec.hom =
      (fieldTopAffineOpen (k := k)).1.ι ≫ Spec.map (CommRingCat.ofHom σ) := by
    change (isAffineOpen_top (Spec (.of k))).isoSpec.hom =
      (⊤ : (Spec (.of k)).Opens).ι ≫ Spec.map (Scheme.ΓSpecIso (.of k)).hom
    rw [← Scheme.isoSpec_Spec_hom]
    apply (cancel_mono (Spec (.of k)).isoSpec.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simpa only [IsAffineOpen.fromSpec_top] using
      (isAffineOpen_top (Spec (.of k))).isoSpec_hom_fromSpec
  have hf : inv f ≫ projModelπ (fieldWeierstrassModel E.toEllipticCurveGeom) ≫
      Spec.map (CommRingCat.ofHom σ) = projModelπ P.W := by
    rw [← (isPullback_projModelBaseChangeOf σ P.W
      (fieldWeierstrassModel E.toEllipticCurveGeom) rfl).w]
    exact IsIso.inv_hom_id_assoc f _
  change (inv (pullback.fst E.π (fieldTopAffineOpen (k := k)).1.ι) ≫ P.e.hom ≫ inv f) ≫
    projModelπ (fieldWeierstrassModel E.toEllipticCurveGeom) = E.π
  apply (cancel_mono (Spec.map (CommRingCat.ofHom σ))).mp
  simp only [Category.assoc]
  rw [hf, P.compat_π, hbase]
  rw [← Category.assoc (pullback.snd E.π (fieldTopAffineOpen (k := k)).1.ι),
    ← pullback.condition]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

example (W : WeierstrassCurve k) [W.IsElliptic] :
    Nonempty ((modelEllipticCurve W).E ≅
      projModel (fieldWeierstrassModel (modelEllipticCurve W).toEllipticCurveGeom)) :=
  ⟨nativeFieldModelIso (modelEllipticCurve W)⟩

#print axioms nativeFieldModelIso
#print axioms nativeFieldModelIso_over
#print axioms EllipticCurve.projModelFunctionFieldEquiv
#print axioms EllipticCurve.functionFieldIsoOfOpenImmersion
#print axioms isPullback_projModelBaseChange
#print axioms isPullback_projModelBaseChangeOf
#print axioms projModelBaseChangeOf
#print axioms fieldWeierstrassModel
#print axioms fieldWeierstrassModel_isElliptic
#print axioms fieldTopPresentation
#print axioms nonempty_fieldTopPresentation
#print axioms EllipticCurve.isIntegral_of_field
#print axioms modelEllipticCurve

end ModularCurves.YZeroCoarseJ
