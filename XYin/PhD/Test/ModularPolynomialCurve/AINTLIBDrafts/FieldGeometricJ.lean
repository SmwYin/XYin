/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.GeometricJ
public import ModularCurves.EllipticCurve.GlobalChartOverField

/-!
# Weierstrass models and geometric j over fields

A pointed Weierstrass chart containing the unique point of `Spec k` covers the entire
base. Mapping its coefficients through `ΓSpecIso` gives an elliptic Weierstrass curve
over `k`, whose j-invariant is the value of the geometric global j section.
This construction has no full-level moduli or coarse-quotient dependency.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ModularCurves

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

/-- The top affine open of the spectrum of a field. -/
noncomputable abbrev fieldTopAffineOpen : (Spec (.of k)).affineOpens :=
  ⟨⊤, isAffineOpen_top _⟩

/-- A geometric elliptic curve over a field has a pointed Weierstrass presentation
on the entire base. -/
theorem nonempty_fieldTopPresentation (G : EllipticCurveGeom (Spec (.of k))) :
    Nonempty (LocalPresentation G (fieldTopAffineOpen (k := k))) :=
  nonempty_localPresentation_top G

/-- A pointed Weierstrass presentation over the entire spectrum of a field. -/
noncomputable def fieldTopPresentation (G : EllipticCurveGeom (Spec (.of k))) :
    LocalPresentation G (fieldTopAffineOpen (k := k)) :=
  localPresentationTop G

/-- The Weierstrass curve over the original field obtained from the top presentation. -/
noncomputable def fieldWeierstrassModel (G : EllipticCurveGeom (Spec (.of k))) :
    WeierstrassCurve k :=
  (fieldTopPresentation G).W.map (Scheme.ΓSpecIso (.of k)).hom.hom

/-- The Weierstrass model of a geometric elliptic curve is elliptic. -/
instance fieldWeierstrassModel_isElliptic (G : EllipticCurveGeom (Spec (.of k))) :
    (fieldWeierstrassModel G).IsElliptic := by
  let fieldModelChartElliptic := (fieldTopPresentation G).elliptic
  unfold fieldWeierstrassModel
  infer_instance

/-- The field model computes the geometric j section under the canonical global-section
identification. -/
theorem fieldWeierstrassModel_j (G : EllipticCurveGeom (Spec (.of k))) :
    (fieldWeierstrassModel G).j = (Scheme.ΓSpecIso (.of k)).hom.hom (jSection G) := by
  let fieldModelJChartElliptic := (fieldTopPresentation G).elliptic
  have h : jSection G = chartJ (fieldTopPresentation G) := by
    simpa only [Scheme.resLE_rfl] using jSection_res (fieldTopPresentation G)
  change ((fieldTopPresentation G).W.map (Scheme.ΓSpecIso (.of k)).hom.hom).j = _
  rw [WeierstrassCurve.map_j]
  exact congrArg (Scheme.ΓSpecIso (.of k)).hom.hom h.symm

#print axioms fieldTopAffineOpen
#print axioms nonempty_fieldTopPresentation
#print axioms fieldTopPresentation
#print axioms fieldWeierstrassModel
#print axioms fieldWeierstrassModel_isElliptic
#print axioms fieldWeierstrassModel_j

end ModularCurves.YZeroCoarseJ
