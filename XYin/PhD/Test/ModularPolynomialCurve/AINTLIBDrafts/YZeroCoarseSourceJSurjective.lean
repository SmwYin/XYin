/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.ModelGeometricJ
public import AINTLIBDrafts.YZeroCoarseMarkedComplexCurves
public import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

/-!
# Surjectivity of the actual coarse source-j on complex points

The geometric j section of the native model of an elliptic Weierstrass curve computes
the original Weierstrass j. Applying this to `WeierstrassCurve.ofJ z` and the actual
full-level classifier gives a coarse complex point with source-j equal to `z`.
The existing scheme/algebra-point equivalence gives the same statement for evaluation
of the literal Borel-invariant fine j section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ModularCurves ModularCurves.YZeroCoarseJ

noncomputable section

universe u

namespace ModularCurves.YZeroCoarseJ

/-- The field model of the native model curve has the j of the original Weierstrass curve. -/
theorem fieldWeierstrassModel_model_j {k : Type u} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic] :
    (fieldWeierstrassModel (modelEllipticCurve W).toEllipticCurveGeom).j = W.j := by
  rw [fieldWeierstrassModel_j, model_jSection]
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ (Scheme.ΓSpecIso (.of k)).hom).hom W.j = W.j
  rw [Iso.inv_hom_id]
  rfl

end ModularCurves.YZeroCoarseJ

namespace ModularPolynomialCurveTest.AINTLIB

variable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))

/-- Every complex number is the actual coarse source-j of an actual coarse complex point. -/
theorem yZeroComplexSourceJValue_surjective :
    Function.Surjective (yZeroComplexSourceJValue N hN) := by
  intro z
  obtain ⟨p, hp⟩ := exists_yZeroComplexSchemePoint_sourceJ_eq N hN
    (modelEllipticCurve (WeierstrassCurve.ofJ z))
  exact ⟨p, hp.trans ((fieldWeierstrassModel_model_j
    (WeierstrassCurve.ofJ z)).trans (WeierstrassCurve.ofJ_j z))⟩

/-- The literal invariant j section takes every complex value on complex algebra points. -/
theorem yZeroComplexInvariantJValue_surjective :
    Function.Surjective (fun φ : yZeroComplexAlgebraPoint N hN =>
      φ (fineJInvariant (R := .of ℂ) N hN (complexLevelIsUnit N))) := by
  intro z
  obtain ⟨p, hp⟩ := yZeroComplexSourceJValue_surjective N hN z
  exact ⟨yZeroComplexAlgebraPointOfScheme N hN p,
    (yZeroComplexSourceJValue_eq N hN p).symm.trans hp⟩

#print axioms ModularCurves.YZeroCoarseJ.fieldWeierstrassModel_model_j
#print axioms yZeroComplexSourceJValue_surjective
#print axioms yZeroComplexInvariantJValue_surjective

/-- Level three already realizes every complex source-j, with no assumed marking. -/
example (z : ℂ) : ∃ p : yZeroComplexSchemePoint 3 (by decide),
    yZeroComplexSourceJValue 3 (by decide) p = z :=
  yZeroComplexSourceJValue_surjective 3 (by decide) z

example (z : ℂ) : ∃ φ : yZeroComplexAlgebraPoint 3 (by decide),
    φ (fineJInvariant (R := .of ℂ) 3 (by decide) (complexLevelIsUnit 3)) = z :=
  yZeroComplexInvariantJValue_surjective 3 (by decide) z

end ModularPolynomialCurveTest.AINTLIB
