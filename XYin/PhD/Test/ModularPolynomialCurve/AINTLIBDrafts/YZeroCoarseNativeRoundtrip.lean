/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseMarkedComplexCurves

/-!
# Classifying the native curve and marking recovers the original full point

The universal pullback at a full point has structure map equal to the complex-base
identity by the point's over-base equation. An explicit pointed cartesian morphism,
with identity base and total-space maps, compares it to `complexEllObj` of the same
literal curve. It pulls the actual marking identically. Yoneda naturality then proves
that the actual marking classifier has exactly the original full scheme point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits ModularCurves

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

variable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))

/-- Identity base and curve maps compare the two structure-map presentations. -/
def fullComplexPointIdentityHom (p : fullComplexSchemePoint N hN) :
    complexEllObj (fullComplexPointEllObj N hN p).curve ⟶
      fullComplexPointEllObj N hN p where
  baseHom := 𝟙 (Spec (.of ℂ))
  base_w := by
    change 𝟙 (Spec (.of ℂ)) ≫
      (p.val ≫ (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).structMap) = 𝟙 _
    rw [Category.id_comp]
    exact p.property
  top := 𝟙 (fullComplexPointEllObj N hN p).curve.E
  isPullback := by
    let π : (fullComplexPointEllObj N hN p).curve.E ⟶ Spec (.of ℂ) :=
      (fullComplexPointEllObj N hN p).curve.π
    change IsPullback (𝟙 _) π π (𝟙 (Spec (.of ℂ)))
    exact IsPullback.of_horiz_isIso
      ⟨(Category.id_comp π).trans (Category.comp_id π).symm⟩
  zero_w := by
    let z : Spec (.of ℂ) ⟶ (fullComplexPointEllObj N hN p).curve.E :=
      (fullComplexPointEllObj N hN p).curve.zero
    change z ≫ 𝟙 _ = 𝟙 (Spec (.of ℂ)) ≫ z
    exact (Category.comp_id z).trans (Category.id_comp z).symm

/-- Every section pulls back identically along the explicit comparison. -/
theorem fullComplexPointIdentityHom_pullSection (p : fullComplexSchemePoint N hN)
    (Q : (fullComplexPointEllObj N hN p).curve.Section) :
    EllHom.pullSection (.of ℂ) (fullComplexPointIdentityHom N hN p) Q = Q := by
  apply Subtype.ext
  let a : Spec (.of ℂ) ⟶ (fullComplexPointEllObj N hN p).curve.E :=
    (EllHom.pullSection (.of ℂ) (fullComplexPointIdentityHom N hN p) Q).val
  let b : Spec (.of ℂ) ⟶ (fullComplexPointEllObj N hN p).curve.E := Q.val
  have h : a ≫ 𝟙 (fullComplexPointEllObj N hN p).curve.E = 𝟙 (Spec (.of ℂ)) ≫ b :=
    (fullComplexPointIdentityHom N hN p).isPullback.lift_fst _ _ _
  exact (Category.comp_id a).symm.trans (h.trans (Category.id_comp b))

/-- The actual native full marking pulls back identically. -/
theorem fullComplexPointIdentityHom_level (p : fullComplexSchemePoint N hN) :
    (gammaFullNaiveProblem (.of ℂ) N).map (fullComplexPointIdentityHom N hN p).op
      (fullComplexPointLevel N hN p) = fullComplexPointLevel N hN p := by
  apply Subtype.ext
  exact Prod.ext (fullComplexPointIdentityHom_pullSection N hN p _)
    (fullComplexPointIdentityHom_pullSection N hN p _)

/-- The actual native curve and marking classify back to the original actual full point. -/
theorem fullComplexSchemePointOfMarking_native (p : fullComplexSchemePoint N hN) :
    fullComplexSchemePointOfMarking N hN (fullComplexPointEllObj N hN p).curve
      (fullComplexPointLevel N hN p) = p := by
  apply Subtype.ext
  let r := xFullNaiveRepr (R := .of ℂ) N hN (complexLevelIsUnit N)
  let v := (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).pullbackAlongπ p.val
  have h := r.comp_homEquiv_symm (r.homEquiv v) (fullComplexPointIdentityHom N hN p)
  rw [r.homEquiv.symm_apply_apply] at h
  change fullComplexPointIdentityHom N hN p ≫ v =
    fullMarkingClassifier N hN (fullComplexPointEllObj N hN p).curve
      ((gammaFullNaiveProblem (.of ℂ) N).map (fullComplexPointIdentityHom N hN p).op
        (fullComplexPointLevel N hN p)) at h
  rw [fullComplexPointIdentityHom_level] at h
  let a : Spec (.of ℂ) ⟶ (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base :=
    (fullMarkingClassifier N hN (fullComplexPointEllObj N hN p).curve
      (fullComplexPointLevel N hN p)).baseHom
  have hb : 𝟙 (Spec (.of ℂ)) ≫ p.val = a := congrArg EllHom.baseHom h
  exact hb.symm.trans (Category.id_comp p.val)

#print axioms fullComplexPointIdentityHom
#print axioms fullComplexPointIdentityHom_pullSection
#print axioms fullComplexPointIdentityHom_level
#print axioms fullComplexSchemePointOfMarking_native

example (p : fullComplexSchemePoint 3 (by decide)) :
    fullComplexSchemePointOfMarking 3 (by decide) (fullComplexPointEllObj 3 (by decide) p).curve
      (fullComplexPointLevel 3 (by decide) p) = p :=
  fullComplexSchemePointOfMarking_native 3 (by decide) p

end ModularPolynomialCurveTest.AINTLIB
