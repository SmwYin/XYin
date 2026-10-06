/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseFineComplexPoints

/-!
# Native marked complex curves give actual coarse modular-curve points

The chosen full-level representation classifies an actual naive marking on a given
complex elliptic curve. Its classification point pulls the universal pointed elliptic
object back to the given object, and transports the universal marking to the given one.
The resulting actual coarse point has the source-j value of that given elliptic curve.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ModularCurves ModularCurves.YZeroCoarseJ
open ModularPolynomialCurveTest.AINTLIB

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

/-- A given native complex elliptic curve as an object over the original complex base. -/
def complexEllObj (E : ModularCurves.EllipticCurve (Spec (.of ℂ))) : EllObj (.of ℂ) where
  base := Spec (.of ℂ)
  structMap := 𝟙 _
  curve := E

/-- The given curve object has the affine complex base. -/
instance complexEllObj_base_isAffine
    (E : ModularCurves.EllipticCurve (Spec (.of ℂ))) : IsAffine (complexEllObj E).base := by
  change IsAffine (Spec (.of ℂ))
  infer_instance

variable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
variable (E : ModularCurves.EllipticCurve (Spec (.of ℂ)))

/-- The marking is the actual naive full-level moduli datum on the given curve. -/
abbrev complexFullMarking :=
  (gammaFullNaiveProblem (.of ℂ) N).obj (Opposite.op (complexEllObj E))

/-- Every native complex elliptic curve has a naive full-level marking at any nonzero level. -/
theorem nonempty_complexFullMarking : Nonempty (complexFullMarking N E) := by
  obtain ⟨P, Q, h⟩ := exists_isNaiveFullLevel_of_isAlgClosed ℂ E N
    (complexLevelIsUnit N).ne_zero
  exact ⟨⟨(P, Q), h⟩⟩

variable (α : complexFullMarking N E)

/-- The actual classifier supplied by the chosen full-level representation. -/
def fullMarkingClassifier : complexEllObj E ⟶
    fullObject (R := .of ℂ) N hN (complexLevelIsUnit N) :=
  (xFullNaiveRepr (R := .of ℂ) N hN (complexLevelIsUnit N)).homEquiv.symm α

/-- Its base morphism is literally an actual full-level complex scheme point. -/
def fullComplexSchemePointOfMarking : fullComplexSchemePoint N hN :=
  ⟨(fullMarkingClassifier N hN E α).baseHom,
    (fullMarkingClassifier N hN E α).base_w⟩

/-- The actual coarse complex scheme point classified by the marked native curve. -/
def yZeroComplexSchemePointOfMarking : yZeroComplexSchemePoint N hN :=
  yZeroComplexSchemePointOfFull N hN (fullComplexSchemePointOfMarking N hN E α)

/-- The given pointed elliptic object is the literal universal-curve pullback at its classifier. -/
def complexFullMarkingNativeIso :
    complexEllObj E ≅
      fullComplexPointEllObj N hN (fullComplexSchemePointOfMarking N hN E α) :=
  EllObj.isoPullbackAlong (fullMarkingClassifier N hN E α)

/-- This pointed comparison isomorphism lies over the identity of `Spec ℂ`. -/
theorem complexFullMarkingNativeIso_hom_baseHom :
    (complexFullMarkingNativeIso N hN E α).hom.baseHom = 𝟙 (Spec (.of ℂ)) := rfl

/-- The actual full-level marking transports back to the original marking. -/
theorem complexFullMarkingNativeIso_level :
    (gammaFullNaiveProblem (.of ℂ) N).map
      (complexFullMarkingNativeIso N hN E α).hom.op
      (fullComplexPointLevel N hN (fullComplexSchemePointOfMarking N hN E α)) = α := by
  let r := xFullNaiveRepr (R := .of ℂ) N hN (complexLevelIsUnit N)
  change (gammaFullNaiveProblem (.of ℂ) N).map
    (EllObj.toPullbackAlong (fullMarkingClassifier N hN E α)).op
    (r.homEquiv ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).pullbackAlongπ
      (fullMarkingClassifier N hN E α).baseHom)) = α
  rw [← r.homEquiv_comp, EllObj.toPullbackAlong_pullbackAlongπ]
  exact r.homEquiv.apply_symm_apply α

/-- The classifier's actual coarse source-j morphism computes the given curve's j morphism. -/
theorem yZeroComplexSchemePointOfMarking_comp_sourceJ :
    (yZeroComplexSchemePointOfMarking N hN E α).val ≫
      yZeroSourceJ (R := .of ℂ) N hN (complexLevelIsUnit N) = jMap (complexEllObj E) := by
  change (yZeroComplexSchemePointOfFull N hN
    (fullComplexSchemePointOfMarking N hN E α)).val ≫ _ = _
  rw [yZeroComplexSchemePointOfFull_comp_sourceJ]
  have h := jMap_naturality (complexFullMarkingNativeIso N hN E α).hom
  rw [complexFullMarkingNativeIso_hom_baseHom] at h
  let jNative : Spec (.of ℂ) ⟶ Spec (.of (Polynomial ℂ)) :=
    jMap (fullComplexPointEllObj N hN (fullComplexSchemePointOfMarking N hN E α))
  let jGiven : Spec (.of ℂ) ⟶ Spec (.of (Polynomial ℂ)) := jMap (complexEllObj E)
  change 𝟙 (Spec (.of ℂ)) ≫ jNative = jGiven at h
  change jNative = jGiven
  exact (Category.id_comp jNative).symm.trans h

/-- The actual coarse source-j value is the Weierstrass j of the given elliptic curve. -/
theorem yZeroComplexSourceJValue_of_marking :
    yZeroComplexSourceJValue N hN (yZeroComplexSchemePointOfMarking N hN E α) =
      (fieldWeierstrassModel E.toEllipticCurveGeom).j := by
  change yZeroComplexSourceJValue N hN (yZeroComplexSchemePointOfFull N hN
    (fullComplexSchemePointOfMarking N hN E α)) = _
  rw [yZeroComplexSourceJValue_of_full]
  let G : EllipticCurveGeom (Spec (.of ℂ)) :=
    (fullComplexPointEllObj N hN
      (fullComplexSchemePointOfMarking N hN E α)).curve.toEllipticCurveGeom
  change (Scheme.ΓSpecIso (.of ℂ)).hom.hom (jSection G) = _
  let u := (complexFullMarkingNativeIso N hN E α).hom
  have h := jSection_naturality u.baseHom u.top u.isPullback u.zero_w
  change jSection G = jSection E.toEllipticCurveGeom at h
  exact (congrArg (Scheme.ΓSpecIso (.of ℂ)).hom.hom h).trans
    (fieldWeierstrassModel_j E.toEllipticCurveGeom).symm

/-- Every given native elliptic curve occurs at an actual coarse point with its source-j. -/
theorem exists_yZeroComplexSchemePoint_sourceJ_eq :
    ∃ p : yZeroComplexSchemePoint N hN,
      yZeroComplexSourceJValue N hN p = (fieldWeierstrassModel E.toEllipticCurveGeom).j := by
  obtain ⟨β⟩ := nonempty_complexFullMarking N E
  exact ⟨yZeroComplexSchemePointOfMarking N hN E β,
    yZeroComplexSourceJValue_of_marking N hN E β⟩

#print axioms ModularCurves.exists_isNaiveFullLevel_of_isAlgClosed
#print axioms nonempty_complexFullMarking
#print axioms fullComplexSchemePointOfMarking
#print axioms yZeroComplexSchemePointOfMarking
#print axioms complexFullMarkingNativeIso
#print axioms complexFullMarkingNativeIso_level
#print axioms yZeroComplexSchemePointOfMarking_comp_sourceJ
#print axioms yZeroComplexSourceJValue_of_marking
#print axioms exists_yZeroComplexSchemePoint_sourceJ_eq

/-- Raw marked-section input at level three uses the same actual classifier API. -/
example (E : ModularCurves.EllipticCurve (Spec (.of ℂ)))
    (P Q : E.Section) (h : E.IsNaiveFullLevel 3 P Q) :
    yZeroComplexSourceJValue 3 (by decide)
      (yZeroComplexSchemePointOfMarking 3 (by decide) E ⟨(P, Q), h⟩) =
        (fieldWeierstrassModel E.toEllipticCurveGeom).j :=
  yZeroComplexSourceJValue_of_marking 3 (by decide) E ⟨(P, Q), h⟩

example (E : ModularCurves.EllipticCurve (Spec (.of ℂ))) :
    ∃ p : yZeroComplexSchemePoint 3 (by decide),
      yZeroComplexSourceJValue 3 (by decide) p =
        (fieldWeierstrassModel E.toEllipticCurveGeom).j :=
  exists_yZeroComplexSchemePoint_sourceJ_eq 3 (by decide) E

end ModularPolynomialCurveTest.AINTLIB
