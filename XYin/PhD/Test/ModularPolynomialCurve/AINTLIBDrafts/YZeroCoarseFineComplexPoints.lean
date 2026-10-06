/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarsePointLifting
public import AINTLIBDrafts.YZeroCoarseComplexPoints
public import AINTLIBDrafts.FieldGeometricJ

/-!
# Actual coarse complex points lift to the universal full-level elliptic curve

The lift is through the literal AINTLIB projection. Pullback of its chosen universal
elliptic curve supplies a native full-level elliptic object over `Spec ℂ`. Its source-j
morphism agrees with the coarse source-j morphism. This uses no quotient curve or analytic
uniformization hypothesis.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ModularCurves.YZeroCoarseJ

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

variable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))

local instance fineComplexPointsFullAlgebra : Algebra ℂ
    Γ((fullObject (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) :=
  (fullCoefficientHom (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)).toAlgebra

local instance fineComplexPointsInvariantAlgebra : Algebra ℂ
    (yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)) :=
  yZeroInvariantAlgebra (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)

/-- Full-level points of the actual chosen representing scheme over `Spec ℂ`. -/
abbrev fullComplexSchemePoint :=
  {p : Spec (.of ℂ) ⟶ (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base //
    p ≫ (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).structMap =
      𝟙 (Spec (.of ℂ))}

/-- The canonical affine identification respects the actual fine coefficient map. -/
theorem fullObject_toSpecΓ_comp_coefficients :
    (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom
        (fullCoefficientHom (R := .of ℂ) N hN (complexLevelIsUnit N))) =
    (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).structMap := by
  change _ ≫ Spec.map ((Scheme.ΓSpecIso (.of ℂ)).inv ≫
    (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).structMap.appTop) = _
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- A fine coefficient algebra point gives an actual full-level scheme point. -/
def fullComplexSchemePointOfAlgebra (ψ : fullComplexAlgebraPoint N hN) :
    fullComplexSchemePoint N hN :=
  ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
    (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base.isoSpec.inv, by
    rw [← fullObject_toSpecΓ_comp_coefficients, Category.assoc,
      Scheme.isoSpec_inv_toSpecΓ_assoc, ← Spec.map_comp, Spec.map_eq_id]
    apply CommRingCat.hom_ext
    ext z
    exact ψ.commutes z⟩

/-- The actual fine base triangle makes the corresponding section-ring point complex-linear. -/
def fullComplexAlgebraPointOfScheme (p : fullComplexSchemePoint N hN) :
    fullComplexAlgebraPoint N hN where
  toRingHom := (Spec.preimage (p.val ≫
    (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base.toSpecΓ)).hom
  commutes' z := by
    have htriangle : (p.val ≫
        (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base.toSpecΓ) ≫
          Spec.map (CommRingCat.ofHom
            (fullCoefficientHom (R := .of ℂ) N hN (complexLevelIsUnit N))) =
        𝟙 (Spec (.of ℂ)) := by
      rw [Category.assoc, fullObject_toSpecΓ_comp_coefficients]
      exact p.property
    have h := congrArg Spec.preimage htriangle
    simp only [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id] at h
    exact congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ ↦ f z) h

/-- Fine coefficient algebra points agree with actual full-level complex scheme points. -/
def fullComplexAlgebraSchemePointEquiv :
    fullComplexAlgebraPoint N hN ≃ fullComplexSchemePoint N hN where
  toFun := fullComplexSchemePointOfAlgebra N hN
  invFun := fullComplexAlgebraPointOfScheme N hN
  left_inv ψ := by
    apply AlgHom.ext
    intro x
    have hmap : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base.isoSpec.inv) ≫
        (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base.toSpecΓ =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
      rw [Category.assoc, Scheme.isoSpec_inv_toSpecΓ]
      exact Category.comp_id (Spec.map (CommRingCat.ofHom ψ.toRingHom))
    change (Spec.preimage ((Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base.isoSpec.inv) ≫
      (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base.toSpecΓ)).hom x = ψ x
    rw [hmap, Spec.preimage_map]
    rfl
  right_inv p := by
    apply Subtype.ext
    change Spec.map (Spec.preimage (p.val ≫
      (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base.toSpecΓ)) ≫
      (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base.isoSpec.inv = p.val
    rw [Spec.map_preimage, Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

/-- The actual full-to-coarse projection sends points to points over the same base. -/
def yZeroComplexSchemePointOfFull (p : fullComplexSchemePoint N hN) :
    yZeroComplexSchemePoint N hN :=
  ⟨p.val ≫ yZeroPr (R := .of ℂ) N hN (complexLevelIsUnit N), by
    rw [Category.assoc, yZeroPr_comp_yZeroStruct]
    exact p.property⟩

/-- Scheme projection agrees with literal restriction along the invariant inclusion. -/
theorem fullComplexSchemePointOfAlgebra_comp_yZeroPr (ψ : fullComplexAlgebraPoint N hN) :
    yZeroComplexSchemePointOfFull N hN (fullComplexSchemePointOfAlgebra N hN ψ) =
      yZeroComplexSchemePointOfAlgebra N hN
        (ψ.comp (yZeroComplexInvariantInclusion N hN)) := by
  apply Subtype.ext
  apply (cancel_mono
    (yZeroInvariantSpecIso (R := .of ℂ) N hN (complexLevelIsUnit N)).hom).mp
  change ((Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
    (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base.isoSpec.inv) ≫
      yZeroPr (R := .of ℂ) N hN (complexLevelIsUnit N)) ≫ _ =
    (Spec.map (CommRingCat.ofHom
      (ψ.comp (yZeroComplexInvariantInclusion N hN)).toRingHom) ≫
      (yZeroInvariantSpecIso (R := .of ℂ) N hN (complexLevelIsUnit N)).inv) ≫ _
  rw [Category.assoc, yZeroPr_comp_invariantSpecIso_hom, Category.assoc,
    Scheme.isoSpec_inv_toSpecΓ_assoc, ← Spec.map_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Every actual coarse complex scheme point lifts through the actual full-level projection. -/
theorem yZeroComplexSchemePoint_lifts (p : yZeroComplexSchemePoint N hN) :
    ∃ q : fullComplexSchemePoint N hN, yZeroComplexSchemePointOfFull N hN q = p := by
  let φ := yZeroComplexAlgebraPointOfScheme N hN p
  obtain ⟨ψ, hψ⟩ := yZeroComplexAlgebraPoint_lifts N hN φ
  have hrestrict : ψ.comp (yZeroComplexInvariantInclusion N hN) = φ := by
    ext x
    exact DFunLike.congr_fun hψ x
  refine ⟨fullComplexSchemePointOfAlgebra N hN ψ, ?_⟩
  rw [fullComplexSchemePointOfAlgebra_comp_yZeroPr, hrestrict]
  exact (yZeroComplexAlgebraSchemePointEquiv N hN).right_inv p

/-- Pullback of the actual universal elliptic curve at an actual full-level point. -/
def fullComplexPointEllObj (p : fullComplexSchemePoint N hN) : ModularCurves.EllObj (.of ℂ) :=
  (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).pullbackAlong p.val

/-- The base of this pullback is literally `Spec ℂ`. -/
instance fullComplexPointEllObj_base_isAffine (p : fullComplexSchemePoint N hN) :
    IsAffine (fullComplexPointEllObj N hN p).base := by
  change IsAffine (Spec (.of ℂ))
  infer_instance

/-- The actual representing bijection supplies a full-level marking on this pullback. -/
def fullComplexPointLevel (p : fullComplexSchemePoint N hN) :
    (ModularCurves.gammaFullNaiveProblem (.of ℂ) N).obj
      (Opposite.op (fullComplexPointEllObj N hN p)) :=
  (ModularCurves.xFullNaiveRepr (R := .of ℂ) N hN (complexLevelIsUnit N)).homEquiv
    ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).pullbackAlongπ p.val)

/-- The marking is the pullback of the same chosen universal full-level marking. -/
theorem fullComplexPointLevel_eq_pullback (p : fullComplexSchemePoint N hN) :
    fullComplexPointLevel N hN p =
      (ModularCurves.gammaFullNaiveProblem (.of ℂ) N).map
        ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).pullbackAlongπ p.val).op
        ((ModularCurves.xFullNaiveRepr (R := .of ℂ) N hN (complexLevelIsUnit N)).homEquiv
          (𝟙 _)) :=
  (ModularCurves.xFullNaiveRepr (R := .of ℂ) N hN (complexLevelIsUnit N)).homEquiv_eq
    ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).pullbackAlongπ p.val)

/-- This elliptic object has the original complex base structure. -/
theorem fullComplexPointEllObj_structMap (p : fullComplexSchemePoint N hN) :
    (fullComplexPointEllObj N hN p).structMap = 𝟙 (Spec (.of ℂ)) :=
  p.property

/-- The native pullback elliptic curve computes the actual coarse source-j morphism. -/
theorem yZeroComplexSchemePointOfFull_comp_sourceJ (p : fullComplexSchemePoint N hN) :
    (yZeroComplexSchemePointOfFull N hN p).val ≫
      yZeroSourceJ (R := .of ℂ) N hN (complexLevelIsUnit N) =
      jMap (fullComplexPointEllObj N hN p) := by
  change (p.val ≫ yZeroPr (R := .of ℂ) N hN (complexLevelIsUnit N)) ≫ _ = _
  rw [Category.assoc, yZeroPr_comp_yZeroSourceJ]
  exact jMap_naturality (X' := fullComplexPointEllObj N hN p)
    ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).pullbackAlongπ p.val)

/-- The geometric source-j value of the native pullback elliptic curve. -/
def fullComplexPointJValue (p : fullComplexSchemePoint N hN) : ℂ :=
  (Scheme.ΓSpecIso (.of ℂ)).hom.hom
    (jSection (fullComplexPointEllObj N hN p).curve.toEllipticCurveGeom)

/-- The actual coarse point's source-j coordinate is its native elliptic curve's j value. -/
theorem yZeroComplexSourceJValue_of_full (p : fullComplexSchemePoint N hN) :
    yZeroComplexSourceJValue N hN (yZeroComplexSchemePointOfFull N hN p) =
      fullComplexPointJValue N hN p := by
  unfold yZeroComplexSourceJValue
  rw [yZeroComplexSchemePointOfFull_comp_sourceJ]
  let f : Spec (.of ℂ) ⟶ Spec (.of (Polynomial ℂ)) := jMap (fullComplexPointEllObj N hN p)
  change (Spec.preimage f).hom Polynomial.X = _
  have h₀ := Scheme.ΓSpecIso_inv_naturality (Spec.preimage f)
  rw [Spec.map_preimage] at h₀
  have h : Spec.preimage f =
      ((Scheme.ΓSpecIso (.of (Polynomial ℂ))).inv ≫ f.appTop) ≫
        (Scheme.ΓSpecIso (.of ℂ)).hom := by
    calc
      _ = (Spec.preimage f ≫ (Scheme.ΓSpecIso (.of ℂ)).inv) ≫
          (Scheme.ΓSpecIso (.of ℂ)).hom := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = _ := congrArg (· ≫ (Scheme.ΓSpecIso (.of ℂ)).hom) h₀
  rw [h]
  change (Scheme.ΓSpecIso (.of ℂ)).hom.hom
    ((((Scheme.ΓSpecIso (.of (Polynomial ℂ))).inv ≫ f.appTop).hom) Polynomial.X) = _
  have hX := jMap_pullback_X (fullComplexPointEllObj N hN p)
  change (((Scheme.ΓSpecIso (.of (Polynomial ℂ))).inv ≫ f.appTop).hom) Polynomial.X =
    jSection (fullComplexPointEllObj N hN p).curve.toEllipticCurveGeom at hX
  rw [hX]
  rfl

/-- A genuine Weierstrass model of the native curve obtained from its pointed presentation. -/
def fullComplexPointWeierstrassModel (p : fullComplexSchemePoint N hN) : WeierstrassCurve ℂ :=
  fieldWeierstrassModel (fullComplexPointEllObj N hN p).curve.toEllipticCurveGeom

instance fullComplexPointWeierstrassModel_isElliptic (p : fullComplexSchemePoint N hN) :
    (fullComplexPointWeierstrassModel N hN p).IsElliptic := by
  unfold fullComplexPointWeierstrassModel
  exact fieldWeierstrassModel_isElliptic (k := ℂ)
    (fullComplexPointEllObj N hN p).curve.toEllipticCurveGeom

/-- The coarse source-j value is the algebraic j of the native Weierstrass model. -/
theorem yZeroComplexSourceJValue_eq_weierstrassModel (p : fullComplexSchemePoint N hN) :
    yZeroComplexSourceJValue N hN (yZeroComplexSchemePointOfFull N hN p) =
      (fullComplexPointWeierstrassModel N hN p).j := by
  rw [yZeroComplexSourceJValue_of_full]
  exact (fieldWeierstrassModel_j
    (fullComplexPointEllObj N hN p).curve.toEllipticCurveGeom).symm

#print axioms fullComplexSchemePointOfAlgebra
#print axioms fullComplexAlgebraSchemePointEquiv
#print axioms fullComplexSchemePointOfAlgebra_comp_yZeroPr
#print axioms yZeroComplexSchemePoint_lifts
#print axioms fullComplexPointLevel
#print axioms fullComplexPointLevel_eq_pullback
#print axioms fullComplexPointEllObj_structMap
#print axioms yZeroComplexSchemePointOfFull_comp_sourceJ
#print axioms yZeroComplexSourceJValue_of_full
#print axioms fullComplexPointWeierstrassModel_isElliptic
#print axioms yZeroComplexSourceJValue_eq_weierstrassModel

example (p : yZeroComplexSchemePoint 3 (by decide)) :
    ∃ q : fullComplexSchemePoint 3 (by decide),
      yZeroComplexSchemePointOfFull 3 (by decide) q = p :=
  yZeroComplexSchemePoint_lifts 3 (by decide) p

end ModularPolynomialCurveTest.AINTLIB
