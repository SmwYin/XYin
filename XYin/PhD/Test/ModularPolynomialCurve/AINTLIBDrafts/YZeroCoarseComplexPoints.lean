/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.ComplexPointSeparation
public import AINTLIBDrafts.YZeroCoarseReduced
public import AINTLIBDrafts.YZeroCoarseJInvariants

/-!
# Complex points detect actual `YZeroCoarse` invariant sections

Both hypotheses of the point-separation theorem are proved for the actual Borel invariant
ring: finite type and reducedness. Its scalar algebra is the one induced by the actual
coarse structure morphism. No modular-polynomial equation is assumed or encoded here.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ModularCurves.YZeroCoarseJ

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

variable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))

local instance complexPointsInvariantAlgebra : Algebra ℂ
    (yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)) :=
  yZeroInvariantAlgebra (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)

/-- Complex algebra points of the actual Borel invariant coordinate ring. -/
abbrev yZeroComplexAlgebraPoint :=
  yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N) →ₐ[ℂ] ℂ

/-- Actual complex-valued scheme points of `YZeroCoarse` over `Spec ℂ`. -/
abbrev yZeroComplexSchemePoint :=
  {p : Spec (.of ℂ) ⟶ ModularCurves.YZeroCoarse (R := .of ℂ) N hN (complexLevelIsUnit N) //
    p ≫ yZeroStruct (R := .of ℂ) N hN (complexLevelIsUnit N) = 𝟙 (Spec (.of ℂ))}

/-- An invariant-ring algebra point gives a point of the actual coarse scheme. -/
def yZeroComplexSchemePointOfAlgebra (φ : yZeroComplexAlgebraPoint N hN) :
    yZeroComplexSchemePoint N hN :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      (yZeroInvariantSpecIso (R := .of ℂ) N hN (complexLevelIsUnit N)).inv, by
    rw [Category.assoc, ← yZeroInvariantSpecIso_hom_comp_base,
      Iso.inv_hom_id_assoc, ← Spec.map_comp, Spec.map_eq_id]
    apply CommRingCat.hom_ext
    ext z
    exact φ.commutes z⟩

/-- The actual base triangle makes the corresponding invariant-ring hom complex-linear. -/
def yZeroComplexAlgebraPointOfScheme (p : yZeroComplexSchemePoint N hN) :
    yZeroComplexAlgebraPoint N hN where
  toRingHom := (Spec.preimage
    (p.val ≫ (yZeroInvariantSpecIso (R := .of ℂ) N hN (complexLevelIsUnit N)).hom)).hom
  commutes' z := by
    have htriangle : (p.val ≫
        (yZeroInvariantSpecIso (R := .of ℂ) N hN (complexLevelIsUnit N)).hom) ≫
          Spec.map (yZeroInvariantCoefficients (R := .of ℂ) N hN (complexLevelIsUnit N)) =
        𝟙 (Spec (.of ℂ)) := by
      rw [Category.assoc, yZeroInvariantSpecIso_hom_comp_base]
      exact p.property
    have h := congrArg Spec.preimage htriangle
    simp only [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id] at h
    exact congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ ↦ f z) h

/-- Actual complex scheme points agree with complex algebra points of the invariant ring. -/
def yZeroComplexAlgebraSchemePointEquiv :
    yZeroComplexAlgebraPoint N hN ≃ yZeroComplexSchemePoint N hN where
  toFun := yZeroComplexSchemePointOfAlgebra N hN
  invFun := yZeroComplexAlgebraPointOfScheme N hN
  left_inv φ := by
    apply AlgHom.ext
    intro x
    change (Spec.preimage ((Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      (yZeroInvariantSpecIso (R := .of ℂ) N hN (complexLevelIsUnit N)).inv) ≫
      (yZeroInvariantSpecIso (R := .of ℂ) N hN (complexLevelIsUnit N)).hom)).hom x = φ x
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Spec.preimage_map]
    rfl
  right_inv p := by
    apply Subtype.ext
    change Spec.map (Spec.preimage (p.val ≫
      (yZeroInvariantSpecIso (R := .of ℂ) N hN (complexLevelIsUnit N)).hom)) ≫
      (yZeroInvariantSpecIso (R := .of ℂ) N hN (complexLevelIsUnit N)).inv = p.val
    rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The source-j coordinate of an actual complex scheme point. -/
def yZeroComplexSourceJValue (p : yZeroComplexSchemePoint N hN) : ℂ :=
  (Spec.preimage (p.val ≫ yZeroSourceJ (R := .of ℂ) N hN (complexLevelIsUnit N))).hom
    Polynomial.X

/-- Evaluating the actual source-j morphism agrees with evaluating its invariant section. -/
theorem yZeroComplexSourceJValue_of_algebra (φ : yZeroComplexAlgebraPoint N hN) :
    yZeroComplexSourceJValue N hN (yZeroComplexSchemePointOfAlgebra N hN φ) =
      φ (fineJInvariant (R := .of ℂ) N hN (complexLevelIsUnit N)) := by
  unfold yZeroComplexSourceJValue
  rw [← yZeroInvariantSpecIso_hom_comp_sourceJ]
  change (Spec.preimage ((Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    (yZeroInvariantSpecIso (R := .of ℂ) N hN (complexLevelIsUnit N)).inv) ≫
    ((yZeroInvariantSpecIso (R := .of ℂ) N hN (complexLevelIsUnit N)).hom ≫
      Spec.map (yZeroJPolynomial (R := .of ℂ) N hN (complexLevelIsUnit N))))).hom
    Polynomial.X = _
  rw [Category.assoc, Iso.inv_hom_id_assoc, Spec.preimage_comp,
    Spec.preimage_map, Spec.preimage_map]
  exact congrArg φ (yZeroJPolynomialHom_X N hN (complexLevelIsUnit N))

/-- The same coordinate formula for an arbitrary actual complex scheme point. -/
theorem yZeroComplexSourceJValue_eq (p : yZeroComplexSchemePoint N hN) :
    yZeroComplexSourceJValue N hN p =
      yZeroComplexAlgebraPointOfScheme N hN p
        (fineJInvariant (R := .of ℂ) N hN (complexLevelIsUnit N)) := by
  have hpoint : yZeroComplexSchemePointOfAlgebra N hN
      (yZeroComplexAlgebraPointOfScheme N hN p) = p :=
    (yZeroComplexAlgebraSchemePointEquiv N hN).right_inv p
  simpa only [hpoint] using
    yZeroComplexSourceJValue_of_algebra N hN (yZeroComplexAlgebraPointOfScheme N hN p)

/-- Complex algebra points detect zero in the actual coarse invariant coordinate ring. -/
theorem yZeroComplexInvariant_eq_zero_of_forall_algHom_eq_zero
    (x : yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N))
    (h : ∀ φ : yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)
      →ₐ[ℂ] ℂ, φ x = 0) : x = 0 := by
  have : Algebra.FiniteType ℂ
      (yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)) :=
    yZeroComplexInvariantRing_finiteType N hN
  have : _root_.IsReduced
      (yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)) :=
    yZeroComplexInvariantRing_isReduced N hN
  exact eq_zero_of_forall_complex_algHom_eq_zero x h

/-- Actual coarse invariant regular functions are determined by their values at complex points. -/
theorem yZeroComplexInvariant_eq_of_forall_algHom_eq
    (x y : yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N))
    (h : ∀ φ : yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)
      →ₐ[ℂ] ℂ, φ x = φ y) : x = y := by
  apply sub_eq_zero.mp
  apply yZeroComplexInvariant_eq_zero_of_forall_algHom_eq_zero
  intro φ
  simp only [map_sub, h φ, sub_self]

#print axioms yZeroComplexInvariant_eq_zero_of_forall_algHom_eq_zero
#print axioms yZeroComplexInvariant_eq_of_forall_algHom_eq
#print axioms yZeroComplexAlgebraSchemePointEquiv
#print axioms yZeroComplexSourceJValue_of_algebra
#print axioms yZeroComplexSourceJValue_eq

example (φ : yZeroComplexAlgebraPoint 3 (by decide)) :
    yZeroComplexAlgebraPointOfScheme 3 (by decide)
      (yZeroComplexSchemePointOfAlgebra 3 (by decide) φ) = φ :=
  (yZeroComplexAlgebraSchemePointEquiv 3 (by decide)).left_inv φ

example (p : yZeroComplexSchemePoint 3 (by decide)) :
    yZeroComplexSchemePointOfAlgebra 3 (by decide)
      (yZeroComplexAlgebraPointOfScheme 3 (by decide) p) = p :=
  (yZeroComplexAlgebraSchemePointEquiv 3 (by decide)).right_inv p

end ModularPolynomialCurveTest.AINTLIB
