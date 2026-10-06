/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseInvariantSpec
public import AINTLIBDrafts.YZeroCoarseJ

/-!
# The regular source-j coordinate in the actual `YZeroCoarse` invariant ring

The polynomial map here lands in fixed regular sections on the actual full-level scheme.
Its composition with the inclusion is exactly the universal curve's j polynomial map.
Neither injectivity of that map nor connectedness of the full-level scheme is assumed.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry ModularCurves.YZeroCoarseJ

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

variable {R : CommRingCat.{u}} (N : ℕ) [NeZero N]
variable (hN : 3 ≤ (N : ℤ)) (hinv : IsUnit (N : R))

/-- Pulling the j-line coordinates back to regular sections of the actual coarse curve. -/
def yZeroSourceJSections : CommRingCat.of (Polynomial R) ⟶
    Γ(ModularCurves.YZeroCoarse (R := R) N hN hinv, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial R))).inv ≫ (yZeroSourceJ N hN hinv).appTop

/-- The descended source-j polynomial map recovers the literal fine j polynomial map. -/
theorem yZeroSourceJSections_comp_yZeroPr :
    yZeroSourceJSections N hN hinv ≫ (yZeroPr N hN hinv).appTop =
      CommRingCat.ofHom (jPolynomialHom (fullObject N hN hinv)) := by
  rw [yZeroSourceJSections, Category.assoc, ← Scheme.Hom.comp_appTop,
    yZeroPr_comp_yZeroSourceJ]
  exact jMap_pullback_hom (fullObject N hN hinv)

/-- The explicit polynomial map to Borel-invariant regular sections. -/
def yZeroJPolynomial : CommRingCat.of (Polynomial R) ⟶ yZeroInvariantRing N hN hinv :=
  yZeroSourceJSections N hN hinv ≫ (yZeroSectionsIso N hN hinv).hom

/-- The same polynomial map in the ring-hom API. -/
def yZeroJPolynomialHom : Polynomial R →+* yZeroInvariantRing N hN hinv :=
  (yZeroJPolynomial N hN hinv).hom

theorem yZeroJPolynomial_comp_inclusion :
    yZeroJPolynomial N hN hinv ≫ yZeroInvariantRingι N hN hinv =
      CommRingCat.ofHom (jPolynomialHom (fullObject N hN hinv)) := by
  rw [yZeroJPolynomial, Category.assoc, yZeroSectionsIso_hom_comp_inclusion,
    yZeroSourceJSections_comp_yZeroPr]

theorem yZeroJPolynomialHom_comp_inclusion :
    (yZeroInvariantRingι N hN hinv).hom.comp (yZeroJPolynomialHom N hN hinv) =
      jPolynomialHom (fullObject N hN hinv) :=
  congrArg (fun φ ↦ φ.hom) (yZeroJPolynomial_comp_inclusion N hN hinv)

/-- The upstairs universal source-j section as a genuine Borel-invariant section. -/
def fineJInvariant : yZeroInvariantRing N hN hinv := by
  letI : MulSemiringAction (ModularCurves.borel N) ↑Γ((fullObject N hN hinv).base, ⊤) :=
    (borelAction N hN hinv).gammaMulSemiringAction
      (show (borelAction N hN hinv).IsStableOpen (⊤ : (fullObject N hN hinv).base.Opens)
        from (borelAction N hN hinv).isStableOpen_preimage (fullObject N hN hinv).structMap
          (borelAction_over N hN hinv) (⊤ : (Spec R).Opens))
  refine ⟨jSection (fullObject N hN hinv).curve.toEllipticCurveGeom, ?_⟩
  intro g
  let a := (borelAction N hN hinv).hom g
  change (a.appLE ⊤ (a ⁻¹ᵁ ⊤) le_rfl).hom
    (jSection (fullObject N hN hinv).curve.toEllipticCurveGeom) = _
  rw [a.appLE_eq_app]
  exact action_jSection (ModularCurves.xFullNaiveRepr (R := R) N hN hinv)
    (ModularCurves.gammaHAut R N (ModularCurves.borel N)) g

/-- The polynomial variable is exactly the Borel-invariant source-j section upstairs. -/
theorem yZeroJPolynomialHom_X :
    yZeroJPolynomialHom N hN hinv Polynomial.X = fineJInvariant N hN hinv := by
  apply Subtype.ext
  change (yZeroInvariantRingι N hN hinv).hom
    (yZeroJPolynomialHom N hN hinv Polynomial.X) =
      jSection (fullObject N hN hinv).curve.toEllipticCurveGeom
  have h := DFunLike.congr_fun (yZeroJPolynomialHom_comp_inclusion N hN hinv)
    Polynomial.X
  simpa only [RingHom.comp_apply, jPolynomialHom, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X] using h

/-- The section-ring isomorphism sends the actual coarse j section to fine invariant j. -/
theorem yZeroSectionsIso_sourceJ_X :
    (yZeroSectionsIso N hN hinv).hom
      ((yZeroSourceJSections N hN hinv).hom Polynomial.X) = fineJInvariant N hN hinv :=
  yZeroJPolynomialHom_X N hN hinv

/-- Constants pulled back along the actual coarse structure map. -/
def yZeroCoefficientSections : R ⟶ Γ(ModularCurves.YZeroCoarse (R := R) N hN hinv, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ (yZeroStruct N hN hinv).appTop

/-- The invariant-ring coefficient map coming from the actual coarse structure morphism. -/
def yZeroInvariantCoefficients : R ⟶ yZeroInvariantRing N hN hinv :=
  yZeroCoefficientSections N hN hinv ≫ (yZeroSectionsIso N hN hinv).hom

/-- The section-ring identification respects constants from the original base. -/
theorem yZeroInvariantCoefficients_comp_inclusion :
    yZeroInvariantCoefficients N hN hinv ≫ yZeroInvariantRingι N hN hinv =
      CommRingCat.ofHom (coeffHom (fullObject N hN hinv)) := by
  rw [yZeroInvariantCoefficients, Category.assoc, yZeroSectionsIso_hom_comp_inclusion,
    yZeroCoefficientSections, Category.assoc, ← Scheme.Hom.comp_appTop,
    yZeroPr_comp_yZeroStruct]
  rfl

/-- Polynomial constants agree with the invariant-ring coefficient map. -/
theorem yZeroJPolynomial_C :
    CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫ yZeroJPolynomial N hN hinv =
      yZeroInvariantCoefficients N hN hinv := by
  have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (Polynomial R))).inv =
        (Scheme.ΓSpecIso R).inv ≫ jLineBase.appTop :=
    Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  have hsections : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
      yZeroSourceJSections N hN hinv = yZeroCoefficientSections N hN hinv := by
    rw [yZeroSourceJSections, ← Category.assoc, h, Category.assoc,
      ← Scheme.Hom.comp_appTop, yZeroSourceJ_comp_base]
    rfl
  rw [yZeroJPolynomial, yZeroInvariantCoefficients, ← Category.assoc, hsections]

/-- The invariant-spectrum identification is an isomorphism over the original base. -/
theorem yZeroInvariantSpecIso_hom_comp_base :
    (yZeroInvariantSpecIso N hN hinv).hom ≫
      Spec.map (yZeroInvariantCoefficients N hN hinv) = yZeroStruct N hN hinv := by
  have hfirst : yZeroPr N hN hinv ≫
      ((yZeroInvariantSpecIso N hN hinv).hom ≫
        Spec.map (yZeroInvariantCoefficients N hN hinv)) =
      (fullObject N hN hinv).structMap := by
    rw [← Category.assoc, yZeroPr_comp_invariantSpecIso_hom, Category.assoc,
      ← Spec.map_comp, yZeroInvariantCoefficients_comp_inclusion]
    change (fullObject N hN hinv).base.toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ (fullObject N hN hinv).structMap.appTop) = _
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hex := (ModularCurves.xFullNaiveRepr (R := R) N hN hinv).coarsePr_existsUnique_lift
    (ModularCurves.gammaHAut R N (ModularCurves.borel N))
    (fullObject N hN hinv).structMap
    ((ModularCurves.xFullNaiveRepr (R := R) N hN hinv).baseSchemeAction_over
      (ModularCurves.gammaHAut R N (ModularCurves.borel N)))
  exact (hex.choose_spec.2 _ hfirst).trans
    (hex.choose_spec.2 _ (yZeroPr_comp_yZeroStruct N hN hinv)).symm

/-- Under the actual invariant-spectrum identification, the source-j map is its polynomial map. -/
theorem yZeroInvariantSpecIso_hom_comp_sourceJ :
    (yZeroInvariantSpecIso N hN hinv).hom ≫ Spec.map (yZeroJPolynomial N hN hinv) =
      yZeroSourceJ N hN hinv := by
  have hfirst : yZeroPr N hN hinv ≫
      ((yZeroInvariantSpecIso N hN hinv).hom ≫ Spec.map (yZeroJPolynomial N hN hinv)) =
      jMap (fullObject N hN hinv) := by
    rw [← Category.assoc, yZeroPr_comp_invariantSpecIso_hom, Category.assoc,
      ← Spec.map_comp, yZeroJPolynomial_comp_inclusion]
    rfl
  have hex := (ModularCurves.xFullNaiveRepr (R := R) N hN hinv).coarsePr_existsUnique_lift
    (ModularCurves.gammaHAut R N (ModularCurves.borel N)) (jMap (fullObject N hN hinv))
    (action_comp_jMap (ModularCurves.xFullNaiveRepr (R := R) N hN hinv)
      (ModularCurves.gammaHAut R N (ModularCurves.borel N)))
  exact (hex.choose_spec.2 _ hfirst).trans
    (hex.choose_spec.2 _ (yZeroPr_comp_yZeroSourceJ N hN hinv)).symm

#print axioms yZeroJPolynomial_comp_inclusion
#print axioms yZeroJPolynomialHom_X
#print axioms yZeroSectionsIso_sourceJ_X
#print axioms yZeroInvariantCoefficients_comp_inclusion
#print axioms yZeroJPolynomial_C
#print axioms yZeroInvariantSpecIso_hom_comp_base
#print axioms yZeroInvariantSpecIso_hom_comp_sourceJ

end ModularPolynomialCurveTest.AINTLIB
