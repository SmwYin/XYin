/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.Moduli.CoarseSpace

/-!
# The actual AINTLIB `YZeroCoarse` as an invariant affine spectrum

This file targets the pinned AINTLIB environment, rather than the local XYin toolchain.
The quotient is AINTLIB's actual `YZeroCoarse`; its ring comes from sections of the actual
representing full-level scheme. No domain hypothesis is imposed on that full-level scheme.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

namespace AffineInvariantQuotient

variable {G : Type*} [Group G] [Finite G] {Z S : Scheme.{u}}
variable (σ : SchemeAction G Z) (f : Z ⟶ S)
variable (hover : ∀ g : G, σ.hom g ≫ f = f)
variable [IsAffineHom f] [IsAffine S]

/-- The actual fixed subring of global sections, using the action over the structure map. -/
def invariantSections : CommRingCat.{u} :=
  letI : MulSemiringAction G ↑Γ(Z, ⊤) := σ.gammaMulSemiringAction
    (show σ.IsStableOpen (⊤ : Z.Opens) from σ.isStableOpen_preimage f hover (⊤ : S.Opens))
  .of (FixedPoints.subalgebra ℤ ↑Γ(Z, ⊤) G)

/-- The inclusion of invariant sections in all global sections. -/
def invariantSectionsι : invariantSections σ f hover ⟶ Γ(Z, ⊤) :=
  letI : MulSemiringAction G ↑Γ(Z, ⊤) := σ.gammaMulSemiringAction
    (show σ.IsStableOpen (⊤ : Z.Opens) from σ.isStableOpen_preimage f hover (⊤ : S.Opens))
  CommRingCat.ofHom (FixedPoints.subalgebra ℤ ↑Γ(Z, ⊤) G).val.toRingHom

/-- The top affine chart of the actual relative quotient. -/
def topChartι : Spec (invariantSections σ f hover) ⟶ σ.relQuotient f hover :=
  σ.relQuotientChartι f hover ⟨⊤, isAffineOpen_top S⟩

instance : IsOpenImmersion (topChartι σ f hover) :=
  (σ.invariantsGlueData f hover).cover.map_prop ⟨⊤, isAffineOpen_top S⟩

theorem topChartι_opensRange : (topChartι σ f hover).opensRange = ⊤ := by
  have h := σ.relQuotientStruct_preimage f hover ⟨⊤, isAffineOpen_top S⟩
  exact h.symm

instance : IsIso (topChartι σ f hover) :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _ (topChartι_opensRange σ f hover)

/-- The top invariant chart covers the whole quotient over an affine base. -/
def invariantSpecIso : σ.relQuotient f hover ≅ Spec (invariantSections σ f hover) :=
  (asIso (topChartι σ f hover)).symm

instance : IsAffine (σ.relQuotient f hover) :=
  IsAffine.of_isIso (invariantSpecIso σ f hover).hom

/-- Compatibility of the actual quotient projection with the invariant-ring inclusion. -/
theorem relQuotientπ_eq :
    σ.relQuotientπ f hover =
      Z.toSpecΓ ≫ Spec.map (invariantSectionsι σ f hover) ≫ topChartι σ f hover := by
  rw [← cancel_epi Z.topIso.hom]
  have h := σ.ι_relQuotientπ f hover ⟨⊤, isAffineOpen_top S⟩
  change (⊤ : Z.Opens).ι ≫ σ.relQuotientπ f hover =
    (⊤ : Z.Opens).toSpecΓ ≫ Spec.map (invariantSectionsι σ f hover) ≫
      topChartι σ f hover at h
  simpa only [Scheme.Opens.toSpecΓ_top, Scheme.topIso_hom, Category.assoc] using h

theorem relQuotientπ_comp_invariantSpecIso_hom :
    σ.relQuotientπ f hover ≫ (invariantSpecIso σ f hover).hom =
      Z.toSpecΓ ≫ Spec.map (invariantSectionsι σ f hover) := by
  rw [relQuotientπ_eq]
  simp only [Category.assoc, invariantSpecIso, Iso.symm_hom, asIso_inv,
    IsIso.hom_inv_id, Category.comp_id]

/-- Global sections of the actual quotient identify with invariant sections upstairs. -/
def sectionsIso : Γ(σ.relQuotient f hover, ⊤) ≅ invariantSections σ f hover :=
  (Scheme.Γ.mapIso (invariantSpecIso σ f hover).op).symm ≪≫
    Scheme.ΓSpecIso (invariantSections σ f hover)

/-- Under the section-ring identification, projection pullback is the literal inclusion. -/
theorem sectionsIso_hom_comp_inclusion :
    (sectionsIso σ f hover).hom ≫ invariantSectionsι σ f hover =
      (σ.relQuotientπ f hover).appTop := by
  rw [relQuotientπ_eq, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    Scheme.toSpecΓ_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
  change ((invariantSpecIso σ f hover).inv.appTop ≫
    (Scheme.ΓSpecIso (invariantSections σ f hover)).hom) ≫
      invariantSectionsι σ f hover = _
  simp only [Category.assoc, invariantSpecIso, Iso.symm_inv, asIso_hom]

end AffineInvariantQuotient

variable {R : CommRingCat.{u}} (N : ℕ) [NeZero N]
variable (hN : 3 ≤ (N : ℤ)) (hinv : IsUnit (N : R))

/-- The actual representing full-level object used in `YZeroCoarse`. -/
abbrev fullObject : ModularCurves.EllObj R :=
  ModularCurves.xFullNaive (R := R) N hN hinv

instance fullObject_structMap_isAffineHom :
    IsAffineHom (fullObject N hN hinv).structMap :=
  ModularCurves.ModuliProblem.gammaFullNaive_isAffineHom_structMap N hN hinv
    (ModularCurves.xFullNaiveRepr (R := R) N hN hinv)

instance fullObject_base_isAffine : IsAffine (fullObject N hN hinv).base :=
  isAffine_of_isAffineHom (fullObject N hN hinv).structMap

/-- The actual Borel action transported from the full-level moduli problem. -/
def borelAction : SchemeAction (ModularCurves.borel N) (fullObject N hN hinv).base :=
  (ModularCurves.xFullNaiveRepr (R := R) N hN hinv).baseSchemeAction
    (ModularCurves.gammaHAut R N (ModularCurves.borel N))

theorem borelAction_over (g : ModularCurves.borel N) :
    (borelAction N hN hinv).hom g ≫ (fullObject N hN hinv).structMap =
      (fullObject N hN hinv).structMap :=
  (ModularCurves.xFullNaiveRepr (R := R) N hN hinv).baseSchemeAction_over
    (ModularCurves.gammaHAut R N (ModularCurves.borel N)) g

/-- The invariant ring of the actual full-level scheme for the actual Borel action. -/
def yZeroInvariantRing : CommRingCat.{u} :=
  AffineInvariantQuotient.invariantSections (borelAction N hN hinv)
    (fullObject N hN hinv).structMap (borelAction_over N hN hinv)

/-- The actual projection `Y(N) ⟶ YZeroCoarse`, using the chosen representing object. -/
def yZeroPr : (fullObject N hN hinv).base ⟶
    ModularCurves.YZeroCoarse (R := R) N hN hinv :=
  (ModularCurves.xFullNaiveRepr (R := R) N hN hinv).coarsePr
    (ModularCurves.gammaHAut R N (ModularCurves.borel N))

/-- The actual structure map of `YZeroCoarse` to the original base. -/
def yZeroStruct : ModularCurves.YZeroCoarse (R := R) N hN hinv ⟶ Spec R :=
  (ModularCurves.xFullNaiveRepr (R := R) N hN hinv).coarseStruct
    (ModularCurves.gammaHAut R N (ModularCurves.borel N))

theorem yZeroPr_comp_yZeroStruct :
    yZeroPr N hN hinv ≫ yZeroStruct N hN hinv = (fullObject N hN hinv).structMap :=
  (ModularCurves.xFullNaiveRepr (R := R) N hN hinv).coarsePr_comp_coarseStruct
    (ModularCurves.gammaHAut R N (ModularCurves.borel N))

/-- A concrete affine-spectrum identification of the actual AINTLIB `YZeroCoarse`. -/
def yZeroInvariantSpecIso :
    ModularCurves.YZeroCoarse (R := R) N hN hinv ≅ Spec (yZeroInvariantRing N hN hinv) :=
  AffineInvariantQuotient.invariantSpecIso (borelAction N hN hinv)
    (fullObject N hN hinv).structMap (borelAction_over N hN hinv)

instance yZeroCoarse_isAffine : IsAffine (ModularCurves.YZeroCoarse (R := R) N hN hinv) :=
  IsAffine.of_isIso (yZeroInvariantSpecIso N hN hinv).hom

def yZeroInvariantRingι : yZeroInvariantRing N hN hinv ⟶
    Γ((fullObject N hN hinv).base, ⊤) :=
  AffineInvariantQuotient.invariantSectionsι (borelAction N hN hinv)
    (fullObject N hN hinv).structMap (borelAction_over N hN hinv)

theorem yZeroPr_comp_invariantSpecIso_hom :
    yZeroPr N hN hinv ≫ (yZeroInvariantSpecIso N hN hinv).hom =
      (fullObject N hN hinv).base.toSpecΓ ≫ Spec.map (yZeroInvariantRingι N hN hinv) :=
  AffineInvariantQuotient.relQuotientπ_comp_invariantSpecIso_hom
    (borelAction N hN hinv) (fullObject N hN hinv).structMap
    (borelAction_over N hN hinv)

def yZeroSectionsIso : Γ(ModularCurves.YZeroCoarse (R := R) N hN hinv, ⊤) ≅
    yZeroInvariantRing N hN hinv :=
  AffineInvariantQuotient.sectionsIso (borelAction N hN hinv)
    (fullObject N hN hinv).structMap (borelAction_over N hN hinv)

theorem yZeroSectionsIso_hom_comp_inclusion :
    (yZeroSectionsIso N hN hinv).hom ≫ yZeroInvariantRingι N hN hinv =
      (yZeroPr N hN hinv).appTop :=
  AffineInvariantQuotient.sectionsIso_hom_comp_inclusion
    (borelAction N hN hinv) (fullObject N hN hinv).structMap
    (borelAction_over N hN hinv)

#print axioms AffineInvariantQuotient.relQuotientπ_comp_invariantSpecIso_hom
#print axioms AffineInvariantQuotient.sectionsIso_hom_comp_inclusion
#print axioms yZeroInvariantSpecIso
#print axioms yZeroPr_comp_invariantSpecIso_hom
#print axioms yZeroSectionsIso_hom_comp_inclusion

end ModularPolynomialCurveTest.AINTLIB
