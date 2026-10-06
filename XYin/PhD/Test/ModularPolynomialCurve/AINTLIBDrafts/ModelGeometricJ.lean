/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.GeometricJ
public import ModularCurves.EllipticCurve.ModelRecord

/-!
# Geometric j of the actual projective Weierstrass model

The whole-base pointed presentation is the construction used by
`ModularCurves.locallyWeierstrass_projModel` in `EllipticCurve/Comparison.lean`.
It compares the projective model with its coefficient-ring base change using the actual
base-change square and zero-section compatibility. This explicit presentation computes
the global geometric j section over any commutative coefficient ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits ModularCurves ModularCurves.YZeroCoarseJ

noncomputable section

universe u

namespace ModularCurves.YZeroCoarseJ

variable {A : Type u} [CommRing A] (W : WeierstrassCurve A) [W.IsElliptic]

set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit whole-base presentation used by the projective model construction. -/
def modelTopPresentation : LocalPresentation (modelEllipticCurve W).toEllipticCurveGeom
    ⟨⊤, isAffineOpen_top _⟩ := by
  let S := Spec (CommRingCat.of A)
  letI : Algebra A ↑Γ(S, (⊤ : S.Opens)) :=
    (Scheme.ΓSpecIso (.of A)).inv.hom.toAlgebra
  have htop : IsIso (⊤ : S.Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  have hspec : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap A ↑Γ(S, (⊤ : S.Opens))))) := by
    have h : CommRingCat.ofHom (algebraMap A ↑Γ(S, (⊤ : S.Opens))) =
        (Scheme.ΓSpecIso (.of A)).inv := rfl
    rw [h]
    infer_instance
  have hfstTop : IsIso (pullback.fst (projModelπ W) (⊤ : S.Opens).ι) :=
    inferInstance
  have hfstSpec : IsIso (pullback.fst (projModelπ W) (Spec.map (CommRingCat.ofHom
      (algebraMap A ↑Γ(S, (⊤ : S.Opens)))))) := inferInstance
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) =
      S.isoSpec.inv := (Scheme.isoSpec_Spec_inv (.of A)).symm
  let eModel : pullback (projModelπ W) (⊤ : S.Opens).ι ≅
      projModel (W.map (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) :=
    (@asIso Scheme _ _ _ (pullback.fst (projModelπ W) (⊤ : S.Opens).ι) hfstTop) ≪≫
      (@asIso Scheme _ _ _ (pullback.fst (projModelπ W)
        (Spec.map (CommRingCat.ofHom
          (algebraMap A ↑Γ(S, (⊤ : S.Opens)))))) hfstSpec).symm ≪≫
      (isPullback_projModelBaseChange W).isoPullback.symm
  refine { W := W.map (algebraMap A ↑Γ(S, (⊤ : S.Opens)))
           elliptic := inferInstance
           e := eModel
           compat_π := ?_
           compat_zero := ?_ }
  · change eModel.hom ≫ projModelπ (W.map (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) =
      pullback.snd (projModelπ W) (⊤ : S.Opens).ι ≫ (isAffineOpen_top S).isoSpec.hom
    dsimp only [eModel]
    have hcrux : ∀ (h : (⊤ : S.Opens) ∈ S.affineOpens),
        (IsAffineOpen.isoSpec h).hom ≫ Spec.map (CommRingCat.ofHom
          (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) = (⊤ : S.Opens).ι := by
      exact fun h => hφ ▸ isoSpec_hom_comp_isoSpec_inv_top S h
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom
      (algebraMap A ↑Γ(S, (⊤ : S.Opens)))))]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
      IsPullback.isoPullback_inv_snd]
    conv_rhs => erw [hcrux]
    erw [← pullback.condition, IsIso.inv_hom_id_assoc]
    exact pullback.condition
  · have hzeroCond : ((⊤ : S.Opens).ι ≫ projModelZero W) ≫ projModelπ W =
        𝟙 (⊤ : S.Opens).toScheme ≫ (⊤ : S.Opens).ι := by
      rw [Category.assoc, projModelZero_projModelπ, Category.comp_id, Category.id_comp]
    change ((isAffineOpen_top S).isoSpec.inv ≫
      pullback.lift ((⊤ : S.Opens).ι ≫ projModelZero W) (𝟙 _) hzeroCond) ≫ eModel.hom =
        projModelZero (W.map (algebraMap A ↑Γ(S, (⊤ : S.Opens))))
    dsimp only [eModel]
    have hcrux : (isAffineOpen_top S).isoSpec.inv ≫ (⊤ : S.Opens).ι =
        Spec.map (CommRingCat.ofHom (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) :=
      hφ ▸ (IsAffineOpen.isoSpec_inv_ι _).trans IsAffineOpen.fromSpec_top
    have hcrux_assoc : ∀ {Z : Scheme.{u}} (g : S ⟶ Z),
        (isAffineOpen_top S).isoSpec.inv ≫ (⊤ : S.Opens).ι ≫ g =
          Spec.map (CommRingCat.ofHom
            (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) ≫ g := fun g => by
      rw [← Category.assoc]
      exact congrArg (· ≫ g) hcrux
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc]
    rw [pullback.lift_fst_assoc]
    simp only [Category.assoc]
    conv_lhs => erw [hcrux_assoc]
    erw [← reassoc_of% projModelZero_baseChange W,
      ← (isPullback_projModelBaseChange W).isoPullback_hom_fst_assoc,
      IsIso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The geometric j section of an actual model is its coefficient-ring j. -/
theorem model_jSection :
    jSection (modelEllipticCurve W).toEllipticCurveGeom =
      (Scheme.ΓSpecIso (.of A)).inv.hom W.j := by
  let P := modelTopPresentation W
  let modelChartElliptic := P.elliptic
  have h : jSection (modelEllipticCurve W).toEllipticCurveGeom = P.W.j := by
    simpa only [Scheme.resLE_rfl, chartJ] using jSection_res P
  have hj : P.W.j = (Scheme.ΓSpecIso (.of A)).inv.hom W.j := by
    change (W.map (Scheme.ΓSpecIso (.of A)).inv.hom).j = _
    exact WeierstrassCurve.map_j W _
  exact h.trans hj

#print axioms modelTopPresentation
#print axioms model_jSection

end ModularCurves.YZeroCoarseJ
