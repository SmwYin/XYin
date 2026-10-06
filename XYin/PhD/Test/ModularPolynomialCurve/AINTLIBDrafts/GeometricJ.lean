/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.EllipticCurve.InvariantDifferential
public import ModularCurves.Moduli.EllCategory
public import ModularCurves.ForMathlib.SchemeAppLE

/-!
# Regular geometric j sections over affine bases

This file targets AINTLIB revision `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`.
The construction only uses local pointed Weierstrass presentations and sheaf gluing.
It does not use any full-level moduli object or coarse quotient.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace WeierstrassCurve

namespace ModularCurves.YZeroCoarseJ

variable {S : Scheme.{u}} {G : EllipticCurveGeom S}

/-- The j-invariant in the section ring of a local pointed Weierstrass presentation. -/
noncomputable def chartJ {V : S.affineOpens} (P : LocalPresentation G V) : Γ(S, V.1) :=
  letI := P.elliptic
  P.W.j

/-- The section is independent of the pointed presentation over the same affine open. -/
theorem chartJ_eq {V : S.affineOpens} (P Q : LocalPresentation G V) :
    chartJ P = chartJ Q := by
  let := P.elliptic
  let := Q.elliptic
  change P.W.j = Q.W.j
  have h := WeierstrassCurve.variableChange_j Q.W (P.transVC Q)
  simpa only [P.transVC_smul Q] using h

/-- The chart j-invariant commutes with a pointed cartesian change of base. -/
theorem chartJ_transport {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    {V : S.affineOpens} (P : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    chartJ (P.transport f t hsq hz hV') = sectionsMapLE f hV' (chartJ P) := by
  let := P.elliptic
  let := (P.transport f t hsq hz hV').elliptic
  change (P.transport f t hsq hz hV').W.j = sectionsMapLE f hV' P.W.j
  simp_rw [LocalPresentation.transport_W]
  exact WeierstrassCurve.map_j P.W (sectionsMapLE f hV')

/-- Restriction of a chart j-invariant is the j-invariant of the restricted chart. -/
theorem chartJ_restrict {V V' : S.affineOpens} (P : LocalPresentation G V)
    (h : V'.1 ≤ V.1) :
    chartJ (P.restrict h) = Scheme.resLE h (chartJ P) := by
  unfold LocalPresentation.restrict
  rw [chartJ_transport, LocalPresentation.sectionsMapLE_id]

/-- On an affine base the local j-invariants glue to a regular global section. -/
theorem existsUnique_jSection [IsAffine S] (G : EllipticCurveGeom S) :
    ∃! j : Γ(S, ⊤), ∀ i : G.atlas.ι,
      Scheme.resLE le_top j = chartJ (G.atlas.presentation i) := by
  let U : G.atlas.ι → S.Opens := fun i ↦ (G.atlas.U i).1
  have hcover : (⊤ : S.Opens) ≤ iSup U := by
    intro x _
    obtain ⟨i, hi⟩ := G.atlas.covers x
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  have hcompat : TopCat.Presheaf.IsCompatible S.sheaf.1 U
      (fun i ↦ chartJ (G.atlas.presentation i)) := by
    intro i k
    let V : S.affineOpens := ⟨U i ⊓ U k, (G.atlas.U i).2.inf (G.atlas.U k).2⟩
    show Scheme.resLE (inf_le_left : V.1 ≤ U i)
        (chartJ (G.atlas.presentation i)) =
      Scheme.resLE (inf_le_right : V.1 ≤ U k) (chartJ (G.atlas.presentation k))
    exact (chartJ_restrict (V' := V) (G.atlas.presentation i) inf_le_left).symm.trans
      ((chartJ_eq
          ((G.atlas.presentation i).restrict (V' := V) inf_le_left)
          ((G.atlas.presentation k).restrict (V' := V) inf_le_right)).trans
        (chartJ_restrict (V' := V) (G.atlas.presentation k) inf_le_right))
  exact TopCat.Sheaf.existsUnique_gluing' S.sheaf U ⊤
    (fun _ ↦ homOfLE le_top) hcover (fun i ↦ chartJ (G.atlas.presentation i)) hcompat

/-- The regular j section of a geometric elliptic curve over an affine base. -/
noncomputable def jSection [IsAffine S] (G : EllipticCurveGeom S) : Γ(S, ⊤) :=
  (existsUnique_jSection G).choose

/-- The defining atlas restriction of the global j section. -/
theorem jSection_res_atlas [IsAffine S] (G : EllipticCurveGeom S) (i : G.atlas.ι) :
    Scheme.resLE le_top (jSection G) = chartJ (G.atlas.presentation i) :=
  (existsUnique_jSection G).choose_spec.1 i

/-- The regular section restricts to the j-invariant of any pointed local presentation. -/
theorem jSection_res [IsAffine S] {V : S.affineOpens} (P : LocalPresentation G V) :
    Scheme.resLE le_top (jSection G) = chartJ P := by
  let U : G.atlas.ι → S.Opens := fun i ↦ V.1 ⊓ (G.atlas.U i).1
  have hcover : V.1 ≤ iSup U := by
    intro x hx
    obtain ⟨i, hi⟩ := G.atlas.covers x
    exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  refine TopCat.Sheaf.eq_of_locally_eq' S.sheaf U V.1
    (fun _ ↦ homOfLE inf_le_left) hcover _ _ (fun i ↦ ?_)
  let W : S.affineOpens := ⟨U i, V.2.inf (G.atlas.U i).2⟩
  show Scheme.resLE (inf_le_left : W.1 ≤ V.1)
      (Scheme.resLE le_top (jSection G)) =
    Scheme.resLE (inf_le_left : W.1 ≤ V.1) (chartJ P)
  calc
    _ = Scheme.resLE (inf_le_right : W.1 ≤ (G.atlas.U i).1)
        (Scheme.resLE le_top (jSection G)) := by
      rw [Scheme.resLE_resLE, Scheme.resLE_resLE]
    _ = Scheme.resLE (inf_le_right : W.1 ≤ (G.atlas.U i).1)
        (chartJ (G.atlas.presentation i)) :=
      congrArg (Scheme.resLE (inf_le_right : W.1 ≤ (G.atlas.U i).1))
        (jSection_res_atlas G i)
    _ = chartJ ((G.atlas.presentation i).restrict (V' := W) inf_le_right) :=
      (chartJ_restrict (V' := W) (G.atlas.presentation i) inf_le_right).symm
    _ = chartJ (P.restrict (V' := W) (inf_le_left : W.1 ≤ V.1)) :=
      chartJ_eq ((G.atlas.presentation i).restrict (V' := W) inf_le_right)
        (P.restrict (V' := W) inf_le_left)
    _ = _ := chartJ_restrict (V' := W) P inf_le_left

/-- The global j section is natural under pointed cartesian affine changes of base. -/
theorem jSection_naturality [IsAffine S] {S' : Scheme.{u}} [IsAffine S']
    {G' : EllipticCurveGeom S'} (f : S' ⟶ S) [IsAffineHom f]
    (t : G'.E ⟶ G.E) (hsq : IsPullback t G'.π G.π f)
    (hz : G'.zero ≫ t = f ≫ G.zero) :
    f.appTop.hom (jSection G) = jSection G' := by
  let U : G.atlas.ι → S'.Opens := fun i ↦ f ⁻¹ᵁ (G.atlas.U i).1
  have hcover : (⊤ : S'.Opens) ≤ iSup U := by
    intro x _
    obtain ⟨i, hi⟩ := G.atlas.covers (f.base x)
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  refine TopCat.Sheaf.eq_of_locally_eq' S'.sheaf U ⊤
    (fun _ ↦ homOfLE le_top) hcover _ _ (fun i ↦ ?_)
  let V : S'.affineOpens := ⟨U i, (G.atlas.U i).2.preimage f⟩
  let P := (G.atlas.presentation i).transport f t hsq hz (le_refl V.1)
  show Scheme.resLE (le_top : V.1 ≤ ⊤) (f.appTop.hom (jSection G)) =
    Scheme.resLE (le_top : V.1 ≤ ⊤) (jSection G')
  rw [jSection_res P, chartJ_transport]
  have hTop : sectionsMapLE f (show (⊤ : S'.Opens) ≤ f ⁻¹ᵁ ⊤ from by simp) =
      f.appTop.hom := by
    exact congrArg CommRingCat.Hom.hom (appLE_top_top f)
  rw [← hTop]
  rw [← jSection_res_atlas G i]
  have hleft := congrArg (fun ρ : Γ(S, ⊤) →+* Γ(S', V.1) ↦ ρ (jSection G))
    (LocalPresentation.sectionsMapLE_comp_resLE f
      (show (⊤ : S'.Opens) ≤ f ⁻¹ᵁ ⊤ from by simp) (le_top : V.1 ≤ ⊤))
  have hright := congrArg (fun ρ : Γ(S, ⊤) →+* Γ(S', V.1) ↦ ρ (jSection G))
    (LocalPresentation.resLE_comp_sectionsMapLE f (le_top : (G.atlas.U i).1 ≤ ⊤)
      (le_refl V.1))
  exact hleft.trans hright.symm

variable {R : CommRingCat.{u}}

/-- Pull back the constants along the structure morphism. -/
noncomputable def coeffHom (X : EllObj R) : R →+* Γ(X.base, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ X.structMap.appTop).hom

/-- Constants pull back naturally in the elliptic-curve category. -/
theorem coeffHom_naturality {X X' : EllObj R} (φ : X' ⟶ X) :
    φ.baseHom.appTop.hom.comp (coeffHom X) = coeffHom X' := by
  change ((Scheme.ΓSpecIso R).inv ≫ X.structMap.appTop ≫ φ.baseHom.appTop).hom =
    ((Scheme.ΓSpecIso R).inv ≫ X'.structMap.appTop).hom
  rw [← Scheme.Hom.comp_appTop, φ.base_w]

/-- Evaluation of the polynomial variable at the regular global j section. -/
noncomputable def jPolynomialHom (X : EllObj R) [IsAffine X.base] :
    Polynomial R →+* Γ(X.base, ⊤) :=
  Polynomial.eval₂RingHom (coeffHom X) (jSection X.curve.toEllipticCurveGeom)

/-- The regular source-j morphism to the affine j-line over the base ring. -/
noncomputable def jMap (X : EllObj R) [IsAffine X.base] :
    X.base ⟶ Spec (.of (Polynomial R)) :=
  X.base.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (jPolynomialHom X))

/-- The source-j morphism is natural in pointed cartesian squares on affine bases. -/
theorem jMap_naturality {X X' : EllObj R} [IsAffine X.base] [IsAffine X'.base]
    (φ : X' ⟶ X) : φ.baseHom ≫ jMap X = jMap X' := by
  rw [jMap, jMap, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  change φ.baseHom.appTop.hom.comp (jPolynomialHom X) = jPolynomialHom X'
  apply Polynomial.ringHom_ext
  · intro a
    simp only [jPolynomialHom, RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C]
    exact DFunLike.congr_fun (coeffHom_naturality φ) a
  · simp only [jPolynomialHom, RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
    exact jSection_naturality φ.baseHom φ.top φ.isPullback φ.zero_w

/-- The j-line projection to the base ring. -/
noncomputable def jLineBase : Spec (.of (Polynomial R)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

/-- The regular j morphism is a morphism over the original base ring. -/
theorem jMap_comp_base (X : EllObj R) [IsAffine X.base] :
    jMap X ≫ jLineBase = X.structMap := by
  have hcomp : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫
      (CommRingCat.ofHom (jPolynomialHom X)) =
        (Scheme.ΓSpecIso R).inv ≫ X.structMap.appTop := by
    apply CommRingCat.hom_ext
    change (jPolynomialHom X).comp Polynomial.C = coeffHom X
    ext a
    simp [jPolynomialHom]
  rw [jMap, jLineBase, Category.assoc, ← Spec.map_comp, hcomp, Spec.map_comp,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

/-- Pulling back sections along the j morphism is precisely evaluation at geometric j. -/
theorem jMap_pullback_hom (X : EllObj R) [IsAffine X.base] :
    (Scheme.ΓSpecIso (.of (Polynomial R))).inv ≫ (jMap X).appTop =
      CommRingCat.ofHom (jPolynomialHom X) := by
  rw [jMap, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Scheme.toSpecΓ_appTop,
    Iso.inv_hom_id, Category.comp_id]

/-- Pulling back the j-line coordinate recovers the glued Weierstrass j section. -/
theorem jMap_pullback_X (X : EllObj R) [IsAffine X.base] :
    (((Scheme.ΓSpecIso (.of (Polynomial R))).inv ≫ (jMap X).appTop).hom)
      Polynomial.X = jSection X.curve.toEllipticCurveGeom := by
  rw [jMap_pullback_hom]
  simp [jPolynomialHom]

#print axioms chartJ_eq
#print axioms existsUnique_jSection
#print axioms jMap_naturality
#print axioms jMap_comp_base
#print axioms jMap_pullback_hom
#print axioms jMap_pullback_X

end ModularCurves.YZeroCoarseJ
