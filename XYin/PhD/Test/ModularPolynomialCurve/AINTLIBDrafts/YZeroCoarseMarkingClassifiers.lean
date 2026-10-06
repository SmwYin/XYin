/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseMarkedComplexCurves

/-!
# Naturality and Borel compatibility of native marking classifiers

A cartesian pointed morphism between native complex curve objects lies over the
identity of `Spec ℂ`, so functorial pullback of a marking preserves its classified
fine complex point. The proof projects mathlib's `comp_homEquiv_symm` to the base.

The actual Borel scheme action is obtained from `CoarseSpace.baseSchemeAction`.
Its inverse convention cancels the inverse in `GammaHRepresentability.gammaHAut`:
postcomposition by the action of `g` corresponds to positive `glSmul g` of the
marking. The proof uses `RepresentableAut.homEquiv_comp_transportHom` on the inverse
natural transformation and then projects the resulting classifier equality.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ModularCurves ModularCurves.YZeroCoarseJ

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

variable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))

/-- A same-base cartesian pointed morphism preserves the classified fine complex point. -/
theorem fullComplexSchemePointOfMarking_map
    (E E' : ModularCurves.EllipticCurve (Spec (.of ℂ)))
    (u : complexEllObj E ⟶ complexEllObj E')
    (L' : complexFullMarking N E') :
    fullComplexSchemePointOfMarking N hN E
        ((gammaFullNaiveProblem (.of ℂ) N).map u.op L') =
      fullComplexSchemePointOfMarking N hN E' L' := by
  apply Subtype.ext
  change (fullMarkingClassifier N hN E
      ((gammaFullNaiveProblem (.of ℂ) N).map u.op L')).baseHom =
    (fullMarkingClassifier N hN E' L').baseHom
  have h := (xFullNaiveRepr (R := .of ℂ) N hN (complexLevelIsUnit N)).comp_homEquiv_symm
    L' u
  let b : Spec (.of ℂ) ⟶ Spec (.of ℂ) := u.baseHom
  let p : Spec (.of ℂ) ⟶ (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base :=
    (fullMarkingClassifier N hN E
      ((gammaFullNaiveProblem (.of ℂ) N).map u.op L')).baseHom
  let q : Spec (.of ℂ) ⟶ (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base :=
    (fullMarkingClassifier N hN E' L').baseHom
  have hb : b ≫ q = p := congrArg EllHom.baseHom h
  have hb_id : b = 𝟙 (Spec (.of ℂ)) := by
    have hw : b ≫ 𝟙 (Spec (.of ℂ)) = 𝟙 (Spec (.of ℂ)) := u.base_w
    exact (Category.comp_id b).symm.trans hw
  rw [hb_id, Category.id_comp] at hb
  exact hb.symm

/-- The actual represented Borel action changes the given marking by positive `glSmul g`. -/
theorem fullComplexSchemePointOfMarking_glSmul
    (E : ModularCurves.EllipticCurve (Spec (.of ℂ)))
    (g : borel N) (L : complexFullMarking N E) :
    (fullComplexSchemePointOfMarking N hN E
        (E.glSmul (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) L)).val =
      (fullComplexSchemePointOfMarking N hN E L).val ≫
        (borelAction (R := .of ℂ) N hN (complexLevelIsUnit N)).hom g := by
  let r := xFullNaiveRepr (R := .of ℂ) N hN (complexLevelIsUnit N)
  let v := fullMarkingClassifier N hN E L
  have h := r.homEquiv_comp_transportHom (gammaHAut (.of ℂ) N (borel N) g).inv v
  have hv : r.homEquiv v = L := r.homEquiv.apply_symm_apply L
  rw [hv] at h
  change r.homEquiv (v ≫ (r.autMulHom (gammaHAut (.of ℂ) N (borel N) g)).inv) =
    E.glSmul (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) L at h
  have hClass : r.homEquiv (fullMarkingClassifier N hN E
      (E.glSmul (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) L)) =
        E.glSmul (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) L :=
    r.homEquiv.apply_symm_apply _
  have hc : v ≫ (r.autMulHom (gammaHAut (.of ℂ) N (borel N) g)).inv =
      fullMarkingClassifier N hN E
        (E.glSmul (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) L) :=
    r.homEquiv.injective (h.trans hClass.symm)
  change (fullMarkingClassifier N hN E
      (E.glSmul (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) L)).baseHom =
    v.baseHom ≫ (r.autMulHom (gammaHAut (.of ℂ) N (borel N) g)).inv.baseHom
  exact (congrArg EllHom.baseHom hc).symm

#print axioms fullComplexSchemePointOfMarking_map
#print axioms fullComplexSchemePointOfMarking_glSmul

example (E E' : ModularCurves.EllipticCurve (Spec (.of ℂ)))
    (u : complexEllObj E ⟶ complexEllObj E')
    (L' : complexFullMarking 3 E') :
    fullComplexSchemePointOfMarking 3 (by decide) E
        ((gammaFullNaiveProblem (.of ℂ) 3).map u.op L') =
      fullComplexSchemePointOfMarking 3 (by decide) E' L' :=
  fullComplexSchemePointOfMarking_map 3 (by decide) E E' u L'

example (E : ModularCurves.EllipticCurve (Spec (.of ℂ)))
    (g : borel 3) (L : complexFullMarking 3 E) :
    (fullComplexSchemePointOfMarking 3 (by decide) E
        (E.glSmul (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) L)).val =
      (fullComplexSchemePointOfMarking 3 (by decide) E L).val ≫
        (borelAction (R := .of ℂ) 3 (by decide) (complexLevelIsUnit 3)).hom g :=
  fullComplexSchemePointOfMarking_glSmul 3 (by decide) E g L

end ModularPolynomialCurveTest.AINTLIB
