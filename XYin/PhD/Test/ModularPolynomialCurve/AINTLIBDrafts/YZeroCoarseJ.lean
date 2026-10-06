/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.GeometricJ
public import ModularCurves.Moduli.CoarseSpace
public import AINTLIBDrafts.YZeroCoarseInvariantSpec
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.NormNum

/-!
# Regular source-j morphisms on the actual AINTLIB coarse curve

This file targets AINTLIB revision `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`
and its pinned toolchain. It is deliberately not imported by the XYin build.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace WeierstrassCurve

namespace ModularCurves.YZeroCoarseJ

variable {R : CommRingCat.{u}}

section Coarse

variable {P : ModuliProblem R} {X : EllObj R} {H : Type*} [Group H]
variable (r : P.RepresentableBy X) (φ : H →* Aut P) [IsAffineHom X.structMap]

/-- An affine structure morphism over the affine base ring has affine source. -/
local instance affineBase : IsAffine X.base := isAffine_of_isAffineHom X.structMap

/-- The genuine Weierstrass j section is fixed by every transported moduli automorphism. -/
theorem action_jSection (γ : H) :
    ((r.baseSchemeAction φ).hom γ).appTop.hom (jSection X.curve.toEllipticCurveGeom) =
      jSection X.curve.toEllipticCurveGeom :=
  jSection_naturality ((r.autMulHom (φ γ)).inv).baseHom
    ((r.autMulHom (φ γ)).inv).top ((r.autMulHom (φ γ)).inv).isPullback
    ((r.autMulHom (φ γ)).inv).zero_w

/-- The source-j morphism is invariant under the induced action on the fine base. -/
theorem action_comp_jMap (γ : H) :
    (r.baseSchemeAction φ).hom γ ≫ jMap X = jMap X :=
  jMap_naturality ((r.autMulHom (φ γ)).inv)

variable [Finite H]

/-- The unique source-j morphism on the actual relative invariant-Spec coarse quotient. -/
noncomputable def coarseJMap : r.coarseQuotient φ ⟶ Spec (.of (Polynomial R)) :=
  (r.coarsePr_existsUnique_lift φ (jMap X) (action_comp_jMap r φ)).choose

/-- The coarse source-j map pulls back to the fine source-j map. -/
theorem coarsePr_comp_coarseJMap :
    r.coarsePr φ ≫ coarseJMap r φ = jMap X :=
  (r.coarsePr_existsUnique_lift φ (jMap X) (action_comp_jMap r φ)).choose_spec.1

/-- The descended j map is also over the original base ring. -/
theorem coarseJMap_comp_base :
    coarseJMap r φ ≫ jLineBase = r.coarseStruct φ := by
  have hex := r.coarsePr_existsUnique_lift φ X.structMap (r.baseSchemeAction_over φ)
  have hfirst : r.coarsePr φ ≫ (coarseJMap r φ ≫ jLineBase) = X.structMap := by
    rw [← Category.assoc, coarsePr_comp_coarseJMap, jMap_comp_base]
  exact (hex.choose_spec.2 _ hfirst).trans
    (hex.choose_spec.2 _ (r.coarsePr_comp_coarseStruct φ)).symm

end Coarse

/-- The actual full-level universal object's base is affine. -/
theorem xFullNaive_base_isAffine (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R)) : IsAffine (xFullNaive (R := R) N hN hinv).base := by
  have : IsAffineHom (xFullNaive (R := R) N hN hinv).structMap :=
    ModuliProblem.gammaFullNaive_isAffineHom_structMap N hN hinv
      (xFullNaiveRepr (R := R) N hN hinv)
  exact isAffine_of_isAffineHom (xFullNaive (R := R) N hN hinv).structMap

/-- The universal curve's j morphism descended through AINTLIB's chosen Borel quotient
`YZeroCoarse`. -/
noncomputable def yZeroSourceJ (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ)) (hinv : IsUnit (N : R)) :
    YZeroCoarse (R := R) N hN hinv ⟶ Spec (.of (Polynomial R)) :=
  coarseJMap (xFullNaiveRepr (R := R) N hN hinv) (gammaHAut R N (borel N))

open ModularPolynomialCurveTest.AINTLIB

/-- The source-j morphism on the actual coarse curve pulls back along its chosen projection. -/
theorem yZeroPr_comp_yZeroSourceJ (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R)) :
    yZeroPr N hN hinv ≫ yZeroSourceJ N hN hinv = jMap (fullObject N hN hinv) :=
  coarsePr_comp_coarseJMap (xFullNaiveRepr (R := R) N hN hinv)
    (gammaHAut R N (borel N))

/-- The actual source-j morphism commutes with the actual structural map of `YZeroCoarse`. -/
theorem yZeroSourceJ_comp_base (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R)) :
    yZeroSourceJ N hN hinv ≫ jLineBase = yZeroStruct N hN hinv :=
  coarseJMap_comp_base (xFullNaiveRepr (R := R) N hN hinv)
    (gammaHAut R N (borel N))

/-- Pullback of the actual coarse j coordinate is the fine universal curve's Weierstrass j. -/
theorem yZeroPr_sourceJ_pullback_X (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R)) :
    (((Scheme.ΓSpecIso (.of (Polynomial R))).inv ≫
        (yZeroPr N hN hinv ≫ yZeroSourceJ N hN hinv).appTop).hom) Polynomial.X =
      jSection (fullObject N hN hinv).curve.toEllipticCurveGeom := by
  rw [yZeroPr_comp_yZeroSourceJ]
  exact jMap_pullback_X _

/-- Any actual local Weierstrass model of the universal fine curve computes coarse j pullback. -/
theorem yZeroPr_sourceJ_pullback_X_res_chart (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R)) {V : (fullObject N hN hinv).base.affineOpens}
    (P : LocalPresentation (fullObject N hN hinv).curve.toEllipticCurveGeom V) :
    Scheme.resLE le_top
        ((((Scheme.ΓSpecIso (.of (Polynomial R))).inv ≫
          (yZeroPr N hN hinv ≫ yZeroSourceJ N hN hinv).appTop).hom) Polynomial.X) =
      chartJ P := by
  rw [yZeroPr_sourceJ_pullback_X]
  exact jSection_res P

/-- A concrete characteristic-zero base and admissible level for the source-j construction. -/
theorem isUnit_three_complex : IsUnit (3 : ℂ) :=
  isUnit_iff_ne_zero.mpr (by norm_num)

/-- The actual level-three AINTLIB coarse curve over `ℂ`, with its regular source-j map. -/
noncomputable def yZeroThreeComplexSourceJ :
    YZeroCoarse (R := .of ℂ) 3 le_rfl isUnit_three_complex ⟶
      Spec (.of (Polynomial ℂ)) :=
  yZeroSourceJ 3 le_rfl isUnit_three_complex

example : yZeroThreeComplexSourceJ ≫ jLineBase (R := .of ℂ) =
    yZeroStruct (R := .of ℂ) 3 le_rfl isUnit_three_complex :=
  yZeroSourceJ_comp_base 3 le_rfl isUnit_three_complex

example : yZeroPr (R := .of ℂ) 3 le_rfl isUnit_three_complex ≫
      yZeroThreeComplexSourceJ =
    jMap (fullObject (R := .of ℂ) 3 le_rfl isUnit_three_complex) :=
  yZeroPr_comp_yZeroSourceJ 3 le_rfl isUnit_three_complex

example {V : (fullObject (R := .of ℂ) 3 le_rfl isUnit_three_complex).base.affineOpens}
    (P : LocalPresentation
      (fullObject (R := .of ℂ) 3 le_rfl isUnit_three_complex).curve.toEllipticCurveGeom V) :
    Scheme.resLE le_top
        ((((Scheme.ΓSpecIso (.of (Polynomial ℂ))).inv ≫
          (yZeroPr (R := .of ℂ) 3 le_rfl isUnit_three_complex ≫
            yZeroThreeComplexSourceJ).appTop).hom) Polynomial.X) = chartJ P :=
  yZeroPr_sourceJ_pullback_X_res_chart 3 le_rfl isUnit_three_complex P

#print axioms chartJ_eq
#print axioms existsUnique_jSection
#print axioms jMap_naturality
#print axioms jMap_comp_base
#print axioms jMap_pullback_hom
#print axioms jMap_pullback_X
#print axioms yZeroSourceJ
#print axioms yZeroSourceJ_comp_base
#print axioms yZeroPr_sourceJ_pullback_X_res_chart
#print axioms yZeroThreeComplexSourceJ

end ModularCurves.YZeroCoarseJ
