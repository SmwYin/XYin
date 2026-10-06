/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.WeilPairing.FieldComparisonBridge

/-!
# Geometric constants in a projective model's function field

The constant ring homomorphism is defined independently by the literal chain
`ΓSpecIso.inv → projModelπ.appTop → generic top germ`. The existing native
projective-model function-field ring equivalence preserves this map: its
composite equals the canonical constant map into the affine function field.

The proof reuses the public chart-constant and coordinate-germ formulas,
restriction compatibility of germs, and the canonical affine scalar tower.
It assumes only an arbitrary field and an elliptic Weierstrass curve; any
`DecidableEq` needed by the reused native theorem is supplied locally.

This proves a genuine constant-map square. It does not construct an algebra
equivalence for an arbitrary native elliptic curve, prove a genus result, or
provide a Weierstrass model for a subgroup quotient. The imported native
leaf's historical source warnings are recorded separately from this module's
strict, warning-free verification.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ModularCurves

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

/-- Constants come independently from the structural map and the generic germ. -/
noncomputable def projModelConstantRingHom (W : WeierstrassCurve k) [W.IsElliptic] :
    k →+* (projModel W).functionField :=
  ((projModel W).germToFunctionField ⊤).hom.comp
    (((projModelπ W).appTop).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)

/-- The existing ring equivalence preserves the literal geometric constants. -/
theorem projModelFunctionFieldEquiv_comp_constants
    (W : WeierstrassCurve k) [W.IsElliptic] :
    (EllipticCurve.projModelFunctionFieldEquiv W).toRingHom.comp
      (projModelConstantRingHom W) = algebraMap k W.toAffine.FunctionField := by
  classical
  have hZaff : IsAffineOpen (EllipticCurve.zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  have : Nontrivial Γ(projModel W, EllipticCurve.zChart W) :=
    (coordRingToZSection W).toEquiv.symm.nontrivial
  have : Nonempty (EllipticCurve.zChart W : (projModel W).Opens) :=
    ⟨hZaff.isoSpec.inv.base (Classical.arbitrary _)⟩
  have : IsFractionRing Γ(projModel W, EllipticCurve.zChart W) (projModel W).functionField :=
    functionField_isFractionRing_of_isAffineOpen (projModel W) _ hZaff
  have hres (s : Γ(projModel W, ⊤)) :
      algebraMap Γ(projModel W, EllipticCurve.zChart W) (projModel W).functionField
          (((projModel W).presheaf.map
            (homOfLE (le_top : (EllipticCurve.zChart W : (projModel W).Opens) ≤ ⊤)).op).hom s) =
        (projModel W).germToFunctionField ⊤ s :=
    TopCat.Presheaf.germ_res_apply (projModel W).presheaf
      (homOfLE le_top) (genericPoint (projModel W)) _ s
  ext r
  change EllipticCurve.projModelFunctionFieldEquiv W
      ((projModel W).germToFunctionField ⊤
        (((projModelπ W).appTop).hom ((Scheme.ΓSpecIso (.of k)).inv.hom r))) = _
  have hconst : coordRingToZSection W (algebraMap k W.toAffine.CoordinateRing r) =
      (((projModel W).presheaf.map
        (homOfLE (le_top : (EllipticCurve.zChart W : (projModel W).Opens) ≤ ⊤)).op).hom
          (((projModelπ W).appTop).hom ((Scheme.ΓSpecIso (.of k)).inv.hom r))) :=
    EllipticCurve.coordRingToZSection_algebraMap W r
  rw [← hres _, ← hconst, EllipticCurve.projModelFunctionFieldEquiv_germ,
    RingEquiv.symm_apply_apply]
  exact (IsScalarTower.algebraMap_apply k W.toAffine.CoordinateRing
    W.toAffine.FunctionField r).symm

example (W : WeierstrassCurve k) [W.IsElliptic] (r : k) :
    projModelConstantRingHom W r = (projModel W).germToFunctionField ⊤
      (((projModelπ W).appTop).hom ((Scheme.ΓSpecIso (.of k)).inv.hom r)) := rfl

example (W : WeierstrassCurve k) [W.IsElliptic] (r : k) :
    EllipticCurve.projModelFunctionFieldEquiv W
      ((projModel W).germToFunctionField ⊤
        (((projModelπ W).appTop).hom ((Scheme.ΓSpecIso (.of k)).inv.hom r))) =
      algebraMap k W.toAffine.FunctionField r :=
  congrArg (fun f : k →+* W.toAffine.FunctionField => f r)
    (projModelFunctionFieldEquiv_comp_constants W)

#print axioms projModelConstantRingHom
#print axioms projModelFunctionFieldEquiv_comp_constants
#print axioms EllipticCurve.coordRingToZSection_algebraMap
#print axioms EllipticCurve.projModelFunctionFieldEquiv_germ
#print axioms EllipticCurve.projModelFunctionFieldEquiv_symm_algebraMap
#print axioms chartZRingEquiv_fromZero
#print axioms structure_section_square_apply
#print axioms IsLocalization.ringEquivOfRingEquiv_eq
#print axioms TopCat.Presheaf.germ_res_apply
#print axioms IsScalarTower.algebraMap_apply

end ModularCurves.YZeroCoarseJ
