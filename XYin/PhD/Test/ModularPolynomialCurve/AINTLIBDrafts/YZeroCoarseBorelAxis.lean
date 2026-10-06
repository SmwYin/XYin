/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseConstantAxis

/-!
# Borel invariance of the embedded constant-axis subgroup

For a fixed elliptic curve, a Borel matrix changes the first section of a naive full
level marking by a unit of `ZMod N`. Positive multiplication by this unit reindexes
the actual constant label scheme. The new section-axis morphism is therefore this
label isomorphism followed by the old section-axis morphism, and their kernels agree.

The scalar/reindexing lemma works over any scheme for any `N`-killed section. Invertibility
of `N` on `Spec R` is needed only to instantiate the existing finite locally free subgroup
constructor. This proves equality of the embedded subgroup ideals in the fixed curve.
It does not assert literal equality of bundled `GammaZeroStructure` records or descent
of a quotient-curve `j` invariant.

The determinant and scalar arithmetic use the pinned AINTLIB `borel` and `glSmul`
definitions. Reindexing and kernel invariance use mathlib's actual coproduct isomorphism
and `Scheme.Hom.ker_comp_of_isIso`. The three API checks include a positive unit-2
morphism equation modulo 5, where the inverse unit is 3.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ModularCurves

noncomputable section

universe u

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

variable {N : ℕ} [NeZero N]

/-- The first diagonal entry of an actual Borel matrix is a unit. -/
theorem borel_fstEntry_isUnit (g : ↥(borel N)) :
    IsUnit ((g.val : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0) := by
  have h10 : (g.val : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0 = 0 := g.property
  have hdet : IsUnit (g.val : Matrix (Fin 2) (Fin 2) (ZMod N)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.val.isUnit
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact (IsUnit.mul_iff.mp hdet).1

/-- Scaling a killed section by a residue-class unit positively reindexes its axis. -/
theorem sectionAxis_zsmul_of_unit {S : Scheme.{u}} (E : EllipticCurve S)
    (P : E.Section) (hP : (N : ℤ) • P = 0) (v : (ZMod N)ˣ) :
    sectionAxis (N := N) E (((v : ZMod N).val : ℤ) • P) =
      (Sigma.reindex v.mulLeft (fun _ : ZMod N ↦ S)).hom ≫ sectionAxis E P := by
  refine Sigma.hom_ext _ _ fun a ↦ ?_
  change Sigma.ι ((fun _ : ZMod N ↦ S) ∘ v.mulLeft) a ≫
      sectionAxis E (((v : ZMod N).val : ℤ) • P) =
    Sigma.ι ((fun _ : ZMod N ↦ S) ∘ v.mulLeft) a ≫
      (Sigma.reindex v.mulLeft (fun _ : ZMod N ↦ S)).hom ≫ sectionAxis E P
  rw [Sigma.ι_reindex_hom_assoc]
  simp only [sectionAxis, Sigma.ι_comp_desc, Units.mulLeft_apply]
  have hsec : (a.val : ℤ) • (((v : ZMod N).val : ℤ) • P) =
      ((((v : ZMod N) * a).val : ℤ) • P) := by
    rw [smul_smul]
    simpa only [mul_comm] using (E.val_smul_mul P hP a (v : ZMod N)).symm
  exact congrArg Subtype.val hsec

/-- A Borel change of full marking preserves the embedded subgroup ideal in a fixed curve. -/
theorem sectionAxisSubgroup_glSmul_borel_ker (R : CommRingCat.{u})
    (E : EllipticCurve (Spec R)) (hinv : NIsInvertible (Spec R) N)
    (L : E.FullLevelPt N) (g : ↥(borel N)) :
    (sectionAxisSubgroup R N E hinv (E.glSmul g.val L)).ι.ker =
      (sectionAxisSubgroup R N E hinv L).ι.ker := by
  let v : (ZMod N)ˣ := (borel_fstEntry_isUnit g).unit
  have hfirst : (E.glSmul g.val L).val.1 =
      (((v : ZMod N).val : ℤ) • L.val.1) := by
    change (((g.val : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0).val : ℤ) • L.val.1 +
      (((g.val : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0).val : ℤ) • L.val.2 = _
    rw [g.property, ZMod.val_zero, Nat.cast_zero, zero_smul, add_zero]
    rw [show (v : ZMod N) = (g.val : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0 from
      (borel_fstEntry_isUnit g).unit_spec]
  change (sectionAxis (N := N) E (E.glSmul g.val L).val.1).ker =
    (sectionAxis (N := N) E L.val.1).ker
  rw [hfirst, sectionAxis_zsmul_of_unit E L.val.1 L.property.1.1 v]
  exact Scheme.Hom.ker_comp_of_isIso _ _

example {S : Scheme.{u}} (E : EllipticCurve S) (P : E.Section)
    (hP : (3 : ℤ) • P = 0) :
    (sectionAxis (N := 3) E ((2 : ℤ) • P)).ker =
      (sectionAxis (N := 3) E P).ker := by
  let v : (ZMod 3)ˣ := ⟨2, 2, by decide, by decide⟩
  have h := sectionAxis_zsmul_of_unit E P hP v
  change sectionAxis (N := 3) E ((2 : ℤ) • P) = _ at h
  rw [h]
  exact Scheme.Hom.ker_comp_of_isIso _ _

example (R : CommRingCat.{u}) (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) 3) (L : E.FullLevelPt 3) (g : ↥(borel 3)) :
    (sectionAxisSubgroup R 3 E hinv (E.glSmul g.val L)).ι.ker =
      (sectionAxisSubgroup R 3 E hinv L).ι.ker :=
  sectionAxisSubgroup_glSmul_borel_ker R E hinv L g

example {S : Scheme.{u}} (E : EllipticCurve S) (P : E.Section)
    (hP : (5 : ℤ) • P = 0) :
    sectionAxis (N := 5) E ((2 : ℤ) • P) =
      (Sigma.reindex (⟨2, 3, by decide, by decide⟩ : (ZMod 5)ˣ).mulLeft
        (fun _ : ZMod 5 ↦ S)).hom ≫ sectionAxis E P :=
  sectionAxis_zsmul_of_unit E P hP ⟨2, 3, by decide, by decide⟩

#print axioms borel_fstEntry_isUnit
#print axioms sectionAxis_zsmul_of_unit
#print axioms sectionAxisSubgroup_glSmul_borel_ker
#print axioms ModularCurves.EllipticCurve.val_smul_mul
#print axioms Sigma.reindex
#print axioms Sigma.ι_reindex_hom
#print axioms AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis
