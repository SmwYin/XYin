/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseConstantAxis
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Etaleness of the actual marked constant-axis subgroup

The projection of the actual finite constant scheme is etale over any base
scheme: source-locality checks its identity components. The explicit local
source-locality instance is the existing mathlib instance, with its morphism
and ring-hom properties specified to avoid implicit-property unification in
the pinned AINTLIB compatibility context.

The actual axis subgroup structure map is this constant projection by the
proved section-axis triangle. The same theorem applies to the native curve
pulled back from an actual full-level complex point. Invertibility of `N` is
used only to construct the existing finite locally free subgroup; no quotient
projection is asserted to be etale by this leaf alone.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

/-- The actual finite constant-scheme projection is etale over any base scheme. -/
theorem constSchemeProjection_etale (S : Scheme.{u}) (A : Type) [Finite A] :
    Etale (constSchemeπ S A) := by
  have : IsZariskiLocalAtSource (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Etale)
      (Q := RingHom.Etale)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @AlgebraicGeometry.Etale)
    (fun _ ↦ inferInstance)

/-- The literal marked constant-axis subgroup has an etale structure map. -/
theorem sectionAxisSubgroup_etale (R : CommRingCat.{u}) (N : ℕ) [NeZero N]
    (E : EllipticCurve (Spec R)) (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    Etale (sectionAxisSubgroup R N E hinv L).π := by
  change Etale (sectionAxis (N := N) E L.val.1 ≫ E.π)
  rw [sectionAxis_π]
  exact constSchemeProjection_etale (Spec R) (ZMod N)

/-- The subgroup from an actual full complex point has the same etale structure map. -/
theorem fullComplexPointAxisSubgroup_etale (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (p : fullComplexSchemePoint N hN) : Etale (fullComplexPointAxisSubgroup N hN p).π :=
  sectionAxisSubgroup_etale (.of ℂ) N (fullComplexPointEllObj N hN p).curve
    (complexLevelNIsInvertible N) (fullComplexPointLevel N hN p)

example (S : Scheme.{u}) : Etale (constSchemeπ S (ZMod 5)) :=
  constSchemeProjection_etale S (ZMod 5)

example (p : fullComplexSchemePoint 3 (by norm_num)) :
    Etale (fullComplexPointAxisSubgroup 3 (by norm_num) p).π :=
  fullComplexPointAxisSubgroup_etale 3 (by norm_num) p

#print axioms constSchemeProjection_etale
#print axioms sectionAxisSubgroup_etale
#print axioms fullComplexPointAxisSubgroup_etale
#print axioms AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc
#print axioms sectionAxis_π

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis
