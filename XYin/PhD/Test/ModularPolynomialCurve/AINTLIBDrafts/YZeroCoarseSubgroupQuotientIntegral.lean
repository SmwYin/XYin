/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Properties
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientGeometry
public import ModularCurves.EllipticCurve.IntegralOverField

/-!
# Integrality of the actual subgroup quotient over a field

Reducedness descends along any flat surjective morphism by the injectivity
of its faithfully flat local stalk maps. For an integral source, continuous
surjective image irreducibility supplies integrality of the target as well.
Neither generic result needs quasi-compactness or a Noetherian hypothesis.

For a native elliptic curve over an arbitrary field, its existing local
Weierstrass model makes the original curve integral. Applying the generic
descent to the actual raw subgroup quotient projection proves that quotient
integral. The public wrapper uses its actual chosen killing integer; the
marked-axis wrapper applies over every field with invertible level.

This is an integral scheme and function-field prerequisite. It does not
supply a quotient Weierstrass model, genus, or a target j-invariant. In
particular, the raw quotient is not assumed to be an elliptic curve.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Reducedness descends along a flat surjective scheme morphism. -/
theorem isReduced_of_flat_surjective (f : X ⟶ Y) [Flat f] [Surjective f]
    [IsReduced X] : IsReduced Y := by
  have : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := by
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    apply _root_.isReduced_of_injective (f.stalkMap x).hom
    algebraize [(f.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap f x) (f.toLRSHom.prop x)
    exact ‹RingHom.FaithfullyFlat _›.injective
  exact isReduced_of_isReduced_stalk Y

/-- An integral source has integral target under a flat surjective morphism. -/
theorem isIntegral_of_flat_surjective (f : X ⟶ Y) [Flat f] [Surjective f]
    [IsIntegral X] : IsIntegral Y := by
  have : IsReduced Y := isReduced_of_flat_surjective f
  have : IrreducibleSpace Y := f.surjective.irreducibleSpace f.continuous
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

example [IsReduced X] : IsReduced X := isReduced_of_flat_surjective (𝟙 X)

example [IsIntegral X] : IsIntegral X := isIntegral_of_flat_surjective (𝟙 X)

#print axioms isReduced_of_flat_surjective
#print axioms isIntegral_of_flat_surjective
#print axioms isReduced_of_isReduced_stalk
#print axioms Flat.stalkMap
#print axioms Module.FaithfullyFlat.of_flat_of_isLocalHom
#print axioms RingHom.FaithfullyFlat.injective
#print axioms isIntegral_of_irreducibleSpace_of_isReduced
#print axioms Function.Surjective.irreducibleSpace

end AlgebraicGeometry

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

open AlgebraicGeometry CategoryTheory

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

/-- The actual raw subgroup quotient of an elliptic curve over a field is integral. -/
theorem gluedQuotient_isIntegral : IsIntegral (G.gluedQuotient N hkill) := by
  have : Flat (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_flat N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  exact isIntegral_of_flat_surjective (G.gluedQuotientπ N hkill)

/-- Integrality for the public quotient with its actual chosen killing integer. -/
theorem quotient_isIntegral [G.HasKillingInt] : IsIntegral G.quotient :=
  G.gluedQuotient_isIntegral G.killN G.killN_spec

example [G.HasKillingInt] : IsIntegral G.quotient := G.quotient_isIntegral

#print axioms gluedQuotient_isIntegral
#print axioms quotient_isIntegral
#print axioms ModularCurves.EllipticCurve.isIntegral_of_field

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

open AlgebraicGeometry CategoryTheory ModularCurves

/-- The literal marked-axis quotient is integral over every field. -/
theorem sectionAxis_quotient_isIntegral (k : Type u) [Field k] (N : ℕ) [NeZero N]
    (E : EllipticCurve (Spec (.of k))) (hinv : NIsInvertible (Spec (.of k)) N)
    (L : E.FullLevelPt N) :
    let G := sectionAxisSubgroup (.of k) N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt (.of k) N E hinv L
    IsIntegral G.quotient := by
  let G := sectionAxisSubgroup (.of k) N E hinv L
  have : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt (.of k) N E hinv L
  exact G.quotient_isIntegral

example (p : fullComplexSchemePoint 3 (by norm_num)) :
    let G := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    IsIntegral G.quotient :=
  sectionAxis_quotient_isIntegral ℂ 3 (fullComplexPointEllObj 3 (by norm_num) p).curve
    (complexLevelNIsInvertible 3) (fullComplexPointLevel 3 (by norm_num) p)

#print axioms sectionAxis_quotient_isIntegral

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis
