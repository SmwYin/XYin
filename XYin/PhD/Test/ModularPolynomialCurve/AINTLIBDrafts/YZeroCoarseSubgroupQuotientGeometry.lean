/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.GroupScheme.SubgroupQuotient
public import AINTLIBDrafts.YZeroCoarseConstantAxis

/-!
# Flatness and universal closedness of the actual subgroup quotient

For an elliptic curve over an arbitrary scheme, the chosen nonzero killing integer
of a finite locally free subgroup supplies AINTLIB's actual gluing construction.
The local Hopf–Galois quotient projections are flat and surjective. The source
chart cover and quotient chart inclusions give flatness and surjectivity of the
glued projection, and the original curve's proper structure map then gives
universal closedness of the quotient structure map.

The public quotient wrappers use precisely the construction's chosen `killN` and
`killN_spec`. The constant-axis check uses the independently proved killing datum
of the literal marked subgroup over `Spec R`, including the subgroup of the
native marked curve pulled back from an actual full complex point at level 3.

These statements concern the raw quotient scheme. Finiteness of its projection,
properness, smoothness, and local Weierstrass presentations of its structure map
remain separate obligations before an elliptic curve record can be constructed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : E.FiniteLocallyFreeSubgroup)
  (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

/-- The actual glued quotient projection is flat, checked on its source chart cover. -/
theorem gluedQuotientπ_flat : Flat (G.gluedQuotientπ N hkill) := by
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @Flat)
    (G.glueCover N hkill)).mpr ?_
  intro i
  have : Module.Free (G.gluePatch N hkill i).baseRing (G.gluePatch N hkill i).groupRing :=
    G.free_gluePatch N hkill i
  have hflat : Flat (G.localQuotientOpenπ (G.gluePatch N hkill i).hstable) :=
    (G.gluePatch N hkill i).flat_and_surjective_localQuotientOpenπ.1
  change Flat ((G.gluePatch N hkill i).U.ι ≫ G.gluedQuotientπ N hkill)
  rw [G.ι_gluedQuotientπ N hkill i]
  exact @Flat.comp _ _ _ _ _ hflat (by
    change Flat ((G.quotientGlueData N hkill).ι i)
    have : IsOpenImmersion ((G.quotientGlueData N hkill).ι i) :=
      (G.quotientGlueData N hkill).ι_isOpenImmersion i
    infer_instance)

/-- Every point of the actual glued quotient lifts to a point of the original curve. -/
theorem gluedQuotientπ_surjective : Surjective (G.gluedQuotientπ N hkill) := by
  constructor
  intro y
  obtain ⟨i, z, hz⟩ := (G.quotientGlueData N hkill).ι_jointly_surjective y
  change (G.gluedQuotientι N hkill i).base z = y at hz
  have : Module.Free (G.gluePatch N hkill i).baseRing (G.gluePatch N hkill i).groupRing :=
    G.free_gluePatch N hkill i
  have : Surjective (G.localQuotientOpenπ (G.gluePatch N hkill i).hstable) :=
    (G.gluePatch N hkill i).flat_and_surjective_localQuotientOpenπ.2
  obtain ⟨x, hx⟩ := (G.localQuotientOpenπ (G.gluePatch N hkill i).hstable).surjective z
  refine ⟨(G.gluePatch N hkill i).U.ι.base x, ?_⟩
  have hleg := congrArg
    (fun f : (G.gluePatch N hkill i).U.toScheme ⟶ G.gluedQuotient N hkill ↦ f.base x)
    (G.ι_gluedQuotientπ N hkill i)
  simp only [gluedQuotientLeg, Scheme.Hom.comp_apply] at hleg
  rw [hx] at hleg
  exact hleg.trans hz

/-- Universal closedness of the original proper curve descends through this surjection. -/
theorem gluedQuotientS_universallyClosed :
    UniversallyClosed (G.gluedQuotientS N hkill) := by
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  have : UniversallyClosed (G.gluedQuotientπ N hkill ≫ G.gluedQuotientS N hkill) := by
    rw [G.gluedQuotientπ_gluedQuotientS N hkill]
    infer_instance
  exact UniversallyClosed.of_comp_surjective
    (G.gluedQuotientπ N hkill) (G.gluedQuotientS N hkill)

variable {N hkill}

/-- The public quotient projection is flat for its actual chosen killing integer. -/
theorem quotientπ_flat [G.HasKillingInt] : Flat G.quotientπ :=
  G.gluedQuotientπ_flat G.killN G.killN_spec

/-- The public quotient projection is surjective for its actual chosen killing integer. -/
theorem quotientπ_surjective [G.HasKillingInt] : Surjective G.quotientπ :=
  G.gluedQuotientπ_surjective G.killN G.killN_spec

/-- The public quotient structure map is universally closed. -/
theorem quotientS_universallyClosed [G.HasKillingInt] : UniversallyClosed G.quotientS :=
  G.gluedQuotientS_universallyClosed G.killN G.killN_spec

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

/-- The literal marked constant axis satisfies the three quotient properties over any base ring. -/
theorem sectionAxis_quotient_geometry (R : CommRingCat.{u}) (N : ℕ) [NeZero N]
    (E : EllipticCurve (Spec R)) (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    let G := sectionAxisSubgroup R N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
    Flat G.quotientπ ∧ Surjective G.quotientπ ∧ UniversallyClosed G.quotientS := by
  let G := sectionAxisSubgroup R N E hinv L
  have : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
  exact ⟨G.quotientπ_flat, G.quotientπ_surjective, G.quotientS_universallyClosed⟩

example (p : fullComplexSchemePoint 3 (by norm_num)) :
    let G := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    Flat G.quotientπ ∧ Surjective G.quotientπ ∧ UniversallyClosed G.quotientS :=
  sectionAxis_quotient_geometry (.of ℂ) 3 (fullComplexPointEllObj 3 (by norm_num) p).curve
    (complexLevelNIsInvertible 3) (fullComplexPointLevel 3 (by norm_num) p)

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis

#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.gluedQuotientπ_flat
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.gluedQuotientπ_surjective
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.gluedQuotientS_universallyClosed
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.quotientπ_flat
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.quotientπ_surjective
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.quotientS_universallyClosed
#print axioms ModularPolynomialCurveTest.AINTLIB.ConstantAxis.sectionAxis_quotient_geometry
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch.flat_and_surjective_localQuotientOpenπ
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.glueCover
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.free_gluePatch
#print axioms AlgebraicGeometry.Scheme.GlueData.ι_jointly_surjective
