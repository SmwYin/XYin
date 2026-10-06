/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseHopfSmooth
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientFiniteType
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientEtale

/-!
# Smoothness of the actual subgroup quotient structure map

For a finite locally free subgroup with an etale structure map, smoothness
of the actual affine quotient ring over a Noetherian base patch identifies
its local quotient structure map as smooth. The actual source chart cover,
its free patches, and the checked structural triangles then assemble this
into smoothness of the glued quotient over a locally Noetherian base.

The public quotient uses the actual chosen killing integer. A full marking
on an elliptic curve over `Spec R`, with invertible level, supplies the etale
subgroup input for the literal constant-axis subgroup. This leaf proves
smoothness of the actual scheme structure map. Relative dimension, genus,
an elliptic curve model, and a target j-invariant require further proofs.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
  (P : G.AffineChartPatch)

/-- The actual local quotient structure map is smooth over its affine base patch. -/
theorem quotientToBase_smooth [Module.Free P.baseRing P.groupRing]
    [Etale G.π] [IsNoetherianRing P.baseRing] : Smooth P.quotientToBase := by
  have hf : Smooth (Spec.map (CommRingCat.ofHom P.quotientBaseHom)) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth) (Q := RingHom.Smooth)).mpr
      P.quotientBaseHom_smooth
  change Smooth (Spec.map (CommRingCat.ofHom P.quotientBaseHom) ≫ P.hV.isoSpec.inv)
  exact MorphismProperty.comp_mem (@Smooth) _ _ hf (inferInstance)

#print axioms quotientToBase_smooth
#print axioms quotientToBase
#print axioms localQuotientOpenπ_quotientToBase
#print axioms quotientBaseHom_smooth

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : E.FiniteLocallyFreeSubgroup)
  (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)
  [Etale G.π] [IsLocallyNoetherian S]

/-- The actual glued quotient structure map is smooth over a locally Noetherian base. -/
theorem gluedQuotientS_smooth : Smooth (G.gluedQuotientS N hkill) := by
  have : IsZariskiLocalAtSource (@Smooth : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth) (Q := RingHom.Smooth)
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth)
    (f := G.gluedQuotientS N hkill) (G.quotientGlueData N hkill).openCover).mpr ?_
  change ∀ i : ↥E.E, Smooth (G.gluedQuotientι N hkill i ≫ G.gluedQuotientS N hkill)
  intro i
  have : Module.Free (G.gluePatch N hkill i).baseRing
      (G.gluePatch N hkill i).groupRing := G.free_gluePatch N hkill i
  have : IsNoetherianRing (G.gluePatch N hkill i).baseRing :=
    IsLocallyNoetherian.component_noetherian
      ⟨(G.gluePatch N hkill i).V, (G.gluePatch N hkill i).hV⟩
  rw [G.gluedQuotientι_gluedQuotientS N hkill i]
  have hf : Smooth (G.gluePatch N hkill i).quotientToBase :=
    (G.gluePatch N hkill i).quotientToBase_smooth
  exact MorphismProperty.comp_mem (@Smooth) _ _ hf (inferInstance)

/-- The public chosen-killing quotient has the same smooth structure map. -/
theorem quotientS_smooth [G.HasKillingInt] : Smooth G.quotientS :=
  G.gluedQuotientS_smooth G.killN G.killN_spec

example [G.HasKillingInt] : Smooth G.quotientS := G.quotientS_smooth

#print axioms gluedQuotientS_smooth
#print axioms quotientS_smooth
#print axioms gluedQuotientι_gluedQuotientS
#print axioms free_gluePatch

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

/-- The literal marked constant-axis quotient is smooth over every Noetherian base ring. -/
theorem sectionAxis_quotientS_smooth (R : CommRingCat.{u}) [IsNoetherianRing R]
    (N : ℕ) [NeZero N] (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    let G := sectionAxisSubgroup R N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
    Smooth G.quotientS := by
  let G := sectionAxisSubgroup R N E hinv L
  have : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
  have : Etale G.π := sectionAxisSubgroup_etale R N E hinv L
  exact G.quotientS_smooth

example (p : fullComplexSchemePoint 3 (by norm_num)) :
    let G := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    Smooth G.quotientS :=
  sectionAxis_quotientS_smooth (.of ℂ) 3 (fullComplexPointEllObj 3 (by norm_num) p).curve
    (complexLevelNIsInvertible 3) (fullComplexPointLevel 3 (by norm_num) p)

#print axioms sectionAxis_quotientS_smooth
#print axioms sectionAxisSubgroup_etale
#print axioms sectionAxisSubgroup_hasKillingInt

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis

namespace AlgebraicGeometry

#print axioms IsLocallyNoetherian.component_noetherian
#print axioms HasRingHomProperty.Spec_iff
#print axioms IsZariskiLocalAtSource.iff_of_openCover
#print axioms HasRingHomProperty.instIsZariskiLocalAtSource

end AlgebraicGeometry
