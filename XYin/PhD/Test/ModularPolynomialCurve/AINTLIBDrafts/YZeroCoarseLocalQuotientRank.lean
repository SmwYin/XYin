/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseHopfStalkRank
public import AINTLIBDrafts.YZeroCoarseGroupRingStalkRank
public import ModularCurves.GroupScheme.SubgroupQuotientConstruction
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Actual local quotient fibre rank

For an actual affine chart patch, the canonical local quotient projection has
fibre finrank `r` when the genuine subgroup has `HasRank r`. A quotient-ring
prime lifts through the actual Hopf faithfully flat inclusion. The Hopf stalk-rank
comparison and the subgroup chart rank identify the coordinate-module stalk rank;
the literal affine chart isomorphism then identifies the scheme fibre rank.

The only additional hypothesis is freeness of this patch's group ring over its
base ring, as required by the actual Hopf datum. The two examples check the given
subgroup rank and the genuine marked-axis subgroup of rank `N`. Raw-subring and
global quotient ranks, and function-field degrees, are separate steps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

open ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
  (P : G.AffineChartPatch) [Module.Free P.baseRing P.groupRing]

/-- The actual canonical local quotient projection has the genuine subgroup rank. -/
theorem localQuotientπ_finrank (r : ℕ) (hG : G.HasRank r) (x : P.localQuotient) :
    P.localQuotientπ.finrank x = r := by
  have : Module.FaithfullyFlat (coinvariants P.chartCoaction) P.chartRing :=
    P.isHopfGalois_chartCoaction.faithfullyFlat
  have : Module.Finite (coinvariants P.chartCoaction) P.chartRing :=
    chartCoinvariants_finite P
  let p : PrimeSpectrum (coinvariants P.chartCoaction) := x
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := coinvariants P.chartCoaction) (B := P.chartRing) p
  have hcomp := coinvariants_rankAtStalk_eq P.isHopfGalois_chartCoaction q
  rw [hq] at hcomp
  have hrank : Module.rankAtStalk (R := coinvariants P.chartCoaction) P.chartRing p = r :=
    hcomp.trans (groupRing_rankAtStalk P r hG (q.comap (algebraMap P.baseRing P.chartRing)))
  let f : Spec P.chartRing ⟶ P.localQuotient :=
    Spec.map (CommRingCat.ofHom (algebraMap (coinvariants P.chartCoaction) P.chartRing))
  have : IsFinite f := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr
    (chartCoinvariants_finite P))
  have : Flat f := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  change (P.hU.isoSpec.hom ≫ f).finrank x = r
  rw [Scheme.Hom.finrank_comp_left_of_isIso]
  change (Spec.map (CommRingCat.ofHom
    (algebraMap (coinvariants P.chartCoaction) P.chartRing))).finrank p = r
  rw [Scheme.Hom.finrank_SpecMap_algebraMap]
  exact hrank

example (r : ℕ) (hG : G.HasRank r) : ∀ x : P.localQuotient, P.localQuotientπ.finrank x = r :=
  localQuotientπ_finrank P r hG

open ModularPolynomialCurveTest.AINTLIB.ConstantAxis

example (R : CommRingCat.{u}) (N : ℕ) [NeZero N] (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N)
    (P : (sectionAxisSubgroup R N E hinv L).AffineChartPatch)
    [Module.Free P.baseRing P.groupRing] (x : P.localQuotient) :
    P.localQuotientπ.finrank x = N :=
  localQuotientπ_finrank P N (sectionAxisSubgroup_hasRank R N E hinv L) x

#print axioms localQuotientπ_finrank
#print axioms coinvariants_rankAtStalk_eq
#print axioms groupRing_rankAtStalk
#print axioms isHopfGalois_chartCoaction
#print axioms ModularCurves.IsHopfGalois.faithfullyFlat
#print axioms chartCoinvariants_finite
#print axioms PrimeSpectrum.comap_surjective_of_faithfullyFlat
#print axioms localQuotientπ
#print axioms specEqualizerπ
#print axioms Scheme.Hom.finrank_SpecMap_algebraMap
#print axioms Scheme.Hom.finrank_comp_left_of_isIso
#print axioms IsFinite.SpecMap_iff
#print axioms Flat.SpecMap_iff

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch
