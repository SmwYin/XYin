/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseChartKaehlerRank
public import AINTLIBDrafts.YZeroCoarseKaehlerRankDescent

/-!
# Differential stalk rank one on actual chart coinvariants

For an actual free affine chart patch with Noetherian base-patch ring and étale
subgroup projection, the retained smoothness and étaleness APIs apply to the
literal chart-coaction coinvariants and their canonical inclusion in the chart
ring. The actual Hopf--Galois datum supplies faithful flatness of that inclusion.

The constant-rank descent theorem lifts each coinvariant prime to a chart prime
and compares differential stalk ranks by formally étale base change. The actual
source-chart rank-one theorem therefore gives rank one on these coinvariants.
Smoothness of the coinvariant algebra supplies the finite and flat differential
module hypotheses, through existing instances.

The scalar tower is the canonical `R → C ⊆ B` tower. No ring-domain, globally
standard-smooth-chart, or assumed differential-rank hypothesis is introduced.
The two sanities exercise the arbitrary actual free patch and a canonical
gluing patch whose freeness is supplied by the actual gluing API.

This is a rank statement for the canonical coinvariant algebra. Transfer to the
raw quotient scalar map and scheme relative-dimension descent are separate steps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
  (P : G.AffineChartPatch)

/-- Actual chart coinvariants have differential stalk rank one over the actual
Noetherian base-patch ring, using the genuine étale faithfully flat chart inclusion. -/
theorem chartCoinvariants_kaehler_rankAtStalk [Module.Free P.baseRing P.groupRing]
    [Etale G.π] [IsNoetherianRing P.baseRing]
    (p : PrimeSpectrum (coinvariants P.chartCoaction)) :
    Module.rankAtStalk (R := coinvariants P.chartCoaction)
      Ω[coinvariants P.chartCoaction⁄P.baseRing] p = 1 := by
  have : Algebra.Smooth P.baseRing (coinvariants P.chartCoaction) :=
    chartCoinvariants_smooth P
  have : Algebra.Etale (coinvariants P.chartCoaction) P.chartRing :=
    chartCoinvariants_etale P
  have : Module.FaithfullyFlat (coinvariants P.chartCoaction) P.chartRing :=
    P.isHopfGalois_chartCoaction.faithfullyFlat
  exact RelativeDimension.kaehler_rankAtStalk_eq_of_formallyEtale_faithfullyFlat
    P.baseRing (coinvariants P.chartCoaction) P.chartRing 1
    (chartRing_kaehler_rankAtStalk P) p

example [Module.Free P.baseRing P.groupRing] [Etale G.π]
    [IsNoetherianRing P.baseRing] :
    ∀ p : PrimeSpectrum (coinvariants P.chartCoaction),
      Module.rankAtStalk (R := coinvariants P.chartCoaction)
        Ω[coinvariants P.chartCoaction⁄P.baseRing] p = 1 :=
  chartCoinvariants_kaehler_rankAtStalk P

example (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)
    (i : ↥E.E) [Etale G.π] [IsNoetherianRing (G.gluePatch N hkill i).baseRing]
    (p : PrimeSpectrum (coinvariants (G.gluePatch N hkill i).chartCoaction)) :
    Module.rankAtStalk (R := coinvariants (G.gluePatch N hkill i).chartCoaction)
      Ω[coinvariants (G.gluePatch N hkill i).chartCoaction⁄
        (G.gluePatch N hkill i).baseRing] p = 1 := by
  have : Module.Free (G.gluePatch N hkill i).baseRing
      (G.gluePatch N hkill i).groupRing := G.free_gluePatch N hkill i
  exact chartCoinvariants_kaehler_rankAtStalk (G.gluePatch N hkill i) p

#print axioms chartCoinvariants_kaehler_rankAtStalk
#print axioms RelativeDimension.kaehler_rankAtStalk_eq_of_formallyEtale_faithfullyFlat
#print axioms chartRing_kaehler_rankAtStalk
#print axioms chartCoinvariants_smooth
#print axioms chartCoinvariants_etale
#print axioms
  ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch.isHopfGalois_chartCoaction
#print axioms ModularCurves.IsHopfGalois.faithfullyFlat
#print axioms PrimeSpectrum.comap_surjective_of_faithfullyFlat
#print axioms Subalgebra.isScalarTower_mid
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.free_gluePatch

end ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft
