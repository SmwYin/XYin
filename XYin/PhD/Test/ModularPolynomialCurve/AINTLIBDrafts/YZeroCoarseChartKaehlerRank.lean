/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseHopfSmooth
public import AINTLIBDrafts.YZeroCoarseLocallyStandardSmoothRank
public import ModularCurves.GroupScheme.SubgroupQuotientGlueData

/-!
# Differential stalk rank one on actual elliptic curve chart patches

For an actual affine chart patch `P` of a finite locally free subgroup of a given
elliptic curve, the chart sections use the existing geometric scalar map from
the affine base-patch sections. The curve's relative-dimension-one smoothness
supplies the literal local standard-relative-dimension-one ring-hom condition
through `HasRingHomProperty.appLE` and the patch's affine-open witnesses.

The existing source-chart smoothness and the verified local-condition-to-rank
adapter then give rank one for the relative differential module at every prime
of the actual chart ring. The theorem requires only the actual patch and prime;
there are no additional group-patch freeness, étale, Noetherian, or domain
hypotheses, and no global standard smooth chart is assumed.

Sanities check the literal scalar-map identity, the arbitrary-patch interface,
and specialization to the actual canonical free gluing patches. The statement
concerns source-chart differentials. Coinvariant ranks and scheme-level relative
dimension descent remain separate proof steps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
  (P : G.AffineChartPatch)

/-- The actual elliptic curve chart has differential stalk rank one over its actual
affine base-patch ring, without requiring a global standard smooth chart. -/
theorem chartRing_kaehler_rankAtStalk (p : PrimeSpectrum P.chartRing) :
    Module.rankAtStalk (R := P.chartRing) Ω[P.chartRing⁄P.baseRing] p = 1 := by
  have : Algebra.Smooth P.baseRing P.chartRing := chartRing_smooth P
  have hlocal : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap P.baseRing P.chartRing) := by
    change RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (E.π.appLE P.V P.U P.hover).hom
    exact HasRingHomProperty.appLE (@SmoothOfRelativeDimension 1) E.π E.smooth
      ⟨P.V, P.hV⟩ ⟨P.U, P.hU⟩ P.hover
  exact RelativeDimension.kaehler_rankAtStalk_eq_of_locally_standardSmooth
    P.baseRing P.chartRing 1 hlocal p

example : algebraMap P.baseRing P.chartRing = (E.π.appLE P.V P.U P.hover).hom := rfl

example : ∀ p : PrimeSpectrum P.chartRing,
    Module.rankAtStalk (R := P.chartRing) Ω[P.chartRing⁄P.baseRing] p = 1 :=
  chartRing_kaehler_rankAtStalk P

example (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)
    (i : ↥E.E) (p : PrimeSpectrum (G.gluePatch N hkill i).chartRing) :
    Module.rankAtStalk (R := (G.gluePatch N hkill i).chartRing)
      Ω[(G.gluePatch N hkill i).chartRing⁄(G.gluePatch N hkill i).baseRing] p = 1 :=
  chartRing_kaehler_rankAtStalk (G.gluePatch N hkill i) p

#print axioms chartRing_kaehler_rankAtStalk
#print axioms chartRing_smooth
#print axioms RelativeDimension.kaehler_rankAtStalk_eq_of_locally_standardSmooth
#print axioms AlgebraicGeometry.HasRingHomProperty.appLE
#print axioms AlgebraicGeometry.SmoothOfRelativeDimension.smooth
#print axioms ModularCurves.EllipticCurveGeom.smooth
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.gluePatch
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.free_gluePatch

end ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft
