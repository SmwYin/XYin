/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseHopfFinite
public import AINTLIBDrafts.YZeroCoarseHopfEtale
public import AINTLIBDrafts.YZeroCoarseLocalQuotientFiniteType
public import ModularCurves.ForMathlib.EtaleSmoothDescent

/-!
# Smoothness of actual stable-chart sections and their coinvariants

The chart algebra is the existing geometric `appLE` algebra of the elliptic
curve structure map. Its smoothness follows directly from that structure
map's actual relative-dimension-one smoothness, with no assumed chart-ring
smoothness or extra base hypothesis.

On a free affine chart patch with Noetherian base ring and etale subgroup
projection, the retained finite and etale coinvariant inclusion and the
actual Hopf-Galois faithfully flat field allow the clean algebraic smooth
descent theorem to prove smoothness of the literal coaction coinvariants
over that base ring. The scalar tower is the canonical subalgebra tower.

The actual raw equalizer-subring quotient uses the explicitly fixed geometric
scalar map `quotientBaseHom`. Its proved algebra equivalence with the canonical
coinvariants transfers the same smoothness result, and the corresponding
ring-hom smooth property concerns this literal scalar map.

This leaf proves algebra smoothness. A statement about the actual quotient
scheme structure map requires the separate geometric factorization triangle.
-/

@[expose] public section

open AlgebraicGeometry ModularCurves

universe u

namespace ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
  (P : G.AffineChartPatch)

/-- The actual chart sections are smooth over their actual affine base-patch sections. -/
theorem chartRing_smooth : Algebra.Smooth P.baseRing P.chartRing := by
  have : Smooth E.π := SmoothOfRelativeDimension.smooth (n := 1) (f := E.π)
  have h : (algebraMap P.baseRing P.chartRing).Smooth :=
    E.π.smooth_appLE P.hV P.hU P.hover
  exact RingHom.smooth_algebraMap.mp h

example : (algebraMap P.baseRing P.chartRing).Smooth :=
  RingHom.smooth_algebraMap.mpr (chartRing_smooth P)

/-- Actual chart coinvariants are smooth over a Noetherian base-patch ring. -/
theorem chartCoinvariants_smooth [Module.Free P.baseRing P.groupRing]
    [Etale G.π] [IsNoetherianRing P.baseRing] :
    Algebra.Smooth P.baseRing (coinvariants P.chartCoaction) := by
  have : Algebra.Smooth P.baseRing P.chartRing := chartRing_smooth P
  have : Module.Finite (coinvariants P.chartCoaction) P.chartRing :=
    chartCoinvariants_finite P
  have : Algebra.Etale (coinvariants P.chartCoaction) P.chartRing :=
    chartCoinvariants_etale P
  have : Module.FaithfullyFlat (coinvariants P.chartCoaction) P.chartRing :=
    P.isHopfGalois_chartCoaction.faithfullyFlat
  exact Algebra.smooth_of_etale_faithfullyFlat P.baseRing
    (coinvariants P.chartCoaction) P.chartRing

example [Module.Free P.baseRing P.groupRing] [Etale G.π]
    [IsNoetherianRing P.baseRing] :
    (algebraMap P.baseRing (coinvariants P.chartCoaction)).Smooth :=
  RingHom.smooth_algebraMap.mpr (chartCoinvariants_smooth P)

#print axioms chartRing_smooth
#print axioms chartCoinvariants_smooth
#print axioms Algebra.smooth_of_etale_faithfullyFlat
#print axioms Algebra.projective_kaehlerDifferential_of_formallyEtale_faithfullyFlat
#print axioms Algebra.subsingleton_h1Cotangent_of_etale_faithfullyFlat
#print axioms Algebra.tensorH1CotangentOfIsStandardEtale
#print axioms fg_of_fg_of_fg
#print axioms RingHom.smooth_algebraMap
#print axioms AlgebraicGeometry.Smooth.smooth_appLE
#print axioms AlgebraicGeometry.SmoothOfRelativeDimension.smooth
#print axioms chartCoinvariants_finite
#print axioms chartCoinvariants_etale
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch.isHopfGalois_chartCoaction
#print axioms Subalgebra.isScalarTower_mid
#print axioms ModularCurves.EllipticCurveGeom.smooth

end ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

open ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
  (P : G.AffineChartPatch) [Module.Free P.baseRing P.groupRing]
  [Etale G.π] [IsNoetherianRing P.baseRing]

/-- The actual raw quotient ring is smooth for its explicitly fixed geometric scalar map. -/
theorem quotientRing_smooth :
    let _ : Algebra P.baseRing (G.quotientRing P.hstable) := (quotientBaseHom P).toAlgebra
    Algebra.Smooth P.baseRing (G.quotientRing P.hstable) := by
  let : Algebra P.baseRing (G.quotientRing P.hstable) := (quotientBaseHom P).toAlgebra
  have : Algebra.Smooth P.baseRing (coinvariants P.chartCoaction) := chartCoinvariants_smooth P
  exact Algebra.Smooth.of_equiv (quotientCoinvariantsAlgEquiv P).symm

/-- The actual raw quotient scalar ring homomorphism is smooth. -/
theorem quotientBaseHom_smooth : (quotientBaseHom P).Smooth := by
  let : Algebra P.baseRing (G.quotientRing P.hstable) := (quotientBaseHom P).toAlgebra
  exact RingHom.smooth_algebraMap.mpr (quotientRing_smooth P)

example :
    let _ : Algebra P.baseRing (G.quotientRing P.hstable) := (quotientBaseHom P).toAlgebra
    Algebra.Smooth P.baseRing (G.quotientRing P.hstable) :=
  quotientRing_smooth P

example : (quotientBaseHom P).Smooth := quotientBaseHom_smooth P

#print axioms quotientRing_smooth
#print axioms quotientBaseHom_smooth
#print axioms quotientBaseHom
#print axioms quotientBaseHom_comp_subtype
#print axioms quotientCoinvariantsAlgEquiv
#print axioms Algebra.Smooth.of_equiv
#print axioms RingHom.smooth_algebraMap
#print axioms ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft.chartCoinvariants_smooth
#print axioms quotientRing_eq_coinvariants

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch
