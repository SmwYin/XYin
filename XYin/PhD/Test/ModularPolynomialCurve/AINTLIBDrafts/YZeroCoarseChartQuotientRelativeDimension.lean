/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseChartCoinvariantsKaehlerRank
public import AINTLIBDrafts.YZeroCoarseSmoothRankCriterion

/-!
# Local relative dimension one for actual chart quotient scalars

For an actual affine chart patch of a finite locally free subgroup of an
elliptic curve, the canonical chart coinvariants are locally standard smooth
of relative dimension one over the actual base-patch ring. This combines the
retained actual coinvariant smoothness and differential-rank-one theorems with
the smooth differential-rank criterion.

The actual raw quotient ring carries the explicit scalar map `quotientBaseHom`.
Its existing algebra equivalence to the chart coinvariants respects these
scalars. Postcomposition by the inverse equivalence transports the local
standard-smooth condition to the literal raw scalar map.

Both statements require the actual free group chart, an étale subgroup
projection, and a Noetherian base-patch ring. No domain, globally standard
smooth chart, or assumed differential-rank condition is used. The examples
exercise an arbitrary actual free patch and a canonical gluing patch, whose
freeness is supplied by the actual gluing API.

These are local algebra conditions. They concern the chart quotient ring,
with its literal geometric scalar map; scheme gluing, global relative
dimension, and the quotient elliptic curve upgrade are separate steps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
  (P : G.AffineChartPatch)

/-- The canonical chart coinvariant scalar map is locally standard smooth of dimension one. -/
theorem chartCoinvariants_locally_standardSmoothRelDim_one
    [Module.Free P.baseRing P.groupRing] [Etale G.π] [IsNoetherianRing P.baseRing] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap P.baseRing (coinvariants P.chartCoaction)) := by
  have : Algebra.Smooth P.baseRing (coinvariants P.chartCoaction) :=
    chartCoinvariants_smooth P
  exact RelativeDimension.locally_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk
    P.baseRing (coinvariants P.chartCoaction) 1 (chartCoinvariants_kaehler_rankAtStalk P)

example [Module.Free P.baseRing P.groupRing] [Etale G.π]
    [IsNoetherianRing P.baseRing] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap P.baseRing (coinvariants P.chartCoaction)) :=
  chartCoinvariants_locally_standardSmoothRelDim_one P

#print axioms chartCoinvariants_locally_standardSmoothRelDim_one
#print axioms RelativeDimension.locally_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk
#print axioms chartCoinvariants_smooth
#print axioms chartCoinvariants_kaehler_rankAtStalk

end ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

open ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
  (P : G.AffineChartPatch)

/-- The actual raw quotient scalar map is locally standard smooth of dimension one. -/
theorem quotientBaseHom_locally_standardSmoothRelDim_one
    [Module.Free P.baseRing P.groupRing] [Etale G.π] [IsNoetherianRing P.baseRing] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) P.quotientBaseHom := by
  let : Algebra P.baseRing (G.quotientRing P.hstable) := P.quotientBaseHom.toAlgebra
  let e : G.quotientRing P.hstable ≃ₐ[P.baseRing] coinvariants P.chartCoaction :=
    P.quotientCoinvariantsAlgEquiv
  have hC := chartCoinvariants_locally_standardSmoothRelDim_one P
  have h :=
    (RingHom.locally_respectsIso
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1))).1
        (algebraMap P.baseRing (coinvariants P.chartCoaction)) e.symm.toRingEquiv hC
  have hscalar : e.symm.toRingEquiv.toRingHom.comp
      (algebraMap P.baseRing (coinvariants P.chartCoaction)) = P.quotientBaseHom := by
    apply RingHom.ext
    intro r
    change e.symm (algebraMap P.baseRing (coinvariants P.chartCoaction) r) =
      algebraMap P.baseRing (G.quotientRing P.hstable) r
    exact e.symm.commutes r
  simpa only [hscalar] using h

example (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)
    (i : ↥E.E) [Etale G.π] [IsNoetherianRing (G.gluePatch N hkill i).baseRing] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (G.gluePatch N hkill i).quotientBaseHom := by
  have : Module.Free (G.gluePatch N hkill i).baseRing
      (G.gluePatch N hkill i).groupRing := G.free_gluePatch N hkill i
  exact quotientBaseHom_locally_standardSmoothRelDim_one (G.gluePatch N hkill i)

#print axioms quotientBaseHom_locally_standardSmoothRelDim_one
#print axioms quotientBaseHom
#print axioms quotientCoinvariantsAlgEquiv
#print axioms RingHom.locally_respectsIso
#print axioms RingHom.isStandardSmoothOfRelativeDimension_respectsIso
#print axioms AlgEquiv.commutes
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.free_gluePatch

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch
