/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseHopfGaloisLeft
public import Mathlib.RingTheory.Etale.Descent
public import ModularCurves.GroupScheme.StableChartData

/-!
# Etaleness of a Hopf-Galois extension and actual chart sections

If the coefficient algebra is etale, the retained left-factor canonical Galois
algebra equivalence identifies its base change with the base change of the
coinvariant inclusion. The actual Hopf-Galois faithfully flat field then descends
etaleness of that inclusion. No domain, Noetherian, or finite-module assumption
is needed for this algebraic theorem.

For an actual affine chart patch, etaleness of the group projection gives the
etale group-ring algebra through its literal geometric `appLE` map. Combined
with the actual free-patch Hopf-Galois theorem, this yields etaleness of the
chart sections over their literal coinvariants. The group-projection hypothesis
is explicit; etaleness of a constant axis or of a global quotient projection
requires further geometric proofs.
-/

@[expose] public section

open AlgebraicGeometry ModularCurves
open scoped TensorProduct

universe u

namespace ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

variable {R0 A B : Type*} [CommRing R0] [CommRing A] [CommRing B]
  [Algebra R0 A] [Algebra R0 B] {ρ : B →ₐ[R0] B ⊗[R0] A}

/-- An etale coefficient algebra makes a Hopf-Galois extension etale over its coinvariants. -/
theorem coinvariants_etale [Algebra.Etale R0 A] (h : IsHopfGalois ρ) :
    Algebra.Etale (coinvariants ρ) B := by
  have : Module.FaithfullyFlat (coinvariants ρ) B := h.faithfullyFlat
  have : Algebra.Etale B (B ⊗[R0] A) := inferInstance
  have : Algebra.Etale B (B ⊗[coinvariants ρ] B) :=
    Algebra.Etale.of_equiv (galoisEquivOverLeft h).symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat B

/-- The actual etale group projection induces the literal etale group-ring algebra. -/
theorem chartGroupRing_etale {S : Scheme.{u}} {E : EllipticCurve S}
    {G : E.FiniteLocallyFreeSubgroup} (P : G.AffineChartPatch) [Etale G.π] :
    Algebra.Etale P.baseRing P.groupRing := by
  have h : (algebraMap P.baseRing P.groupRing).Etale :=
    G.π.etale_appLE P.hV P.isAffineOpen_groupOpen le_rfl
  exact RingHom.etale_algebraMap.mp h

/-- Actual free stable-chart sections are etale over their literal coaction coinvariants. -/
theorem chartCoinvariants_etale {S : Scheme.{u}} {E : EllipticCurve S}
    {G : E.FiniteLocallyFreeSubgroup} (P : G.AffineChartPatch)
    [Module.Free P.baseRing P.groupRing] [Etale G.π] :
    Algebra.Etale (coinvariants P.chartCoaction) P.chartRing := by
  have : Algebra.Etale P.baseRing P.groupRing := chartGroupRing_etale P
  exact coinvariants_etale P.isHopfGalois_chartCoaction

example [Algebra.Etale R0 A] (h : IsHopfGalois ρ) :
    (algebraMap (coinvariants ρ) B).Etale :=
  RingHom.etale_algebraMap.mpr (coinvariants_etale h)

example {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
    (P : G.AffineChartPatch) [Module.Free P.baseRing P.groupRing] [Etale G.π] :
    Algebra.Etale (coinvariants P.chartCoaction) P.chartRing :=
  chartCoinvariants_etale P

#print axioms coinvariants_etale
#print axioms chartGroupRing_etale
#print axioms chartCoinvariants_etale
#print axioms Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat
#print axioms Algebra.Etale.of_equiv
#print axioms Algebra.Etale.baseChange
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch.isHopfGalois_chartCoaction
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch.isAffineOpen_groupOpen

end ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft
