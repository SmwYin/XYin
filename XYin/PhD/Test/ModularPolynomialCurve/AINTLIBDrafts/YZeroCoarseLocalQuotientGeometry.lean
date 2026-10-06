/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseHopfFinite
public import AINTLIBDrafts.YZeroCoarseHopfEtale
public import ModularCurves.GroupScheme.SubgroupQuotientGlue
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Finite and etale actual local subgroup quotient projections

On an actual free affine chart patch, the literal invariant section inclusion is finite.
The existing equality with the chart coaction's coinvariants transfers the retained
finite-module result to this inclusion. Since the local quotient projection is the
chart's actual `toSpecΓ` isomorphism followed by the spectrum of this inclusion, it is finite.

If the actual subgroup projection `G.π` is etale, the same invariant-ring equality and
the retained chart etaleness theorem make the inclusion and local quotient projection
etale. This additional geometric hypothesis is explicit in both etale declarations;
it is not required by the finite declarations. The statements use the existing local
freeness prerequisite of the chart Hopf-Galois theorem and need no domain or Noetherian
hypothesis. Global quotient properties require the separate target-chart pullback bridge.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

noncomputable section

universe u

namespace ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
  (P : G.AffineChartPatch) [Module.Free P.baseRing P.groupRing]

/-- The actual invariant section inclusion on a free affine patch is finite. -/
theorem quotientRing_subtype_finite : (G.quotientRing P.hstable).subtype.Finite := by
  rw [P.quotientRing_eq_coinvariants]
  change (algebraMap (coinvariants P.chartCoaction) P.chartRing).Finite
  exact RingHom.finite_algebraMap.mpr (chartCoinvariants_finite P)

/-- The actual local quotient projection on a free affine patch is finite. -/
theorem localQuotientOpenπ_isFinite : IsFinite (G.localQuotientOpenπ P.hstable) := by
  let : IsIso P.U.toSpecΓ := P.isIso_toSpecΓ_U
  let : IsFinite P.U.toSpecΓ := inferInstance
  let : IsFinite (Spec.map (CommRingCat.ofHom (G.quotientRing P.hstable).subtype)) :=
    (IsFinite.SpecMap_iff _).mpr (quotientRing_subtype_finite P)
  rw [EllipticCurve.FiniteLocallyFreeSubgroup.localQuotientOpenπ]
  exact MorphismProperty.IsStableUnderComposition.comp_mem (P := @IsFinite)
    P.U.toSpecΓ (Spec.map (CommRingCat.ofHom (G.quotientRing P.hstable).subtype))
    inferInstance inferInstance

example : IsFinite (G.localQuotientOpenπ P.hstable) := localQuotientOpenπ_isFinite P

variable [Etale G.π]

/-- An etale subgroup projection makes the actual invariant section inclusion etale. -/
theorem quotientRing_subtype_etale : (G.quotientRing P.hstable).subtype.Etale := by
  rw [P.quotientRing_eq_coinvariants]
  change (algebraMap (coinvariants P.chartCoaction) P.chartRing).Etale
  exact RingHom.etale_algebraMap.mpr (chartCoinvariants_etale P)

/-- An etale subgroup projection makes the actual local quotient projection etale. -/
theorem localQuotientOpenπ_etale : Etale (G.localQuotientOpenπ P.hstable) := by
  let : IsIso P.U.toSpecΓ := P.isIso_toSpecΓ_U
  let : Etale P.U.toSpecΓ := inferInstance
  let : Etale (Spec.map (CommRingCat.ofHom (G.quotientRing P.hstable).subtype)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (quotientRing_subtype_etale P)
  rw [EllipticCurve.FiniteLocallyFreeSubgroup.localQuotientOpenπ]
  exact MorphismProperty.IsStableUnderComposition.comp_mem (P := @Etale)
    P.U.toSpecΓ (Spec.map (CommRingCat.ofHom (G.quotientRing P.hstable).subtype))
    inferInstance inferInstance

example : Etale (G.localQuotientOpenπ P.hstable) := localQuotientOpenπ_etale P

#print axioms quotientRing_subtype_finite
#print axioms localQuotientOpenπ_isFinite
#print axioms chartCoinvariants_finite
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch.quotientRing_eq_coinvariants
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch.isIso_toSpecΓ_U
#print axioms ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.localQuotientOpenπ
#print axioms AlgebraicGeometry.IsFinite.SpecMap_iff
#print axioms RingHom.finite_algebraMap
#print axioms quotientRing_subtype_etale
#print axioms localQuotientOpenπ_etale
#print axioms chartCoinvariants_etale
#print axioms AlgebraicGeometry.HasRingHomProperty.Spec_iff
#print axioms RingHom.etale_algebraMap

end ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft
