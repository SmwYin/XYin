/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientChartPullback
public import AINTLIBDrafts.YZeroCoarseLocalQuotientGeometry

/-!
# Finiteness of the actual subgroup quotient projection

For an elliptic curve over an arbitrary scheme and a finite locally free subgroup
with an explicit nonzero killing integer, AINTLIB's actual glued quotient
projection is finite. The proof checks the quotient target chart cover. Each
chart restriction is identified by the proved actual pullback square with its
local quotient projection, whose invariant-ring finiteness is already verified.
Transport is through the pullback comparison isomorphism.

The public projection uses the construction's chosen killing integer. The
constant-axis wrapper applies over any `Spec R` with invertible level and an
actual full marking; the sanity check uses an actual level-3 complex full point.
No domain, noetherian, or étale hypothesis is required for finiteness. No held
`NIsogeny` quotient-geometry theorem is used. The quotient elliptic curve upgrade
and its target-j remain separate conclusions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ModularCurves
open ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : E.FiniteLocallyFreeSubgroup)
  (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

/-- The actual glued quotient projection is finite, checked on its target quotient chart cover. -/
theorem gluedQuotientπ_isFinite : IsFinite (G.gluedQuotientπ N hkill) := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite)
    (G.quotientGlueData N hkill).openCover).mpr ?_
  change ∀ i : ↥E.E, IsFinite
    (pullback.snd (G.gluedQuotientπ N hkill) (G.gluedQuotientι N hkill i))
  intro i
  have : Module.Free (G.gluePatch N hkill i).baseRing
      (G.gluePatch N hkill i).groupRing := G.free_gluePatch N hkill i
  have : IsFinite (G.localQuotientOpenπ (G.gluePatch N hkill i).hstable) :=
    localQuotientOpenπ_isFinite (G.gluePatch N hkill i)
  let h := (G.isPullback_localQuotientOpenπ_gluedQuotientπ N hkill i).flip
  rw [← h.isoPullback_inv_snd]
  infer_instance

/-- The public quotient projection is finite for the construction's chosen killing integer. -/
theorem quotientπ_isFinite [G.HasKillingInt] : IsFinite G.quotientπ :=
  G.gluedQuotientπ_isFinite G.killN G.killN_spec

#print axioms gluedQuotientπ_isFinite
#print axioms quotientπ_isFinite
#print axioms isPullback_localQuotientOpenπ_gluedQuotientπ
#print axioms free_gluePatch

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

/-- The literal marked constant-axis subgroup has an actual finite quotient projection. -/
theorem sectionAxis_quotientπ_isFinite (R : CommRingCat.{u}) (N : ℕ) [NeZero N]
    (E : EllipticCurve (Spec R)) (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    let G := sectionAxisSubgroup R N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
    IsFinite G.quotientπ := by
  let G := sectionAxisSubgroup R N E hinv L
  have : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
  exact G.quotientπ_isFinite

example (p : fullComplexSchemePoint 3 (by norm_num)) :
    let G := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    IsFinite G.quotientπ :=
  sectionAxis_quotientπ_isFinite (.of ℂ) 3 (fullComplexPointEllObj 3 (by norm_num) p).curve
    (complexLevelNIsInvertible 3) (fullComplexPointLevel 3 (by norm_num) p)

#print axioms sectionAxis_quotientπ_isFinite

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis

#print axioms ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft.localQuotientOpenπ_isFinite
#print axioms AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover
#print axioms AlgebraicGeometry.IsFinite.SpecMap_iff
#print axioms CategoryTheory.IsPullback.isoPullback_inv_snd
