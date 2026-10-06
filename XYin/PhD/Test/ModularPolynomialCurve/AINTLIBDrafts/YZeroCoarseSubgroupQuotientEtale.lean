/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientChartPullback
public import AINTLIBDrafts.YZeroCoarseLocalQuotientGeometry
public import AINTLIBDrafts.YZeroCoarseConstantAxisEtale

/-!
# Etaleness of the actual subgroup quotient projection

For a finite locally free subgroup whose structure map is etale, the actual
local quotient projections are etale on the free affine patches of the glue
construction. The checked target-chart pullback identifies each target-local
projection with the local quotient projection preceded by an isomorphism.
Target-locality on the actual quotient chart cover then proves that the glued
quotient projection is etale.

The public quotient projection uses the construction's actual chosen killing
integer. For the literal constant-axis subgroup associated with a full marking
on an elliptic curve over `Spec R`, its already proved etale structure map
supplies the hypothesis. This leaf uses the actual subgroup and quotient
schemes and does not construct an elliptic curve structure on the quotient.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ModularCurves
open ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : E.FiniteLocallyFreeSubgroup)
  (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) [Etale G.π]

/-- An etale subgroup projection gives an actual etale glued quotient projection. -/
theorem gluedQuotientπ_etale : Etale (G.gluedQuotientπ N hkill) := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @Etale)
    (G.quotientGlueData N hkill).openCover).mpr ?_
  change ∀ i : ↥E.E, Etale
    (pullback.snd (G.gluedQuotientπ N hkill) (G.gluedQuotientι N hkill i))
  intro i
  have : Module.Free (G.gluePatch N hkill i).baseRing
      (G.gluePatch N hkill i).groupRing := G.free_gluePatch N hkill i
  have : Etale (G.localQuotientOpenπ (G.gluePatch N hkill i).hstable) :=
    localQuotientOpenπ_etale (G.gluePatch N hkill i)
  let h := (G.isPullback_localQuotientOpenπ_gluedQuotientπ N hkill i).flip
  rw [← h.isoPullback_inv_snd]
  infer_instance

/-- The chosen killing-integer construction has the same etale quotient projection. -/
theorem quotientπ_etale [G.HasKillingInt] : Etale G.quotientπ :=
  G.gluedQuotientπ_etale G.killN G.killN_spec

example [G.HasKillingInt] : Etale G.quotientπ := G.quotientπ_etale

#print axioms gluedQuotientπ_etale
#print axioms quotientπ_etale
#print axioms isPullback_localQuotientOpenπ_gluedQuotientπ
#print axioms free_gluePatch
#print axioms quotientπ

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

/-- The literal marked constant-axis subgroup has an actual etale quotient projection. -/
theorem sectionAxis_quotientπ_etale (R : CommRingCat.{u}) (N : ℕ) [NeZero N]
    (E : EllipticCurve (Spec R)) (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) :
    let G := sectionAxisSubgroup R N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
    Etale G.quotientπ := by
  let G := sectionAxisSubgroup R N E hinv L
  have : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
  have : Etale G.π := sectionAxisSubgroup_etale R N E hinv L
  exact G.quotientπ_etale

example (p : fullComplexSchemePoint 3 (by norm_num)) :
    let G := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    Etale G.quotientπ :=
  sectionAxis_quotientπ_etale (.of ℂ) 3 (fullComplexPointEllObj 3 (by norm_num) p).curve
    (complexLevelNIsInvertible 3) (fullComplexPointLevel 3 (by norm_num) p)

#print axioms sectionAxis_quotientπ_etale
#print axioms sectionAxisSubgroup_etale
#print axioms sectionAxisSubgroup_hasKillingInt

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis

#print axioms ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft.localQuotientOpenπ_etale
#print axioms AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover
#print axioms CategoryTheory.IsPullback.isoPullback_inv_snd
#print axioms AlgebraicGeometry.Etale.etale_comp
