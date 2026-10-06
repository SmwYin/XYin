/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientGeometry

/-!
# The actual subgroup quotient chart pullback

For an elliptic curve over an arbitrary scheme and a finite locally free subgroup
with an explicit nonzero killing integer, each chart in AINTLIB's actual glued
quotient has precisely the corresponding stable source patch as its preimage.

Equality of two points in the glued quotient gives a single actual overlap
witness through `Scheme.GlueData.ι_eq_iff`. Its first equation places the local
quotient point in the saturated overlap image. The existing
`AffineChartPatch.preimage_imageOpens` then puts the original curve point in the
intersection of the two stable source patches. The reverse inclusion follows
from the literal local-to-global projection triangle.

The resulting open preimage equality and `IsOpenImmersion.isPullback` identify
the actual local projection as the target-chart pullback of the global one.
The chart open-immersion instance is local to this file. The level-3 sanity uses
the literal constant-axis subgroup of an actual native marked complex curve.
Finiteness and the quotient elliptic curve upgrade remain separate conclusions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : E.FiniteLocallyFreeSubgroup)
  (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

local instance gluedQuotientι_open (i : ↥E.E) :
    IsOpenImmersion (G.gluedQuotientι N hkill i) :=
  (G.quotientGlueData N hkill).ι_isOpenImmersion i

/-- The actual quotient chart has precisely the corresponding stable source patch as preimage. -/
theorem gluedQuotientπ_preimage_gluedQuotientι (i : ↥E.E) :
    G.gluedQuotientπ N hkill ⁻¹ᵁ (G.gluedQuotientι N hkill i).opensRange =
      (G.gluePatch N hkill i).U := by
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  constructor
  · intro hx
    change ∃ z, (G.gluedQuotientι N hkill i).base z =
      (G.gluedQuotientπ N hkill).base x at hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨j, u, hu⟩ : ∃ (j : ↥E.E) (u : (G.gluePatch N hkill j).U.toScheme),
        (G.gluePatch N hkill j).U.ι.base u = x := (G.glueCover N hkill).exists_eq x
    have : Module.Free (G.gluePatch N hkill j).baseRing
        (G.gluePatch N hkill j).groupRing := G.free_gluePatch N hkill j
    let b := (G.localQuotientOpenπ (G.gluePatch N hkill j).hstable).base u
    have hleg := congrArg
      (fun f : (G.gluePatch N hkill j).U.toScheme ⟶ G.gluedQuotient N hkill ↦ f.base u)
      (G.ι_gluedQuotientπ N hkill j)
    simp only [gluedQuotientLeg, Scheme.Hom.comp_apply] at hleg
    have hEq : ((G.quotientGlueData N hkill).ι j).base b =
        ((G.quotientGlueData N hkill).ι i).base z :=
      hleg.symm.trans ((congrArg (G.gluedQuotientπ N hkill).base hu).trans hz.symm)
    obtain ⟨v, hv, _⟩ := (G.quotientGlueData N hkill).ι_eq_iff j i b z |>.mp hEq
    have hb : b ∈ (G.gluePatch N hkill j).imageOpens
        (G.glueW_stable N hkill j i) inf_le_left := by
      change b ∈ ((G.gluePatch N hkill j).imageOpens
        (G.glueW_stable N hkill j i) inf_le_left : Set _)
      rw [← Scheme.Opens.range_ι]
      exact ⟨v, hv⟩
    have huW : u ∈ (G.gluePatch N hkill j).U.ι ⁻¹ᵁ
        ((G.gluePatch N hkill j).U ⊓ (G.gluePatch N hkill i).U) := by
      rw [← (G.gluePatch N hkill j).preimage_imageOpens
        (G.glueW_stable N hkill j i) inf_le_left]
      exact hb
    have hxW : (G.gluePatch N hkill j).U.ι.base u ∈
        (G.gluePatch N hkill j).U ⊓ (G.gluePatch N hkill i).U := huW
    exact hu ▸ hxW.2
  · intro hx
    obtain ⟨u, hu⟩ : ∃ u, (G.gluePatch N hkill i).U.ι.base u = x := by
      change x ∈ Set.range (G.gluePatch N hkill i).U.ι
      simpa only [Scheme.Opens.range_ι] using hx
    change ∃ z, (G.gluedQuotientι N hkill i).base z =
      (G.gluedQuotientπ N hkill).base x
    refine ⟨(G.localQuotientOpenπ (G.gluePatch N hkill i).hstable).base u, ?_⟩
    have hleg := congrArg
      (fun f : (G.gluePatch N hkill i).U.toScheme ⟶ G.gluedQuotient N hkill ↦ f.base u)
      (G.ι_gluedQuotientπ N hkill i)
    simp only [gluedQuotientLeg, Scheme.Hom.comp_apply] at hleg
    exact hleg.symm.trans (congrArg (G.gluedQuotientπ N hkill).base hu)

/-- Each actual local quotient projection is the target-chart pullback of the global projection. -/
theorem isPullback_localQuotientOpenπ_gluedQuotientπ (i : ↥E.E) :
    IsPullback (G.localQuotientOpenπ (G.gluePatch N hkill i).hstable)
      (G.gluePatch N hkill i).U.ι (G.gluedQuotientι N hkill i)
      (G.gluedQuotientπ N hkill) := by
  apply IsOpenImmersion.isPullback
  · exact G.ι_gluedQuotientπ N hkill i
  · simpa only [Scheme.Opens.opensRange_ι] using
      G.gluedQuotientπ_preimage_gluedQuotientι N hkill i

#print axioms gluedQuotientι_open
#print axioms gluedQuotientπ_preimage_gluedQuotientι
#print axioms isPullback_localQuotientOpenπ_gluedQuotientπ
#print axioms AffineChartPatch.preimage_imageOpens
#print axioms glueCover
#print axioms free_gluePatch

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

#print axioms AlgebraicGeometry.Scheme.GlueData.ι_eq_iff
#print axioms AlgebraicGeometry.Scheme.GlueData.ι_isOpenImmersion

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

example (p : fullComplexSchemePoint 3 (by norm_num)) :
    let G := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    ∀ i : ↥(fullComplexPointEllObj 3 (by norm_num) p).curve.E,
      IsPullback (G.localQuotientOpenπ (G.gluePatch G.killN G.killN_spec i).hstable)
        (G.gluePatch G.killN G.killN_spec i).U.ι
        (G.gluedQuotientι G.killN G.killN_spec i) (G.gluedQuotientπ G.killN G.killN_spec) := by
  let G := fullComplexPointAxisSubgroup 3 (by norm_num) p
  have : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
  exact fun i ↦ G.isPullback_localQuotientOpenπ_gluedQuotientπ G.killN G.killN_spec i

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis
