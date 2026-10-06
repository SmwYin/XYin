/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseRawLocalQuotientRank
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientFinite

/-!
# Actual glued quotient fibre rank

The actual glued quotient projection has fibre finrank `r` when the genuine
subgroup satisfies `HasRank r`. Each quotient point lifts through the construction's
target chart cover. The proved target-chart pullback square identifies the global
fibre rank with the retained raw local quotient rank. The construction itself
provides the required freeness on every chosen patch.

The base scheme is arbitrary, and the actual nonzero killing integer and its
equation are explicit. No global freeness, Noetherian, étale, domain, or model
hypothesis is added. The two examples check all quotient points and points in an
actual target chart. Public chosen-kill wrappers and function-field degrees remain
separate steps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : E.FiniteLocallyFreeSubgroup)
  (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

/-- The actual glued quotient projection has fibre finrank given by the genuine subgroup rank. -/
theorem gluedQuotientπ_finrank (r : ℕ) (hG : G.HasRank r) (y : G.gluedQuotient N hkill) :
    (G.gluedQuotientπ N hkill).finrank y = r := by
  have : Flat (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_flat N hkill
  have : IsFinite (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_isFinite N hkill
  obtain ⟨i, z, hz⟩ : ∃ (i : ↥E.E)
      (z : G.localQuotientOpen (G.gluePatch N hkill i).hstable),
      (G.gluedQuotientι N hkill i).base z = y :=
    (G.quotientGlueData N hkill).ι_jointly_surjective y
  have : Module.Free (G.gluePatch N hkill i).baseRing
      (G.gluePatch N hkill i).groupRing := G.free_gluePatch N hkill i
  have hloc := Scheme.Hom.finrank_of_isPullback (G.gluePatch N hkill i).U.ι
    (G.localQuotientOpenπ (G.gluePatch N hkill i).hstable) (G.gluedQuotientπ N hkill)
    (G.gluedQuotientι N hkill i)
    (G.isPullback_localQuotientOpenπ_gluedQuotientπ N hkill i).flip z
  rw [hz] at hloc
  exact hloc.symm.trans ((G.gluePatch N hkill i).localQuotientOpenπ_finrank r hG z)

example (r : ℕ) (hG : G.HasRank r) :
    ∀ y : G.gluedQuotient N hkill, (G.gluedQuotientπ N hkill).finrank y = r :=
  G.gluedQuotientπ_finrank N hkill r hG

example (r : ℕ) (hG : G.HasRank r) (i : ↥E.E)
    (z : G.localQuotientOpen (G.gluePatch N hkill i).hstable) :
    (G.gluedQuotientπ N hkill).finrank ((G.gluedQuotientι N hkill i).base z) = r :=
  G.gluedQuotientπ_finrank N hkill r hG _

#print axioms gluedQuotientπ_finrank
#print axioms AffineChartPatch.localQuotientOpenπ_finrank
#print axioms isPullback_localQuotientOpenπ_gluedQuotientπ
#print axioms gluedQuotientπ_flat
#print axioms gluedQuotientπ_isFinite
#print axioms gluePatch
#print axioms free_gluePatch
#print axioms quotientGlueData
#print axioms Scheme.GlueData.ι_jointly_surjective
#print axioms Scheme.Hom.finrank_of_isPullback

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
