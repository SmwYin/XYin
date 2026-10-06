/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseLocalQuotientRank
public import AINTLIBDrafts.YZeroCoarseLocalQuotientGeometry

/-!
# Actual raw local quotient fibre rank

The local quotient used by the gluing construction is the spectrum of a raw
invariant subring. Its existing isomorphism with the canonical coinvariant
quotient respects the actual projection. The resulting pullback square transports
the retained canonical fibre rank to this literal raw local quotient projection.

The subgroup rank is supplied by the genuine `HasRank r` predicate, and only the
actual patch's group-ring freeness is required by the Hopf comparison. The two
examples check an arbitrary ranked subgroup and the literal marked-axis subgroup
of rank `N`. No global quotient rank or function-field degree is asserted here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch

open ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : E.FiniteLocallyFreeSubgroup}
  (P : G.AffineChartPatch) [Module.Free P.baseRing P.groupRing]

/-- The actual raw local quotient projection inherits the genuine subgroup rank. -/
theorem localQuotientOpenπ_finrank (r : ℕ) (hG : G.HasRank r)
    (y : G.localQuotientOpen P.hstable) :
    (G.localQuotientOpenπ P.hstable).finrank y = r := by
  have : IsFinite (G.localQuotientOpenπ P.hstable) := localQuotientOpenπ_isFinite P
  have : Flat (G.localQuotientOpenπ P.hstable) :=
    P.flat_and_surjective_localQuotientOpenπ.1
  have : Flat P.localQuotientπ := by
    rw [← P.localQuotientOpenπ_iso]
    infer_instance
  have : IsFinite P.localQuotientπ := by
    rw [← P.localQuotientOpenπ_iso]
    infer_instance
  have hpb : IsPullback (𝟙 P.U.toScheme) (G.localQuotientOpenπ P.hstable)
      P.localQuotientπ P.localQuotientOpenIso.hom := by
    apply IsPullback.of_horiz_isIso
    exact ⟨by simpa only [Category.id_comp] using P.localQuotientOpenπ_iso.symm⟩
  exact (Scheme.Hom.finrank_of_isPullback (𝟙 P.U.toScheme)
    (G.localQuotientOpenπ P.hstable) P.localQuotientπ P.localQuotientOpenIso.hom hpb y).trans
      (P.localQuotientπ_finrank r hG _)

example (r : ℕ) (hG : G.HasRank r) :
    ∀ y : G.localQuotientOpen P.hstable, (G.localQuotientOpenπ P.hstable).finrank y = r :=
  localQuotientOpenπ_finrank P r hG

open ModularPolynomialCurveTest.AINTLIB.ConstantAxis

example (R : CommRingCat.{u}) (N : ℕ) [NeZero N] (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N)
    (P : (sectionAxisSubgroup R N E hinv L).AffineChartPatch)
    [Module.Free P.baseRing P.groupRing]
    (y : (sectionAxisSubgroup R N E hinv L).localQuotientOpen P.hstable) :
    ((sectionAxisSubgroup R N E hinv L).localQuotientOpenπ P.hstable).finrank y = N :=
  localQuotientOpenπ_finrank P N (sectionAxisSubgroup_hasRank R N E hinv L) y

#print axioms localQuotientOpenπ_finrank
#print axioms localQuotientπ_finrank
#print axioms localQuotientOpenIso
#print axioms localQuotientOpenπ_iso
#print axioms coinvSubringEquiv
#print axioms quotientRing_eq_coinvariants
#print axioms flat_and_surjective_localQuotientOpenπ
#print axioms localQuotientOpenπ_isFinite
#print axioms IsPullback.of_horiz_isIso
#print axioms Scheme.Hom.finrank_of_isPullback

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch
