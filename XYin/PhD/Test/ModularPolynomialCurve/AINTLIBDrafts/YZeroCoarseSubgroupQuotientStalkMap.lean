/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.StalkMapMaximalIdeal
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientEtale

/-!
# Maximal ideals under actual subgroup quotient stalk maps

For the actual glued quotient by a finite locally free subgroup with étale
structure map, the literal stalk map sends the maximal ideal at every image
point to the maximal ideal at the original point. The raw killing equation and
the public chosen killing datum are the existing native quotient inputs.

The marked-axis specialization supplies its genuine étale and killing inputs.
The base scheme is arbitrary; no Noetherian, domain, DVR, integrality, genus,
or ramification-index premise is added. The examples test the public API and
a native complex full-level point at level three.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : E.FiniteLocallyFreeSubgroup)
  [Etale G.π]

/-- The actual glued quotient satisfies the local maximal-ideal formula at every point. -/
theorem gluedQuotientπ_map_maximalIdeal_stalkMap (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) (x : E.E) :
    (IsLocalRing.maximalIdeal
      ((G.gluedQuotient N hkill).presheaf.stalk ((G.gluedQuotientπ N hkill).base x))).map
        ((G.gluedQuotientπ N hkill).stalkMap x).hom =
      IsLocalRing.maximalIdeal (E.E.presheaf.stalk x) := by
  have : Etale (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_etale N hkill
  exact FormallyUnramified.map_maximalIdeal_stalkMap _ x

/-- The public projection uses the actual chosen killing integer and literal stalk map. -/
theorem quotientπ_map_maximalIdeal_stalkMap [G.HasKillingInt] (x : E.E) :
    (IsLocalRing.maximalIdeal (G.quotient.presheaf.stalk (G.quotientπ.base x))).map
        (G.quotientπ.stalkMap x).hom = IsLocalRing.maximalIdeal (E.E.presheaf.stalk x) :=
  G.gluedQuotientπ_map_maximalIdeal_stalkMap G.killN G.killN_spec x

example [G.HasKillingInt] (x : E.E) :
    (IsLocalRing.maximalIdeal (G.quotient.presheaf.stalk (G.quotientπ.base x))).map
        (G.quotientπ.stalkMap x).hom = IsLocalRing.maximalIdeal (E.E.presheaf.stalk x) :=
  G.quotientπ_map_maximalIdeal_stalkMap x

#print axioms gluedQuotientπ_map_maximalIdeal_stalkMap
#print axioms quotientπ_map_maximalIdeal_stalkMap
#print axioms FormallyUnramified.map_maximalIdeal_stalkMap
#print axioms gluedQuotientπ_etale
#print axioms quotientπ_etale
#print axioms gluedQuotientπ
#print axioms quotientπ
#print axioms killN_spec

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

/-- The literal marked-axis subgroup supplies the subgroup étale and killing inputs. -/
theorem sectionAxis_quotientπ_map_maximalIdeal_stalkMap (R : CommRingCat.{u})
    (N : ℕ) [NeZero N] (E : EllipticCurve (Spec R))
    (hinv : NIsInvertible (Spec R) N) (L : E.FullLevelPt N) (x : E.E) :
    let G := sectionAxisSubgroup R N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
    (IsLocalRing.maximalIdeal (G.quotient.presheaf.stalk (G.quotientπ.base x))).map
        (G.quotientπ.stalkMap x).hom = IsLocalRing.maximalIdeal (E.E.presheaf.stalk x) := by
  let G := sectionAxisSubgroup R N E hinv L
  have : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
  have : Etale G.π := sectionAxisSubgroup_etale R N E hinv L
  exact G.quotientπ_map_maximalIdeal_stalkMap x

example (p : fullComplexSchemePoint 3 (by norm_num))
    (x : (fullComplexPointEllObj 3 (by norm_num) p).curve.E) :
    let E : EllipticCurve (Spec (.of ℂ)) := (fullComplexPointEllObj 3 (by norm_num) p).curve
    let G : E.FiniteLocallyFreeSubgroup := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    (IsLocalRing.maximalIdeal (G.quotient.presheaf.stalk (G.quotientπ.base x))).map
        (G.quotientπ.stalkMap x).hom = IsLocalRing.maximalIdeal (E.E.presheaf.stalk x) :=
  sectionAxis_quotientπ_map_maximalIdeal_stalkMap (.of ℂ) 3
    (fullComplexPointEllObj 3 (by norm_num) p).curve (complexLevelNIsInvertible 3)
    (fullComplexPointLevel 3 (by norm_num) p) x

#print axioms sectionAxis_quotientπ_map_maximalIdeal_stalkMap
#print axioms sectionAxisSubgroup_etale
#print axioms sectionAxisSubgroup_hasKillingInt
#print axioms sectionAxis_quotientπ_etale

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis
