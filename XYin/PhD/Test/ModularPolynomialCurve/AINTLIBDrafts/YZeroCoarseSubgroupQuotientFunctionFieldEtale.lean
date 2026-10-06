/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.FunctionFieldEtale
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientIntegral
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientFinite
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientEtale

/-!
# Etale native function-field maps of the actual subgroup quotient

Over an arbitrary field, the actual quotient projection of a finite locally
free subgroup with an etale structure map induces an etale ring homomorphism
on the native function fields. The integral target, surjective and finite
projection, and etale projection are supplied by the existing actual APIs.
The public quotient uses its construction's chosen killing integer.

For the literal constant-axis subgroup of a full marking with invertible
level, its proved etale structure map supplies the generic hypothesis.
No Noetherian or characteristic-zero assumption is added. This concerns
the generic field map and supplies no quotient elliptic-curve model, genus,
target j-invariant, or valuation/place ramification statement.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) [Etale G.π]

/-- The actual raw quotient projection has an etale native function-field pullback. -/
theorem gluedQuotientπ_functionFieldMap_etale :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    (G.gluedQuotientπ N hkill).functionFieldMap.hom.Etale := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  have : IsFinite (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_isFinite N hkill
  have : Etale (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_etale N hkill
  exact functionFieldMap_etale _

/-- The public chosen-killing quotient uses the same native etale field map. -/
theorem quotientπ_functionFieldMap_etale [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    G.quotientπ.functionFieldMap.hom.Etale :=
  G.gluedQuotientπ_functionFieldMap_etale G.killN G.killN_spec

example [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    G.quotientπ.functionFieldMap.hom.Etale :=
  G.quotientπ_functionFieldMap_etale

#print axioms gluedQuotientπ_functionFieldMap_etale
#print axioms quotientπ_functionFieldMap_etale
#print axioms AlgebraicGeometry.functionFieldMap_etale
#print axioms gluedQuotient_isIntegral
#print axioms gluedQuotientπ_isFinite
#print axioms gluedQuotientπ_surjective
#print axioms gluedQuotientπ_etale

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

/-- The literal marked-axis quotient supplies its own subgroup-etale hypothesis. -/
theorem sectionAxis_quotientπ_functionFieldMap_etale (k : Type u) [Field k]
    (N : ℕ) [NeZero N] (E : EllipticCurve (Spec (.of k)))
    (hinv : NIsInvertible (Spec (.of k)) N) (L : E.FullLevelPt N) :
    let G := sectionAxisSubgroup (.of k) N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt (.of k) N E hinv L
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    G.quotientπ.functionFieldMap.hom.Etale := by
  let G := sectionAxisSubgroup (.of k) N E hinv L
  have : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt (.of k) N E hinv L
  have : Etale G.π := sectionAxisSubgroup_etale (.of k) N E hinv L
  exact G.quotientπ_functionFieldMap_etale

example (p : fullComplexSchemePoint 3 (by norm_num)) :
    let E : EllipticCurve (Spec (.of ℂ)) := (fullComplexPointEllObj 3 (by norm_num) p).curve
    let G : E.FiniteLocallyFreeSubgroup := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    G.quotientπ.functionFieldMap.hom.Etale :=
  sectionAxis_quotientπ_functionFieldMap_etale ℂ 3
    (fullComplexPointEllObj 3 (by norm_num) p).curve (complexLevelNIsInvertible 3)
    (fullComplexPointLevel 3 (by norm_num) p)

#print axioms sectionAxis_quotientπ_functionFieldMap_etale
#print axioms sectionAxisSubgroup_etale
#print axioms sectionAxisSubgroup_hasKillingInt

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis
