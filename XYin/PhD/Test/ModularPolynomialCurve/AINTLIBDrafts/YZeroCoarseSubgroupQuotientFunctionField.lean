/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.FiniteFunctionField
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientIntegral
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientFinite

/-!
# Finite function-field pullback of the actual subgroup quotient

Over any field, the literal quotient projection is finite and surjective,
and its raw quotient is integral. These verified properties give a finite
injective map of the native function fields. The public wrapper uses its
actual chosen killing integer. The marked-axis wrapper applies over any
field with invertible level, including the native complex level-three point.

No Noetherianity, characteristic restriction, etaleness, or quotient elliptic
model is assumed. This is an extension of function fields; it does not prove
unramifiedness at places, genus one, a target j-invariant, or the modular
polynomial relation. The raw quotient is kept as the original native scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

/-- The actual raw quotient projection induces a finite injective native function-field map. -/
theorem gluedQuotientπ_functionFieldMap_finite_injective :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    (G.gluedQuotientπ N hkill).functionFieldMap.hom.Finite ∧
      Function.Injective (G.gluedQuotientπ N hkill).functionFieldMap.hom := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  have : IsFinite (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_isFinite N hkill
  exact ⟨functionFieldMap_finite _, functionFieldMap_injective _⟩

/-- The public quotient uses the same chosen-killing native field pullback. -/
theorem quotientπ_functionFieldMap_finite_injective [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    G.quotientπ.functionFieldMap.hom.Finite ∧
      Function.Injective G.quotientπ.functionFieldMap.hom :=
  G.gluedQuotientπ_functionFieldMap_finite_injective G.killN G.killN_spec

example [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    G.quotientπ.functionFieldMap.hom.Finite :=
  G.quotientπ_functionFieldMap_finite_injective.1

#print axioms gluedQuotientπ_functionFieldMap_finite_injective
#print axioms quotientπ_functionFieldMap_finite_injective
#print axioms AlgebraicGeometry.functionFieldMap_finite
#print axioms AlgebraicGeometry.functionFieldMap_injective
#print axioms quotient_isIntegral
#print axioms quotientπ_isFinite
#print axioms quotientπ_surjective

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

/-- The literal marked-axis quotient has a finite injective native function-field pullback. -/
theorem sectionAxis_quotientπ_functionFieldMap_finite_injective (k : Type u) [Field k]
    (N : ℕ) [NeZero N] (E : EllipticCurve (Spec (.of k)))
    (hinv : NIsInvertible (Spec (.of k)) N) (L : E.FullLevelPt N) :
    let G := sectionAxisSubgroup (.of k) N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt (.of k) N E hinv L
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    G.quotientπ.functionFieldMap.hom.Finite ∧
      Function.Injective G.quotientπ.functionFieldMap.hom := by
  let G := sectionAxisSubgroup (.of k) N E hinv L
  have : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt (.of k) N E hinv L
  exact G.quotientπ_functionFieldMap_finite_injective

example (p : fullComplexSchemePoint 3 (by norm_num)) :
    let E : EllipticCurve (Spec (.of ℂ)) := (fullComplexPointEllObj 3 (by norm_num) p).curve
    let G : E.FiniteLocallyFreeSubgroup := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    G.quotientπ.functionFieldMap.hom.Finite ∧
      Function.Injective G.quotientπ.functionFieldMap.hom :=
  sectionAxis_quotientπ_functionFieldMap_finite_injective ℂ 3
    (fullComplexPointEllObj 3 (by norm_num) p).curve (complexLevelNIsInvertible 3)
    (fullComplexPointLevel 3 (by norm_num) p)

#print axioms sectionAxis_quotientπ_functionFieldMap_finite_injective

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis
