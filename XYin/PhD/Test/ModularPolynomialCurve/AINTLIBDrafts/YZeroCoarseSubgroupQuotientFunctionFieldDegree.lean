/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.FiniteFlatFunctionFieldDegree
public import AINTLIBDrafts.YZeroCoarseGluedQuotientRank
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientFunctionField

/-!
# Actual subgroup quotient function-field degree

For an actual elliptic curve over any field, the literal finite flat
quotient projection gives a function-field extension whose degree equals
the supplied subgroup rank. Integral descent and surjectivity supply the
native function fields and dominance; the generic finite-flat degree theorem
and genuine global quotient rank identify the actual scalar extension.

The public quotient uses its chosen killing integer. The actual marked-axis
wrapper has degree N, checked on the native complex level-three point.
No Noetherian, etaleness, quotient model or genus input is assumed.

This is the degree of the elliptic-curve quotient E to E/G. The function
field of YZeroCoarse and the modular-polynomial comparison remain separate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

/-- The actual native function-field extension degree is the genuine subgroup rank. -/
theorem gluedQuotientπ_functionField_finrank (r : ℕ) (hG : G.HasRank r) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := functionFieldAlgebra (G.gluedQuotientπ N hkill)
    Module.finrank (G.gluedQuotient N hkill).functionField E.E.functionField = r := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  have : IsFinite (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_isFinite N hkill
  have : Flat (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_flat N hkill
  let _ := functionFieldAlgebra (G.gluedQuotientπ N hkill)
  exact (Scheme.Hom.finrank_eq_functionField_finrank (G.gluedQuotientπ N hkill)
    (genericPoint (G.gluedQuotient N hkill))).symm.trans
      (G.gluedQuotientπ_finrank N hkill r hG _)

/-- The public quotient uses the actual chosen killing integer in the same degree formula. -/
theorem quotientπ_functionField_finrank [G.HasKillingInt] (r : ℕ) (hG : G.HasRank r) :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := functionFieldAlgebra G.quotientπ
    Module.finrank G.quotient.functionField E.E.functionField = r :=
  G.gluedQuotientπ_functionField_finrank G.killN G.killN_spec r hG

example [G.HasKillingInt] (r : ℕ) (hG : G.HasRank r) :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := functionFieldAlgebra G.quotientπ
    Module.finrank G.quotient.functionField E.E.functionField = r :=
  G.quotientπ_functionField_finrank r hG

#print axioms gluedQuotientπ_functionField_finrank
#print axioms quotientπ_functionField_finrank
#print axioms gluedQuotientπ_finrank
#print axioms Scheme.Hom.finrank_eq_functionField_finrank
#print axioms gluedQuotient_isIntegral
#print axioms gluedQuotientπ_flat
#print axioms gluedQuotientπ_isFinite
#print axioms gluedQuotientπ_surjective
#print axioms functionFieldAlgebra

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

/-- The actual marked-axis quotient gives a degree-N native function-field extension. -/
theorem sectionAxis_quotientπ_functionField_finrank (k : Type u) [Field k]
    (N : ℕ) [NeZero N] (E : EllipticCurve (Spec (.of k)))
    (hinv : NIsInvertible (Spec (.of k)) N) (L : E.FullLevelPt N) :
    let G := sectionAxisSubgroup (.of k) N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt (.of k) N E hinv L
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := functionFieldAlgebra G.quotientπ
    Module.finrank G.quotient.functionField E.E.functionField = N := by
  let G := sectionAxisSubgroup (.of k) N E hinv L
  have : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt (.of k) N E hinv L
  exact G.quotientπ_functionField_finrank N (sectionAxisSubgroup_hasRank (.of k) N E hinv L)

example (p : fullComplexSchemePoint 3 (by norm_num)) :
    let E : EllipticCurve (Spec (.of ℂ)) := (fullComplexPointEllObj 3 (by norm_num) p).curve
    let G : E.FiniteLocallyFreeSubgroup := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := functionFieldAlgebra G.quotientπ
    Module.finrank G.quotient.functionField E.E.functionField = 3 :=
  sectionAxis_quotientπ_functionField_finrank ℂ 3
    (fullComplexPointEllObj 3 (by norm_num) p).curve (complexLevelNIsInvertible 3)
    (fullComplexPointLevel 3 (by norm_num) p)

#print axioms sectionAxis_quotientπ_functionField_finrank
#print axioms sectionAxisSubgroup_hasRank

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis
