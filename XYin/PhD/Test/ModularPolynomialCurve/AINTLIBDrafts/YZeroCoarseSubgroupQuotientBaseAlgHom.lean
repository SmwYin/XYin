/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.FunctionFieldBaseAlgebra
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientIntegral

/-!
# Actual quotient pullback over independent geometric constants

The raw subgroup quotient's native function-field map is a base-field algebra
homomorphism. Its two scalar maps are defined independently by the actual
quotient and elliptic-curve structure morphisms and generic germs. Naturality
and the native over-base triangle prove scalar compatibility; the underlying
ring homomorphism remains the literal native function-field map.

The public and marked-axis interfaces use their genuine killing witnesses.
Only the actual field-base integrality and quotient surjectivity results are
needed. The three examples check raw and public underlying maps by `rfl` and
both the underlying map and geometric constants at a native level-three point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

/-- The literal raw pullback is linear over independently geometric base constants. -/
noncomputable def gluedQuotientπ_functionFieldBaseAlgHom :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    (G.gluedQuotient N hkill).functionField →ₐ[k] E.E.functionField := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  refine { (G.gluedQuotientπ N hkill).functionFieldMap.hom with commutes' := ?_ }
  intro r
  change (G.gluedQuotientπ N hkill).functionFieldMap.hom
      ((G.gluedQuotientS N hkill).functionFieldConstants r) = E.π.functionFieldConstants r
  have h := congrArg (fun φ : k →+* E.E.functionField ↦ φ r)
    (functionFieldMap_comp_functionFieldConstants
      (G.gluedQuotientπ N hkill) (G.gluedQuotientS N hkill))
  rw [G.gluedQuotientπ_gluedQuotientS N hkill] at h
  exact h

/-- The public interface uses exactly the chosen killing integer and its native maps. -/
noncomputable def quotientπ_functionFieldBaseAlgHom [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    G.quotient.functionField →ₐ[k] E.E.functionField :=
  G.gluedQuotientπ_functionFieldBaseAlgHom G.killN G.killN_spec

example :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    (G.gluedQuotientπ_functionFieldBaseAlgHom N hkill).toRingHom =
      (G.gluedQuotientπ N hkill).functionFieldMap.hom := rfl

example [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    G.quotientπ_functionFieldBaseAlgHom.toRingHom = G.quotientπ.functionFieldMap.hom := rfl

#print axioms gluedQuotientπ_functionFieldBaseAlgHom
#print axioms quotientπ_functionFieldBaseAlgHom
#print axioms gluedQuotientπ_gluedQuotientS
#print axioms quotientπ_over
#print axioms functionFieldMap_comp_functionFieldConstants
#print axioms Scheme.Hom.functionFieldBaseAlgebra
#print axioms Scheme.Hom.functionFieldConstants
#print axioms gluedQuotient_isIntegral
#print axioms gluedQuotientπ_surjective
#print axioms Scheme.Hom.functionFieldMap

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

namespace ModularPolynomialCurveTest.AINTLIB.ConstantAxis

/-- The literal marked-axis quotient pullback uses its genuine killing witness. -/
noncomputable def sectionAxis_quotientπ_functionFieldBaseAlgHom (k : Type u) [Field k]
    (N : ℕ) [NeZero N] (E : EllipticCurve (Spec (.of k)))
    (hinv : NIsInvertible (Spec (.of k)) N) (L : E.FullLevelPt N) :
    let G := sectionAxisSubgroup (.of k) N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt (.of k) N E hinv L
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    G.quotient.functionField →ₐ[k] E.E.functionField := by
  let G := sectionAxisSubgroup (.of k) N E hinv L
  have : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt (.of k) N E hinv L
  exact G.quotientπ_functionFieldBaseAlgHom

example (p : fullComplexSchemePoint 3 (by norm_num)) (r : ℂ) :
    let E : EllipticCurve (Spec (.of ℂ)) := (fullComplexPointEllObj 3 (by norm_num) p).curve
    let G : E.FiniteLocallyFreeSubgroup := fullComplexPointAxisSubgroup 3 (by norm_num) p
    let _ : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    G.quotientπ_functionFieldBaseAlgHom.toRingHom = G.quotientπ.functionFieldMap.hom ∧
    G.quotientπ.functionFieldMap.hom (G.quotientS.functionFieldConstants r) =
      E.π.functionFieldConstants r := by
  let E : EllipticCurve (Spec (.of ℂ)) := (fullComplexPointEllObj 3 (by norm_num) p).curve
  let G : E.FiniteLocallyFreeSubgroup := fullComplexPointAxisSubgroup 3 (by norm_num) p
  have : G.HasKillingInt := fullComplexPointAxisSubgroup_hasKillingInt 3 (by norm_num) p
  have : IsIntegral G.quotient := G.quotient_isIntegral
  have : Surjective G.quotientπ := G.quotientπ_surjective
  let _ := G.quotientS.functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  exact ⟨rfl, G.quotientπ_functionFieldBaseAlgHom.commutes r⟩

#print axioms sectionAxis_quotientπ_functionFieldBaseAlgHom
#print axioms sectionAxisSubgroup_hasKillingInt

end ModularPolynomialCurveTest.AINTLIB.ConstantAxis
