/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientBaseAlgHom
public import AINTLIBDrafts.NativeFullConstantField
public import AINTLIBDrafts.FullConstantFieldDescent

/-!
# Full constants of the actual subgroup quotient field

The actual quotient's independently geometric base algebra has no new
algebraic constants. Its genuine base-field field embedding into the native
elliptic field reflects that field's proved full-constant-field property.
The raw and public interfaces use their actual killing witnesses; the two
examples identify algebraic elements with literal geometric quotient constants.

This holds over any field without additional finite, étale, Noetherian,
normality, DVR, genus or quotient-model hypotheses.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

theorem gluedQuotient_isFullConstantField :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    FunctionField.IsFullConstantField k (G.gluedQuotient N hkill).functionField := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  let _ := YZeroCoarseJ.nativeField_isFullConstantField E
  exact FunctionField.IsFullConstantField.of_algHom
    (G.gluedQuotientπ_functionFieldBaseAlgHom N hkill)

theorem quotient_isFullConstantField [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ := G.quotientS.functionFieldBaseAlgebra
    FunctionField.IsFullConstantField k G.quotient.functionField :=
  G.gluedQuotient_isFullConstantField G.killN G.killN_spec

example :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    ∀ z : (G.gluedQuotient N hkill).functionField, IsAlgebraic k z →
      ∃ c : k, z = (G.gluedQuotientS N hkill).functionFieldConstants c := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := G.gluedQuotient_isFullConstantField N hkill
  exact fun z hz ↦ FunctionField.IsFullConstantField.algebraic_mem z hz

example [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ := G.quotientS.functionFieldBaseAlgebra
    ∀ z : G.quotient.functionField, IsAlgebraic k z →
      ∃ c : k, z = G.quotientS.functionFieldConstants c := by
  have : IsIntegral G.quotient := G.quotient_isIntegral
  let _ := G.quotientS.functionFieldBaseAlgebra
  let _ := G.quotient_isFullConstantField
  exact fun z hz ↦ FunctionField.IsFullConstantField.algebraic_mem z hz

#print axioms gluedQuotient_isFullConstantField
#print axioms quotient_isFullConstantField
#print axioms FunctionField.IsFullConstantField.of_algHom
#print axioms YZeroCoarseJ.nativeField_isFullConstantField
#print axioms gluedQuotientπ_functionFieldBaseAlgHom
#print axioms quotientπ_functionFieldBaseAlgHom
#print axioms gluedQuotient_isIntegral
#print axioms gluedQuotientπ_surjective
#print axioms Scheme.Hom.functionFieldBaseAlgebra
#print axioms FunctionField.IsFullConstantField.algebraic_mem

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
