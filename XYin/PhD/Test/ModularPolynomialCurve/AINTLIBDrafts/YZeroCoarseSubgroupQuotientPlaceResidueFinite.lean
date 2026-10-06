/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientParameterFunctionField
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientTranscendental
public import AINTLIBDrafts.IntrinsicPlaceResidueFinite

/-!
# Finite residue fields of places of the actual subgroup quotient

Over a characteristic-zero field, every intrinsic place of the actual finite
subgroup quotient function field has finite residue extension over the original
geometric constants. Its residue degree is therefore positive. The raw and
public interfaces use the actual integrality proofs and independently geometric
structure-map constants.

The proof chooses an already proved quotient transcendental element and installs
its literal polynomial and rational-function scalars. The proved function-field
and characteristic-zero separability pack then supplies the generic intrinsic
place residue-finiteness theorem. The conclusion uses only the original constants
and has no parameter choice in its statement.

The public statements use exactly the native chosen killing integer and witness.
The two examples check raw residue finiteness and public positive degree. No
etale, Noetherian, genus, model, separating-chart, closed-point, or proper-point
representation premise is added.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open scoped Polynomial RatFunc

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] [CharZero k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

theorem gluedQuotient_place_finite_residueField :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k (G.gluedQuotient N hkill).functionField,
      Module.Finite k v.residueField := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  change ∀ v : FunctionField.Place k (G.gluedQuotient N hkill).functionField,
    Module.Finite k v.residueField
  obtain ⟨t, ht⟩ := G.gluedQuotient_exists_transcendental N hkill
  let _ : Algebra k[X] (G.gluedQuotient N hkill).functionField :=
    (Polynomial.aeval t : k[X] →ₐ[k] _).toRingHom.toAlgebra
  let _ := (RatFunc.algHomOfTranscendental t ht).toRingHom.toAlgebra
  have hpack := G.gluedQuotient_parameter_functionField N hkill t ht
  have : IsScalarTower k k[X] (G.gluedQuotient N hkill).functionField := hpack.1
  have : IsScalarTower k[X] k⟮X⟯ (G.gluedQuotient N hkill).functionField := hpack.2.2.1
  have : FunctionField k (G.gluedQuotient N hkill).functionField := hpack.2.2.2
  have : Algebra.IsSeparable k⟮X⟯ (G.gluedQuotient N hkill).functionField :=
    G.gluedQuotient_parameter_isSeparable N hkill t ht
  intro v
  exact FunctionField.Place.finite_residueField k (G.gluedQuotient N hkill).functionField v

theorem quotient_place_finite_residueField [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ := G.quotientS.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k G.quotient.functionField, Module.Finite k v.residueField :=
  G.gluedQuotient_place_finite_residueField G.killN G.killN_spec

theorem gluedQuotient_place_degree_pos :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k (G.gluedQuotient N hkill).functionField, 0 < v.degree := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  change ∀ v : FunctionField.Place k (G.gluedQuotient N hkill).functionField, 0 < v.degree
  intro v
  have : Module.Finite k v.residueField := G.gluedQuotient_place_finite_residueField N hkill v
  exact Module.finrank_pos

theorem quotient_place_degree_pos [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ := G.quotientS.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k G.quotient.functionField, 0 < v.degree :=
  G.gluedQuotient_place_degree_pos G.killN G.killN_spec

example :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k (G.gluedQuotient N hkill).functionField,
      Module.Finite k v.residueField :=
  G.gluedQuotient_place_finite_residueField N hkill

example [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ := G.quotientS.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k G.quotient.functionField, 0 < v.degree :=
  G.quotient_place_degree_pos

#print axioms gluedQuotient_place_finite_residueField
#print axioms quotient_place_finite_residueField
#print axioms gluedQuotient_place_degree_pos
#print axioms quotient_place_degree_pos
#print axioms gluedQuotient_exists_transcendental
#print axioms gluedQuotient_parameter_functionField
#print axioms gluedQuotient_parameter_isSeparable
#print axioms FunctionField.Place.finite_residueField
#print axioms Module.finrank_pos
#print axioms Scheme.Hom.functionFieldBaseAlgebra

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
