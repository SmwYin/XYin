/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientParameterFinite
public import AINTLIBDrafts.RatFuncParameterScalars
public import Mathlib.FieldTheory.Perfect

/-!
# Function-field scalars for an actual quotient parameter

Each transcendental element of the actual subgroup quotient field supplies
explicit polynomial scalars by aeval and rational-function scalars by its
parameter embedding. The raw and public interfaces give three actual scalar
towers and a finite function-field structure over that parameter. The original
base-field constants remain those of the quotient structure map and generic germ.

The finite-parameter result and generic polynomial tower provide these facts
for every field. Separate raw and public characteristic-zero corollaries give
separability over the new rational-function scalars. This makes no assertion
that an arbitrary parameter is separating over a perfect field of positive
characteristic.

The public statements use the native chosen killing integer and its witness.
The two examples check the raw scalar/function-field bundle and public
characteristic-zero separability. No Noetherian, etale, genus, quotient-model,
or old-coordinate-factorization premise is used. Residue fields and places
require separate results.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open scoped Polynomial RatFunc

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

theorem gluedQuotient_parameter_functionField :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    ∀ (t : (G.gluedQuotient N hkill).functionField) (ht : Transcendental k t),
      let _ : Algebra k[X] (G.gluedQuotient N hkill).functionField :=
        (Polynomial.aeval t : k[X] →ₐ[k] _).toRingHom.toAlgebra
      let _ := (RatFunc.algHomOfTranscendental t ht).toRingHom.toAlgebra
      IsScalarTower k k[X] (G.gluedQuotient N hkill).functionField ∧
      IsScalarTower k k⟮X⟯ (G.gluedQuotient N hkill).functionField ∧
      IsScalarTower k[X] k⟮X⟯ (G.gluedQuotient N hkill).functionField ∧
      FunctionField k (G.gluedQuotient N hkill).functionField := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  change ∀ (t : (G.gluedQuotient N hkill).functionField) (ht : Transcendental k t),
    let _ : Algebra k[X] (G.gluedQuotient N hkill).functionField :=
      (Polynomial.aeval t : k[X] →ₐ[k] _).toRingHom.toAlgebra
    let _ := (RatFunc.algHomOfTranscendental t ht).toRingHom.toAlgebra
    IsScalarTower k k[X] (G.gluedQuotient N hkill).functionField ∧
    IsScalarTower k k⟮X⟯ (G.gluedQuotient N hkill).functionField ∧
    IsScalarTower k[X] k⟮X⟯ (G.gluedQuotient N hkill).functionField ∧
    FunctionField k (G.gluedQuotient N hkill).functionField
  intro t ht
  let _ : Algebra k[X] (G.gluedQuotient N hkill).functionField :=
    (Polynomial.aeval t : k[X] →ₐ[k] _).toRingHom.toAlgebra
  let _ := (RatFunc.algHomOfTranscendental t ht).toRingHom.toAlgebra
  have hfinite : FunctionField k (G.gluedQuotient N hkill).functionField :=
    G.gluedQuotient_parameter_finite N hkill t ht
  exact ⟨IsScalarTower.of_algHom (Polynomial.aeval t),
    IsScalarTower.of_algHom (RatFunc.algHomOfTranscendental t ht),
    RatFunc.algHomOfTranscendental_polynomialTower t ht, hfinite⟩

theorem quotient_parameter_functionField [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ := G.quotientS.functionFieldBaseAlgebra
    ∀ (t : G.quotient.functionField) (ht : Transcendental k t),
      let _ : Algebra k[X] G.quotient.functionField :=
        (Polynomial.aeval t : k[X] →ₐ[k] _).toRingHom.toAlgebra
      let _ := (RatFunc.algHomOfTranscendental t ht).toRingHom.toAlgebra
      IsScalarTower k k[X] G.quotient.functionField ∧
      IsScalarTower k k⟮X⟯ G.quotient.functionField ∧
      IsScalarTower k[X] k⟮X⟯ G.quotient.functionField ∧
      FunctionField k G.quotient.functionField :=
  G.gluedQuotient_parameter_functionField G.killN G.killN_spec

theorem gluedQuotient_parameter_isSeparable [CharZero k] :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    ∀ (t : (G.gluedQuotient N hkill).functionField) (ht : Transcendental k t),
      let _ := (RatFunc.algHomOfTranscendental t ht).toRingHom.toAlgebra
      Algebra.IsSeparable k⟮X⟯ (G.gluedQuotient N hkill).functionField := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  change ∀ (t : (G.gluedQuotient N hkill).functionField) (ht : Transcendental k t),
    let _ := (RatFunc.algHomOfTranscendental t ht).toRingHom.toAlgebra
    Algebra.IsSeparable k⟮X⟯ (G.gluedQuotient N hkill).functionField
  intro t ht
  let _ := (RatFunc.algHomOfTranscendental t ht).toRingHom.toAlgebra
  have : FunctionField k (G.gluedQuotient N hkill).functionField :=
    (G.gluedQuotient_parameter_functionField N hkill t ht).2.2.2
  have : Algebra.IsAlgebraic k⟮X⟯ (G.gluedQuotient N hkill).functionField :=
    Algebra.IsAlgebraic.of_finite _ _
  infer_instance

theorem quotient_parameter_isSeparable [G.HasKillingInt] [CharZero k] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ := G.quotientS.functionFieldBaseAlgebra
    ∀ (t : G.quotient.functionField) (ht : Transcendental k t),
      let _ := (RatFunc.algHomOfTranscendental t ht).toRingHom.toAlgebra
      Algebra.IsSeparable k⟮X⟯ G.quotient.functionField :=
  G.gluedQuotient_parameter_isSeparable G.killN G.killN_spec

example :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    ∀ (t : (G.gluedQuotient N hkill).functionField) (ht : Transcendental k t),
      let _ : Algebra k[X] (G.gluedQuotient N hkill).functionField :=
        (Polynomial.aeval t : k[X] →ₐ[k] _).toRingHom.toAlgebra
      let _ := (RatFunc.algHomOfTranscendental t ht).toRingHom.toAlgebra
      IsScalarTower k k[X] (G.gluedQuotient N hkill).functionField ∧
      IsScalarTower k k⟮X⟯ (G.gluedQuotient N hkill).functionField ∧
      IsScalarTower k[X] k⟮X⟯ (G.gluedQuotient N hkill).functionField ∧
      FunctionField k (G.gluedQuotient N hkill).functionField :=
  G.gluedQuotient_parameter_functionField N hkill

example [G.HasKillingInt] [CharZero k] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ := G.quotientS.functionFieldBaseAlgebra
    ∀ (t : G.quotient.functionField) (ht : Transcendental k t),
      let _ := (RatFunc.algHomOfTranscendental t ht).toRingHom.toAlgebra
      Algebra.IsSeparable k⟮X⟯ G.quotient.functionField :=
  G.quotient_parameter_isSeparable

#print axioms gluedQuotient_parameter_functionField
#print axioms quotient_parameter_functionField
#print axioms gluedQuotient_parameter_isSeparable
#print axioms quotient_parameter_isSeparable
#print axioms gluedQuotient_parameter_finite
#print axioms RatFunc.algHomOfTranscendental_polynomialTower
#print axioms IsScalarTower.of_algHom
#print axioms Algebra.IsAlgebraic.of_finite
#print axioms Algebra.IsAlgebraic.isSeparable_of_perfectField
#print axioms PerfectField.ofCharZero
#print axioms Scheme.Hom.functionFieldBaseAlgebra

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
