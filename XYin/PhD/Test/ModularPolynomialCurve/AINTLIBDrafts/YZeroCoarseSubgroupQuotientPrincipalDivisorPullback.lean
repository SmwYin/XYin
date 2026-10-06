/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.PrincipalDivisorPullback
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientDivisorPullback
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientParameterFunctionField

/-!
# Principal divisors under the actual etale subgroup quotient

Over a characteristic-zero field, the actual raw and public subgroup quotient
pullbacks send each principal divisor to the principal divisor of the literal
native function-field pullback. The proof uses the actual finite-fiber place
map, its proved normalized valuation restriction, and the generic principal
pullback theorem.

The two geometric constant algebras remain independently specified. The source
uses its proved native polynomial/rational-function scalar pack. Each supplied
transcendental target parameter uses its actual aeval and rational-function
embedding, with finiteness, towers and characteristic-zero separability proved
by the quotient parameter API. No caller chart, separating, scalar-compatibility,
quotient-model or genus assumption is introduced, and no source coordinate is
assumed to factor through the quotient. The principal-divisor definitions still
use the current chart-based API. The public wrapper uses the actual chosen
killing integer and witness; the two examples check both actual interfaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open ModularCurves.YZeroCoarseJ
open scoped Polynomial RatFunc

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] [CharZero k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) [Etale G.π]

theorem gluedQuotientDivisorPullback_principalDivisor (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    let _ := nativeFieldPolynomialAlgebra E
    let _ := nativeFieldRatFuncAlgebra E
    let _ := nativeFieldPolynomial_baseTower E
    let _ := nativeFieldRatFunc_polynomialTower E
    let _ := nativeField_functionField E
    let _ := nativeField_isSeparable E
    ∀ (τ : (G.gluedQuotient N hkill).functionField) (ht : Transcendental k τ),
      let _ : Algebra k[X] (G.gluedQuotient N hkill).functionField :=
        (Polynomial.aeval τ : k[X] →ₐ[k] _).toRingHom.toAlgebra
      let _ := (RatFunc.algHomOfTranscendental τ ht).toRingHom.toAlgebra
      let hQ := G.gluedQuotient_parameter_functionField N hkill τ ht
      let _ := hQ.1
      let _ := hQ.2.2.1
      let _ := hQ.2.2.2
      let _ := G.gluedQuotient_parameter_isSeparable N hkill τ ht
      ∀ u : (G.gluedQuotient N hkill).functionFieldˣ,
        G.gluedQuotientDivisorPullback N hkill
          (FunctionField.principalDivisor k (G.gluedQuotient N hkill).functionField
            (Additive.ofMul u)) =
            FunctionField.principalDivisor k E.E.functionField
              (Additive.ofMul (Units.map (G.gluedQuotientπ N hkill).functionFieldMap.hom u)) := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  let _ := nativeFieldPolynomialAlgebra E
  let _ := nativeFieldRatFuncAlgebra E
  let _ := nativeFieldPolynomial_baseTower E
  let _ := nativeFieldRatFunc_polynomialTower E
  let _ := nativeField_functionField E
  let _ := nativeField_isSeparable E
  dsimp only
  intro τ ht
  let _ : Algebra k[X] (G.gluedQuotient N hkill).functionField :=
    (Polynomial.aeval τ : k[X] →ₐ[k] _).toRingHom.toAlgebra
  let _ := (RatFunc.algHomOfTranscendental τ ht).toRingHom.toAlgebra
  have hQ := G.gluedQuotient_parameter_functionField N hkill τ ht
  let _ := hQ.1
  let _ := hQ.2.2.1
  let _ := hQ.2.2.2
  let _ := G.gluedQuotient_parameter_isSeparable N hkill τ ht
  intro u
  exact FunctionField.principalDivisor_comapDomainOfFiniteFibers k
    E.E.functionField (G.gluedQuotient N hkill).functionField
    (G.gluedQuotientπ_functionFieldBaseAlgHom N hkill)
    (G.gluedQuotientPlaceMap N hkill)
    (G.gluedQuotientPlaceMap_finite_preimage_singleton N hkill)
    (G.gluedQuotientPlaceMap_valuation N hkill) u

theorem quotientDivisorPullback_principalDivisor [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    let _ := nativeFieldPolynomialAlgebra E
    let _ := nativeFieldRatFuncAlgebra E
    let _ := nativeFieldPolynomial_baseTower E
    let _ := nativeFieldRatFunc_polynomialTower E
    let _ := nativeField_functionField E
    let _ := nativeField_isSeparable E
    ∀ (τ : G.quotient.functionField) (ht : Transcendental k τ),
      let _ : Algebra k[X] G.quotient.functionField :=
        (Polynomial.aeval τ : k[X] →ₐ[k] _).toRingHom.toAlgebra
      let _ := (RatFunc.algHomOfTranscendental τ ht).toRingHom.toAlgebra
      let hQ := G.quotient_parameter_functionField τ ht
      let _ := hQ.1
      let _ := hQ.2.2.1
      let _ := hQ.2.2.2
      let _ := G.quotient_parameter_isSeparable τ ht
      ∀ u : G.quotient.functionFieldˣ,
        G.quotientDivisorPullback
          (FunctionField.principalDivisor k G.quotient.functionField (Additive.ofMul u)) =
            FunctionField.principalDivisor k E.E.functionField
              (Additive.ofMul (Units.map G.quotientπ.functionFieldMap.hom u)) :=
  G.gluedQuotientDivisorPullback_principalDivisor G.killN G.killN_spec

example (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    let _ := nativeFieldPolynomialAlgebra E
    let _ := nativeFieldRatFuncAlgebra E
    let _ := nativeFieldPolynomial_baseTower E
    let _ := nativeFieldRatFunc_polynomialTower E
    let _ := nativeField_functionField E
    let _ := nativeField_isSeparable E
    ∀ (τ : (G.gluedQuotient N hkill).functionField) (ht : Transcendental k τ),
      let _ : Algebra k[X] (G.gluedQuotient N hkill).functionField :=
        (Polynomial.aeval τ : k[X] →ₐ[k] _).toRingHom.toAlgebra
      let _ := (RatFunc.algHomOfTranscendental τ ht).toRingHom.toAlgebra
      let hQ := G.gluedQuotient_parameter_functionField N hkill τ ht
      let _ := hQ.1
      let _ := hQ.2.2.1
      let _ := hQ.2.2.2
      let _ := G.gluedQuotient_parameter_isSeparable N hkill τ ht
      ∀ u : (G.gluedQuotient N hkill).functionFieldˣ,
        G.gluedQuotientDivisorPullback N hkill
          (FunctionField.principalDivisor k (G.gluedQuotient N hkill).functionField
            (Additive.ofMul u)) =
            FunctionField.principalDivisor k E.E.functionField
              (Additive.ofMul (Units.map (G.gluedQuotientπ N hkill).functionFieldMap.hom u)) :=
  G.gluedQuotientDivisorPullback_principalDivisor N hkill

example [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    let _ := nativeFieldPolynomialAlgebra E
    let _ := nativeFieldRatFuncAlgebra E
    let _ := nativeFieldPolynomial_baseTower E
    let _ := nativeFieldRatFunc_polynomialTower E
    let _ := nativeField_functionField E
    let _ := nativeField_isSeparable E
    ∀ (τ : G.quotient.functionField) (ht : Transcendental k τ),
      let _ : Algebra k[X] G.quotient.functionField :=
        (Polynomial.aeval τ : k[X] →ₐ[k] _).toRingHom.toAlgebra
      let _ := (RatFunc.algHomOfTranscendental τ ht).toRingHom.toAlgebra
      let hQ := G.quotient_parameter_functionField τ ht
      let _ := hQ.1
      let _ := hQ.2.2.1
      let _ := hQ.2.2.2
      let _ := G.quotient_parameter_isSeparable τ ht
      ∀ u : G.quotient.functionFieldˣ,
        G.quotientDivisorPullback
          (FunctionField.principalDivisor k G.quotient.functionField (Additive.ofMul u)) =
            FunctionField.principalDivisor k E.E.functionField
              (Additive.ofMul (Units.map G.quotientπ.functionFieldMap.hom u)) :=
  G.quotientDivisorPullback_principalDivisor

#print axioms gluedQuotientDivisorPullback_principalDivisor
#print axioms quotientDivisorPullback_principalDivisor
#print axioms FunctionField.principalDivisor_comapDomainOfFiniteFibers
#print axioms gluedQuotientDivisorPullback
#print axioms gluedQuotientPlaceMap_finite_preimage_singleton
#print axioms gluedQuotientPlaceMap_valuation
#print axioms gluedQuotientπ_functionFieldBaseAlgHom
#print axioms gluedQuotient_parameter_functionField
#print axioms gluedQuotient_parameter_isSeparable
#print axioms nativeFieldPolynomialAlgebra
#print axioms nativeFieldRatFuncAlgebra
#print axioms nativeFieldPolynomial_baseTower
#print axioms nativeFieldRatFunc_polynomialTower
#print axioms nativeField_functionField
#print axioms nativeField_isSeparable

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
