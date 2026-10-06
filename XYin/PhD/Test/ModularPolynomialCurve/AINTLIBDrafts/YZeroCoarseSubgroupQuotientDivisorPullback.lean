/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientPlaceMapFiniteFibers
public import AINTLIBDrafts.FinsuppFiniteFiberPullback
public import ModularCurves.Vendored.RiemannRoch.CoordinateFree.Divisor

/-!
# Divisor pullback along the actual etale subgroup quotient

The proved actual place restriction has finite fibers, so coefficient
precomposition defines an additive homomorphism from quotient divisors to
source divisors. Its coefficient at a source place is the original coefficient
at that place's actual quotient image. The public wrapper uses the literal
chosen killing datum.

These declarations hold over any base field with the actual subgroup etaleness
input. Both geometric constant algebras remain independently defined. No chart,
characteristic-zero, principal-divisor compatibility, degree, genus or quotient
model assertion is used by this coefficient pullback.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) [Etale G.π]

noncomputable def gluedQuotientDivisorPullback (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    FunctionField.Divisor k (G.gluedQuotient N hkill).functionField →+
      FunctionField.Divisor k E.E.functionField := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  exact Finsupp.comapDomainOfFiniteFibers (G.gluedQuotientPlaceMap N hkill)
    (G.gluedQuotientPlaceMap_finite_preimage_singleton N hkill)

theorem gluedQuotientDivisorPullback_apply (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ (D : FunctionField.Divisor k (G.gluedQuotient N hkill).functionField)
      (v : FunctionField.Place k E.E.functionField),
      G.gluedQuotientDivisorPullback N hkill D v = D (G.gluedQuotientPlaceMap N hkill v) := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  dsimp only
  intro D v
  rfl

noncomputable def quotientDivisorPullback [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    FunctionField.Divisor k G.quotient.functionField →+
      FunctionField.Divisor k E.E.functionField :=
  G.gluedQuotientDivisorPullback G.killN G.killN_spec

theorem quotientDivisorPullback_apply [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ (D : FunctionField.Divisor k G.quotient.functionField)
      (v : FunctionField.Place k E.E.functionField),
      G.quotientDivisorPullback D v = D (G.quotientPlaceMap v) :=
  G.gluedQuotientDivisorPullback_apply G.killN G.killN_spec

example (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ (D D' : FunctionField.Divisor k (G.gluedQuotient N hkill).functionField)
      (v : FunctionField.Place k E.E.functionField),
      G.gluedQuotientDivisorPullback N hkill (D + D') v =
        D (G.gluedQuotientPlaceMap N hkill v) +
          D' (G.gluedQuotientPlaceMap N hkill v) := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  dsimp only
  intro D D' v
  rfl

example [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ (D : FunctionField.Divisor k G.quotient.functionField)
      (v : FunctionField.Place k E.E.functionField),
      G.quotientDivisorPullback D v = D (G.quotientPlaceMap v) :=
  G.quotientDivisorPullback_apply

#print axioms gluedQuotientDivisorPullback
#print axioms gluedQuotientDivisorPullback_apply
#print axioms quotientDivisorPullback
#print axioms quotientDivisorPullback_apply
#print axioms Finsupp.comapDomainOfFiniteFibers
#print axioms Finsupp.comapDomainOfFiniteFibers_apply
#print axioms gluedQuotientPlaceMap_finite_preimage_singleton
#print axioms quotientPlaceMap_finite_preimage_singleton
#print axioms FunctionField.Divisor

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
