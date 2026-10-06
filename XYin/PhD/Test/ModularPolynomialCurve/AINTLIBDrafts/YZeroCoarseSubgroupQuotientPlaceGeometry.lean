/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientPlaceResidueFinite
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientRelativeDimension
public import AINTLIBDrafts.ProperPlaceRecovery

/-!
# Closed-point representation of places of the actual subgroup quotient

Over a characteristic-zero field, for an actual finite locally free subgroup with
etale structural map, every intrinsic place of its quotient function field is
represented by a real closed quotient point. The place equals the literal
`closedPointPlace` defined using the original geometric structure-map constants.

The proof uses the actual quotient integrality, smoothness of relative dimension
one and properness, together with the already proved finite residue extension
for every quotient place. The public interface uses exactly the native chosen
killing integer and witness. The two examples check the raw and public APIs.

No parameter, chart, residue-finiteness, genus or Weierstrass-model premise is
added. This establishes existence of a closed-point representation; injectivity,
a bijection of points and places, quotient genus and quotient j are separate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open ModularPolynomialCurveTest.AINTLIB.LocalValuation

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] [CharZero k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) [Etale G.π] (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

theorem gluedQuotient_exists_closedPointPlace :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
      G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k (G.gluedQuotient N hkill).functionField,
      ∃ (y : G.gluedQuotient N hkill) (hy : IsClosed {y}),
        closedPointPlace (G.gluedQuotientS N hkill) y hy = v := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
    G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
  have : IsProper (G.gluedQuotientS N hkill) := G.gluedQuotientS_isProper N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  change ∀ v : FunctionField.Place k (G.gluedQuotient N hkill).functionField,
    ∃ (y : G.gluedQuotient N hkill) (hy : IsClosed {y}),
      closedPointPlace (G.gluedQuotientS N hkill) y hy = v
  intro v
  exact exists_closedPointPlace_eq (G.gluedQuotientS N hkill) v
    (G.gluedQuotient_place_finite_residueField N hkill v)

theorem quotient_exists_closedPointPlace [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : SmoothOfRelativeDimension 1 G.quotientS :=
      G.quotientS_smoothOfRelativeDimension_one
    let _ := G.quotientS.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k G.quotient.functionField,
      ∃ (y : G.quotient) (hy : IsClosed {y}), closedPointPlace G.quotientS y hy = v :=
  G.gluedQuotient_exists_closedPointPlace G.killN G.killN_spec

example :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
      G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k (G.gluedQuotient N hkill).functionField,
      ∃ (y : G.gluedQuotient N hkill) (hy : IsClosed {y}),
        closedPointPlace (G.gluedQuotientS N hkill) y hy = v :=
  G.gluedQuotient_exists_closedPointPlace N hkill

example [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : SmoothOfRelativeDimension 1 G.quotientS :=
      G.quotientS_smoothOfRelativeDimension_one
    let _ := G.quotientS.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k G.quotient.functionField,
      ∃ (y : G.quotient) (hy : IsClosed {y}), closedPointPlace G.quotientS y hy = v :=
  G.quotient_exists_closedPointPlace

#print axioms gluedQuotient_exists_closedPointPlace
#print axioms quotient_exists_closedPointPlace
#print axioms gluedQuotient_isIntegral
#print axioms gluedQuotientS_smoothOfRelativeDimension_one
#print axioms gluedQuotientS_isProper
#print axioms gluedQuotient_place_finite_residueField
#print axioms exists_closedPointPlace_eq
#print axioms closedPointPlace
#print axioms Scheme.Hom.functionFieldBaseAlgebra

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
