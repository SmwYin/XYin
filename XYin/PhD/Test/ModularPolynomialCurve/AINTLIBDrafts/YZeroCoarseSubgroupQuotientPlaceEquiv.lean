/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.SchemeClosedPointPlaceEquiv
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientPlaceGeometry

/-!
# Closed-point and intrinsic-place equivalence of the actual subgroup quotient

Over a characteristic-zero field, an actual finite locally free subgroup with
etale structural map has a quotient whose actual closed points correspond
bijectively to intrinsic places of its literal function field. Proved quotient
integrality, properness, relative dimension one and residue finiteness supply
the generic equivalence, preserving the independent geometric constants.

The public interface forwards the exact native chosen killing integer and
witness. Forward maps equal the existing closedPointPlace constructors, and
two raw/public clients check opposite roundtrips. No quotient model, genus or
function-field pullback premise is supplied.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open ModularPolynomialCurveTest.AINTLIB.LocalValuation

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] [CharZero k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) [Etale G.π] (N : ℕ) [NeZero N]
  (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)

noncomputable def gluedQuotientClosedPointPlaceEquiv :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    {y : G.gluedQuotient N hkill // IsClosed {y}} ≃
      FunctionField.Place k (G.gluedQuotient N hkill).functionField := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
    G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
  have : IsProper (G.gluedQuotientS N hkill) := G.gluedQuotientS_isProper N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  exact closedPointPlaceEquiv (G.gluedQuotientS N hkill)
    (G.gluedQuotient_place_finite_residueField N hkill)

theorem gluedQuotientClosedPointPlaceEquiv_apply
    (y : {y : G.gluedQuotient N hkill // IsClosed {y}}) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
      G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    G.gluedQuotientClosedPointPlaceEquiv N hkill y =
      closedPointPlace (G.gluedQuotientS N hkill) y.1 y.2 := rfl

noncomputable def quotientClosedPointPlaceEquiv [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ := G.quotientS.functionFieldBaseAlgebra
    {y : G.quotient // IsClosed {y}} ≃ FunctionField.Place k G.quotient.functionField :=
  G.gluedQuotientClosedPointPlaceEquiv G.killN G.killN_spec

theorem quotientClosedPointPlaceEquiv_apply [G.HasKillingInt]
    (y : {y : G.quotient // IsClosed {y}}) :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : SmoothOfRelativeDimension 1 G.quotientS :=
      G.quotientS_smoothOfRelativeDimension_one
    let _ := G.quotientS.functionFieldBaseAlgebra
    G.quotientClosedPointPlaceEquiv y = closedPointPlace G.quotientS y.1 y.2 :=
  G.gluedQuotientClosedPointPlaceEquiv_apply G.killN G.killN_spec y

example (y : G.gluedQuotient N hkill) (hy : IsClosed {y}) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
      G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    (G.gluedQuotientClosedPointPlaceEquiv N hkill).symm
      (closedPointPlace (G.gluedQuotientS N hkill) y hy) = ⟨y, hy⟩ := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
    G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  exact (G.gluedQuotientClosedPointPlaceEquiv N hkill).symm_apply_apply ⟨y, hy⟩

example [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : SmoothOfRelativeDimension 1 G.quotientS :=
      G.quotientS_smoothOfRelativeDimension_one
    let _ := G.quotientS.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k G.quotient.functionField,
      closedPointPlace G.quotientS ((G.quotientClosedPointPlaceEquiv).symm v).1
        ((G.quotientClosedPointPlaceEquiv).symm v).2 = v := by
  have : IsIntegral G.quotient := G.quotient_isIntegral
  have : SmoothOfRelativeDimension 1 G.quotientS := G.quotientS_smoothOfRelativeDimension_one
  let _ := G.quotientS.functionFieldBaseAlgebra
  dsimp only
  intro v
  exact (G.quotientClosedPointPlaceEquiv).apply_symm_apply v

#print axioms gluedQuotientClosedPointPlaceEquiv
#print axioms gluedQuotientClosedPointPlaceEquiv_apply
#print axioms quotientClosedPointPlaceEquiv
#print axioms quotientClosedPointPlaceEquiv_apply
#print axioms closedPointPlaceEquiv
#print axioms gluedQuotient_isIntegral
#print axioms gluedQuotientS_smoothOfRelativeDimension_one
#print axioms gluedQuotientS_isProper
#print axioms gluedQuotient_place_finite_residueField
#print axioms Scheme.Hom.functionFieldBaseAlgebra

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
