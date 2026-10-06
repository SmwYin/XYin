/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.NativePlaceGeometry
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientClosedPointPlaceValuation

/-!
# All source places under the actual etale subgroup quotient

Every intrinsic place of the native elliptic field is represented by a real
closed point. Its actual finite quotient image is closed, and the proved
closed-point valuation formula supplies a target place whose normalized
valuation equals the source valuation on the literal native field pullback.

This holds over arbitrary fields with the actual subgroup etaleness input.
It introduces no closed-point, residue-finiteness or parameter premise. The
raw and public APIs retain independent geometric constants. No place-map
surjectivity, cross-field genus formula or quotient model is asserted.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open ModularCurves.YZeroCoarseJ
open ModularPolynomialCurveTest.AINTLIB.LocalValuation

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) [Etale G.π]

theorem gluedQuotientπ_exists_place_valuation (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField,
      ∃ w : FunctionField.Place k (G.gluedQuotient N hkill).functionField,
        ∀ z : (G.gluedQuotient N hkill).functionField,
          w.valuation z = v.valuation ((G.gluedQuotientπ N hkill).functionFieldMap.hom z) := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  have : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
    G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  dsimp only
  intro v
  obtain ⟨x, hx, rfl⟩ := nativeField_exists_closedPointPlace E v
  refine ⟨closedPointPlace (G.gluedQuotientS N hkill) ((G.gluedQuotientπ N hkill) x)
    (G.gluedQuotientπ_isClosed_singleton N hkill x hx), ?_⟩
  exact G.gluedQuotientπ_closedPointPlace_valuation N hkill x hx

theorem quotientπ_exists_place_valuation [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField,
      ∃ w : FunctionField.Place k G.quotient.functionField,
        ∀ z : G.quotient.functionField,
          w.valuation z = v.valuation (G.quotientπ.functionFieldMap.hom z) :=
  G.gluedQuotientπ_exists_place_valuation G.killN G.killN_spec

example (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField,
      ∃ w : FunctionField.Place k (G.gluedQuotient N hkill).functionField,
        ∀ z : (G.gluedQuotient N hkill).functionField,
          w.valuation z = v.valuation ((G.gluedQuotientπ N hkill).functionFieldMap.hom z) :=
  G.gluedQuotientπ_exists_place_valuation N hkill

example [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField,
      ∃ w : FunctionField.Place k G.quotient.functionField,
        ∀ z : G.quotient.functionField,
          w.valuation z = v.valuation (G.quotientπ.functionFieldMap.hom z) :=
  G.quotientπ_exists_place_valuation

#print axioms gluedQuotientπ_exists_place_valuation
#print axioms quotientπ_exists_place_valuation
#print axioms nativeField_exists_closedPointPlace
#print axioms gluedQuotientπ_closedPointPlace_valuation
#print axioms gluedQuotientπ_isClosed_singleton
#print axioms gluedQuotient_isIntegral
#print axioms gluedQuotientπ_surjective
#print axioms gluedQuotientS_smoothOfRelativeDimension_one

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
