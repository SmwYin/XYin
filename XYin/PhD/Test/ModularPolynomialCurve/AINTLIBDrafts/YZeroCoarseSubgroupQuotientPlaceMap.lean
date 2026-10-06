/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientPlaceRestriction

/-!
# Intrinsic place restriction along the actual etale subgroup quotient

A place is determined by its normalized valuation, through the actual
valuation-subring recovery formula. For the raw and public finite subgroup
quotients, choose the target place supplied by the proved all-source-place
valuation theorem. Its valuation agrees with the source valuation on the
literal native function-field pullback, and closed-point places map to the
places of their actual quotient images.

The two geometric constant algebras remain independently defined. These APIs
hold over arbitrary fields with the actual subgroup etaleness input, without
any target-place representation or characteristic-zero premise. Finite fibers,
surjectivity of the place map, genus and a quotient model are separate claims.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open ModularPolynomialCurveTest.AINTLIB.LocalValuation

universe u

namespace FunctionField.Place

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

theorem valuation_injective : Function.Injective (valuation (k := k) (K := K)) := by
  intro v w h
  apply ext
  calc
    v.toValuationSubring = v.valuation.valuationSubring := (valuationSubring_valuation v).symm
    _ = w.valuation.valuationSubring := congrArg Valuation.valuationSubring h
    _ = w.toValuationSubring := valuationSubring_valuation w

end FunctionField.Place

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) [Etale G.π]

noncomputable def gluedQuotientPlaceMap (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    FunctionField.Place k E.E.functionField →
      FunctionField.Place k (G.gluedQuotient N hkill).functionField := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  exact fun v => Classical.choose (G.gluedQuotientπ_exists_place_valuation N hkill v)

theorem gluedQuotientPlaceMap_valuation (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField,
      ∀ z : (G.gluedQuotient N hkill).functionField,
        (G.gluedQuotientPlaceMap N hkill v).valuation z =
          v.valuation ((G.gluedQuotientπ N hkill).functionFieldMap.hom z) := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  exact fun v z => Classical.choose_spec (G.gluedQuotientπ_exists_place_valuation N hkill v) z

theorem gluedQuotientPlaceMap_closedPoint (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
      G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ (x : E.E) (hx : IsClosed {x}),
      G.gluedQuotientPlaceMap N hkill (closedPointPlace E.π x hx) =
        closedPointPlace (G.gluedQuotientS N hkill) ((G.gluedQuotientπ N hkill) x)
          (G.gluedQuotientπ_isClosed_singleton N hkill x hx) := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
    G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  dsimp only
  intro x hx
  apply FunctionField.Place.valuation_injective
  apply Valuation.ext
  intro z
  exact (G.gluedQuotientPlaceMap_valuation N hkill _ z).trans
    (G.gluedQuotientπ_closedPointPlace_valuation N hkill x hx z).symm

noncomputable def quotientPlaceMap [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    FunctionField.Place k E.E.functionField → FunctionField.Place k G.quotient.functionField :=
  G.gluedQuotientPlaceMap G.killN G.killN_spec

theorem quotientPlaceMap_valuation [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField, ∀ z : G.quotient.functionField,
      (G.quotientPlaceMap v).valuation z = v.valuation (G.quotientπ.functionFieldMap.hom z) :=
  G.gluedQuotientPlaceMap_valuation G.killN G.killN_spec

theorem quotientPlaceMap_closedPoint [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : SmoothOfRelativeDimension 1 G.quotientS := G.quotientS_smoothOfRelativeDimension_one
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ (x : E.E) (hx : IsClosed {x}),
      G.quotientPlaceMap (closedPointPlace E.π x hx) =
        closedPointPlace G.quotientS (G.quotientπ x)
          (G.gluedQuotientπ_isClosed_singleton G.killN G.killN_spec x hx) :=
  G.gluedQuotientPlaceMap_closedPoint G.killN G.killN_spec

example (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField,
      ∀ z : (G.gluedQuotient N hkill).functionField,
        (G.gluedQuotientPlaceMap N hkill v).valuation z =
          v.valuation ((G.gluedQuotientπ N hkill).functionFieldMap.hom z) :=
  G.gluedQuotientPlaceMap_valuation N hkill

example [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : SmoothOfRelativeDimension 1 G.quotientS := G.quotientS_smoothOfRelativeDimension_one
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ (x : E.E) (hx : IsClosed {x}),
      G.quotientPlaceMap (closedPointPlace E.π x hx) =
        closedPointPlace G.quotientS (G.quotientπ x)
          (G.gluedQuotientπ_isClosed_singleton G.killN G.killN_spec x hx) :=
  G.quotientPlaceMap_closedPoint

#print axioms FunctionField.Place.valuation_injective
#print axioms gluedQuotientPlaceMap
#print axioms gluedQuotientPlaceMap_valuation
#print axioms gluedQuotientPlaceMap_closedPoint
#print axioms quotientPlaceMap
#print axioms quotientPlaceMap_valuation
#print axioms quotientPlaceMap_closedPoint
#print axioms FunctionField.Place.ext
#print axioms FunctionField.Place.valuationSubring_valuation
#print axioms Valuation.ext
#print axioms gluedQuotientπ_exists_place_valuation
#print axioms gluedQuotientπ_closedPointPlace_valuation

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
