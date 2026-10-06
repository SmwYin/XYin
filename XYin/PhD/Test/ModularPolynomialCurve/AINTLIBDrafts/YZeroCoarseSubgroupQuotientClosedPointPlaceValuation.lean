/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.SchemeClosedPointPlaceValuation
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientFinite
public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientEtale

/-!
# Actual subgroup quotient closed-point place valuations

The genuine finite subgroup quotient projection sends a closed source point
to a closed target point. This closed-image assertion uses no étale subgroup
premise. For an étale subgroup over a field, the proved quotient integrality,
relative dimension one, surjectivity and étale projection then give the actual
closed-point valuation comparison along the literal native function-field map.

The curve and quotient constants are specified independently by their actual
structure maps. Target closedness is derived rather than required as input.
The public interface uses its genuine chosen killing integer and equation.
Raw and public examples verify the same maps; all-place recovery and genus
statements remain separate mathematical steps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open ModularPolynomialCurveTest.AINTLIB.LocalValuation

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup)

/-- The actual finite quotient projection sends a genuine closed point to a closed point. -/
theorem gluedQuotientπ_isClosed_singleton (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)
    (x : E.E) (hx : IsClosed {x}) : IsClosed {(G.gluedQuotientπ N hkill) x} := by
  have : IsFinite (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_isFinite N hkill
  simpa only [Set.image_singleton] using (G.gluedQuotientπ N hkill).isClosedMap {x} hx

variable [Etale G.π]

/-- Valuations of actual raw quotient closed-point places agree under native field pullback. -/
theorem gluedQuotientπ_closedPointPlace_valuation (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)
    (x : E.E) (hx : IsClosed {x}) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
      G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ z : (G.gluedQuotient N hkill).functionField,
    (closedPointPlace (G.gluedQuotientS N hkill) ((G.gluedQuotientπ N hkill) x)
      (G.gluedQuotientπ_isClosed_singleton N hkill x hx)).valuation z =
      (closedPointPlace E.π x hx).valuation
        ((G.gluedQuotientπ N hkill).functionFieldMap.hom z) := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
    G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  have : Etale (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_etale N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  dsimp only
  intro z
  exact closedPointPlace_valuation_functionFieldMap E.π (G.gluedQuotientS N hkill)
    (G.gluedQuotientπ N hkill) x hx (G.gluedQuotientπ_isClosed_singleton N hkill x hx) z

/-- The public quotient forwards its genuine chosen killing integer and equation. -/
theorem quotientπ_closedPointPlace_valuation [G.HasKillingInt]
    (x : E.E) (hx : IsClosed {x}) :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : SmoothOfRelativeDimension 1 G.quotientS := G.quotientS_smoothOfRelativeDimension_one
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ z : G.quotient.functionField,
    (closedPointPlace G.quotientS (G.quotientπ x)
      (G.gluedQuotientπ_isClosed_singleton G.killN G.killN_spec x hx)).valuation z =
      (closedPointPlace E.π x hx).valuation (G.quotientπ.functionFieldMap.hom z) :=
  G.gluedQuotientπ_closedPointPlace_valuation G.killN G.killN_spec x hx

example (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)
    (x : E.E) (hx : IsClosed {x}) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
      G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ z : (G.gluedQuotient N hkill).functionField,
    (closedPointPlace (G.gluedQuotientS N hkill) ((G.gluedQuotientπ N hkill) x)
      (G.gluedQuotientπ_isClosed_singleton N hkill x hx)).valuation z =
      (closedPointPlace E.π x hx).valuation
        ((G.gluedQuotientπ N hkill).functionFieldMap.hom z) :=
  G.gluedQuotientπ_closedPointPlace_valuation N hkill x hx

example [G.HasKillingInt] (x : E.E) (hx : IsClosed {x}) :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : SmoothOfRelativeDimension 1 G.quotientS := G.quotientS_smoothOfRelativeDimension_one
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ z : G.quotient.functionField,
    (closedPointPlace G.quotientS (G.quotientπ x)
      (G.gluedQuotientπ_isClosed_singleton G.killN G.killN_spec x hx)).valuation z =
      (closedPointPlace E.π x hx).valuation (G.quotientπ.functionFieldMap.hom z) :=
  G.quotientπ_closedPointPlace_valuation x hx

#print axioms gluedQuotientπ_isClosed_singleton
#print axioms gluedQuotientπ_closedPointPlace_valuation
#print axioms quotientπ_closedPointPlace_valuation
#print axioms Scheme.Hom.isClosedMap
#print axioms Set.image_singleton
#print axioms gluedQuotientπ_isFinite
#print axioms quotientπ_isFinite
#print axioms gluedQuotient_isIntegral
#print axioms quotient_isIntegral
#print axioms gluedQuotientS_smoothOfRelativeDimension_one
#print axioms quotientS_smoothOfRelativeDimension_one
#print axioms gluedQuotientπ_surjective
#print axioms quotientπ_surjective
#print axioms gluedQuotientπ_etale
#print axioms quotientπ_etale
#print axioms closedPointPlace_valuation_functionFieldMap

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
