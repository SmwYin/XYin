/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseSubgroupQuotientPlaceMap
public import AINTLIBDrafts.SchemeClosedPointPlaceInjective
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Finite fibers of the actual quotient place restriction

The raw and public intrinsic place maps have finite fibers over arbitrary
base fields when the actual subgroup is etale. A nonempty place fiber has
a source closed-point representative. Equality of its target places forces
all source representatives into the same actual quotient point fiber, using
closed-point place injectivity on the target. Restricting that finite scheme
fiber to closed points and taking its place image bounds the whole place fiber.

The original geometric constant algebras are retained. No characteristic-zero,
target-place representation or place-equivalence hypothesis is used. This
supplies finite supports for pulling back finitely supported place data;
place-map surjectivity, divisor compatibility, genus and a quotient model
remain separate conclusions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open ModularCurves.YZeroCoarseJ
open ModularPolynomialCurveTest.AINTLIB.LocalValuation

universe u

namespace ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup

variable {k : Type u} [Field k] {E : EllipticCurve (Spec (.of k))}
  (G : E.FiniteLocallyFreeSubgroup) [Etale G.π]

theorem gluedQuotientPlaceMap_finite_preimage_singleton (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ w : FunctionField.Place k (G.gluedQuotient N hkill).functionField,
      (G.gluedQuotientPlaceMap N hkill ⁻¹' {w}).Finite := by
  have : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
  have : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
  have : SmoothOfRelativeDimension 1 (G.gluedQuotientS N hkill) :=
    G.gluedQuotientS_smoothOfRelativeDimension_one N hkill
  have : IsSeparated (G.gluedQuotientS N hkill) := G.gluedQuotientS_isSeparated N hkill
  have : IsFinite (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_isFinite N hkill
  let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
  let _ := E.π.functionFieldBaseAlgebra
  dsimp only
  intro w
  rcases Set.eq_empty_or_nonempty (G.gluedQuotientPlaceMap N hkill ⁻¹' {w}) with h | h
  · rw [h]
    exact Set.finite_empty
  obtain ⟨v₀, hv₀⟩ := h
  have hv₀ : G.gluedQuotientPlaceMap N hkill v₀ = w := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hv₀
  obtain ⟨x₀, hx₀, hplace₀⟩ := nativeField_exists_closedPointPlace E v₀
  have hw : closedPointPlace (G.gluedQuotientS N hkill) ((G.gluedQuotientπ N hkill) x₀)
      (G.gluedQuotientπ_isClosed_singleton N hkill x₀ hx₀) = w := by
    calc
      _ = G.gluedQuotientPlaceMap N hkill (closedPointPlace E.π x₀ hx₀) :=
        (G.gluedQuotientPlaceMap_closedPoint N hkill x₀ hx₀).symm
      _ = G.gluedQuotientPlaceMap N hkill v₀ :=
        congrArg (G.gluedQuotientPlaceMap N hkill) hplace₀
      _ = w := hv₀
  let T : Set {x : E.E // IsClosed {x}} :=
    Subtype.val ⁻¹' ((G.gluedQuotientπ N hkill) ⁻¹' {(G.gluedQuotientπ N hkill) x₀})
  have hT : T.Finite :=
    ((G.gluedQuotientπ N hkill).finite_preimage_singleton
      ((G.gluedQuotientπ N hkill) x₀)).preimage (fun _ _ _ _ h => Subtype.ext h)
  let p : {x : E.E // IsClosed {x}} → FunctionField.Place k E.E.functionField :=
    fun x => closedPointPlace E.π x.val x.property
  refine (hT.image p).subset ?_
  intro v hv
  have hv : G.gluedQuotientPlaceMap N hkill v = w := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hv
  obtain ⟨x, hx, hplace⟩ := nativeField_exists_closedPointPlace E v
  refine ⟨⟨x, hx⟩, ?_, hplace⟩
  change (G.gluedQuotientπ N hkill) x = (G.gluedQuotientπ N hkill) x₀
  apply closedPointPlace_injective (G.gluedQuotientS N hkill)
    ((G.gluedQuotientπ N hkill) x) (G.gluedQuotientπ_isClosed_singleton N hkill x hx)
    ((G.gluedQuotientπ N hkill) x₀) (G.gluedQuotientπ_isClosed_singleton N hkill x₀ hx₀)
  calc
    _ = G.gluedQuotientPlaceMap N hkill (closedPointPlace E.π x hx) :=
      (G.gluedQuotientPlaceMap_closedPoint N hkill x hx).symm
    _ = G.gluedQuotientPlaceMap N hkill v :=
      congrArg (G.gluedQuotientPlaceMap N hkill) hplace
    _ = w := hv
    _ = _ := hw.symm

theorem quotientPlaceMap_finite_preimage_singleton [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ w : FunctionField.Place k G.quotient.functionField, (G.quotientPlaceMap ⁻¹' {w}).Finite :=
  G.gluedQuotientPlaceMap_finite_preimage_singleton G.killN G.killN_spec

example (N : ℕ) [NeZero N] (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ w : FunctionField.Place k (G.gluedQuotient N hkill).functionField,
      (G.gluedQuotientPlaceMap N hkill ⁻¹' {w}).Finite :=
  G.gluedQuotientPlaceMap_finite_preimage_singleton N hkill

example [G.HasKillingInt] :
    let _ : IsIntegral G.quotient := G.quotient_isIntegral
    let _ : Surjective G.quotientπ := G.quotientπ_surjective
    let _ := G.quotientS.functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    ∀ w : FunctionField.Place k G.quotient.functionField, (G.quotientPlaceMap ⁻¹' {w}).Finite :=
  G.quotientPlaceMap_finite_preimage_singleton

#print axioms gluedQuotientPlaceMap_finite_preimage_singleton
#print axioms quotientPlaceMap_finite_preimage_singleton
#print axioms gluedQuotientPlaceMap_closedPoint
#print axioms nativeField_exists_closedPointPlace
#print axioms closedPointPlace_injective
#print axioms gluedQuotientπ_isFinite
#print axioms gluedQuotientS_isSeparated
#print axioms Scheme.Hom.finite_preimage_singleton
#print axioms Set.Finite.preimage
#print axioms Set.Finite.image
#print axioms Set.Finite.subset

end ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup
