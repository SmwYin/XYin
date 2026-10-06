/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.SchemeClosedPointPlaceInjective
public import AINTLIBDrafts.ProperPlaceRecovery
public import AINTLIBDrafts.NativePlaceResidueFinite

/-!
# Actual closed-point and intrinsic-place equivalences

A proper integral smooth curve of relative dimension one has a closed-point
place equivalence when every intrinsic place has finite residue over the
original geometric constants. The forward map is the actual closedPointPlace
constructor; proved injectivity and actual proper recovery supply the inverse.

For a native elliptic curve over any field, proved residue finiteness discharges
that input. The two API clients verify both directions. No quotient-curve,
coordinate-model or genus assumption is added to the native equivalence.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves

universe u

namespace ModularPolynomialCurveTest.AINTLIB.LocalValuation

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (π : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 π] [IsProper π]

noncomputable def closedPointPlaceEquiv
    (hfinite : let _ := π.functionFieldBaseAlgebra
      ∀ v : FunctionField.Place k X.functionField, Module.Finite k v.residueField) :
    let _ := π.functionFieldBaseAlgebra
    {x : X // IsClosed {x}} ≃ FunctionField.Place k X.functionField := by
  let _ := π.functionFieldBaseAlgebra
  let f : {x : X // IsClosed {x}} → FunctionField.Place k X.functionField :=
    fun x => closedPointPlace π x.1 x.2
  have hi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (closedPointPlace_injective π x.1 x.2 y.1 y.2 h)
  have hs : Function.Surjective f := by
    intro v
    obtain ⟨x, hx, heq⟩ := exists_closedPointPlace_eq π v (hfinite v)
    exact ⟨⟨x, hx⟩, heq⟩
  exact Equiv.ofBijective f ⟨hi, hs⟩

theorem closedPointPlaceEquiv_apply
    (hfinite : let _ := π.functionFieldBaseAlgebra
      ∀ v : FunctionField.Place k X.functionField, Module.Finite k v.residueField)
    (x : {x : X // IsClosed {x}}) :
    let _ := π.functionFieldBaseAlgebra
    closedPointPlaceEquiv π hfinite x = closedPointPlace π x.1 x.2 := rfl

theorem closedPointPlaceEquiv_symm_apply_closedPointPlace
    (hfinite : let _ := π.functionFieldBaseAlgebra
      ∀ v : FunctionField.Place k X.functionField, Module.Finite k v.residueField)
    (x : X) (hx : IsClosed {x}) :
    let _ := π.functionFieldBaseAlgebra
    (closedPointPlaceEquiv π hfinite).symm (closedPointPlace π x hx) = ⟨x, hx⟩ := by
  let _ := π.functionFieldBaseAlgebra
  exact (closedPointPlaceEquiv π hfinite).symm_apply_apply ⟨x, hx⟩

end ModularPolynomialCurveTest.AINTLIB.LocalValuation

namespace ModularCurves.YZeroCoarseJ

open ModularPolynomialCurveTest.AINTLIB.LocalValuation

variable {k : Type u} [Field k]

noncomputable def nativeFieldClosedPointPlaceEquiv (E : EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    {x : E.E // IsClosed {x}} ≃ FunctionField.Place k E.E.functionField := by
  let _ := E.π.functionFieldBaseAlgebra
  exact closedPointPlaceEquiv E.π (nativeField_finite_residueField E)

theorem nativeFieldClosedPointPlaceEquiv_apply (E : EllipticCurve (Spec (.of k)))
    (x : {x : E.E // IsClosed {x}}) :
    let _ := E.π.functionFieldBaseAlgebra
    nativeFieldClosedPointPlaceEquiv E x = closedPointPlace E.π x.1 x.2 := rfl

example (E : EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField,
      closedPointPlace E.π ((nativeFieldClosedPointPlaceEquiv E).symm v).1
        ((nativeFieldClosedPointPlaceEquiv E).symm v).2 = v := by
  let _ := E.π.functionFieldBaseAlgebra
  dsimp only
  intro v
  exact (nativeFieldClosedPointPlaceEquiv E).apply_symm_apply v

example (W : WeierstrassCurve k) [W.IsElliptic]
    (x : (modelEllipticCurve W).E) (hx : IsClosed {x}) :
    let _ := (modelEllipticCurve W).π.functionFieldBaseAlgebra
    (nativeFieldClosedPointPlaceEquiv (modelEllipticCurve W)).symm
      (closedPointPlace (modelEllipticCurve W).π x hx) = ⟨x, hx⟩ := by
  let _ := (modelEllipticCurve W).π.functionFieldBaseAlgebra
  exact (nativeFieldClosedPointPlaceEquiv (modelEllipticCurve W)).symm_apply_apply ⟨x, hx⟩

#print axioms closedPointPlaceEquiv
#print axioms closedPointPlaceEquiv_apply
#print axioms closedPointPlaceEquiv_symm_apply_closedPointPlace
#print axioms nativeFieldClosedPointPlaceEquiv
#print axioms nativeFieldClosedPointPlaceEquiv_apply
#print axioms closedPointPlace_injective
#print axioms exists_closedPointPlace_eq
#print axioms nativeField_finite_residueField
#print axioms Equiv.ofBijective

end ModularCurves.YZeroCoarseJ
