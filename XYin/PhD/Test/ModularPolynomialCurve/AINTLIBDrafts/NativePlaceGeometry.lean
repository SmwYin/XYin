/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.ProperPlaceRecovery
public import AINTLIBDrafts.NativePlaceResidueFinite

/-!
# Closed-point representation of every native elliptic place

Over any field, every intrinsic place of a native elliptic curve's actual
function field is represented by a real closed point. The original geometric
constant algebra remains fixed. Proved native residue finiteness and actual
proper smooth-curve recovery supply the representation.

No extra residue-finiteness, coordinate-chart or characteristic-zero premise
is supplied. The native curve and Weierstrass model examples verify the actual
interfaces. Point injectivity, a place bijection and quotient genus remain
separate mathematical steps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open ModularPolynomialCurveTest.AINTLIB.LocalValuation

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

theorem nativeField_exists_closedPointPlace (E : EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField,
      ∃ (x : E.E) (hx : IsClosed {x}), closedPointPlace E.π x hx = v := by
  let _ := E.π.functionFieldBaseAlgebra
  dsimp only
  intro v
  exact exists_closedPointPlace_eq E.π v (nativeField_finite_residueField E v)

example (E : EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField,
      ∃ (x : E.E) (hx : IsClosed {x}), closedPointPlace E.π x hx = v :=
  nativeField_exists_closedPointPlace E

example (W : WeierstrassCurve k) [W.IsElliptic] :
    let E := modelEllipticCurve W
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField,
      ∃ (x : E.E) (hx : IsClosed {x}), closedPointPlace E.π x hx = v :=
  nativeField_exists_closedPointPlace (modelEllipticCurve W)

#print axioms nativeField_exists_closedPointPlace
#print axioms nativeField_finite_residueField
#print axioms exists_closedPointPlace_eq
#print axioms closedPointPlace
#print axioms modelEllipticCurve
#print axioms nativeField_functionField
#print axioms nativeField_isSeparable

end ModularCurves.YZeroCoarseJ
