/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.NativeFunctionFieldStructure
public import AINTLIBDrafts.IntrinsicPlaceResidueFinite

/-!
# Finite residue fields of all native elliptic places

The independently geometric base algebra and the proved native separating
function-field pack imply finite residue fields and positive degrees for
every intrinsic place, over any field. No geometric place correspondence
or additional residue-finiteness premise is supplied.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ModularCurves
open scoped Polynomial RatFunc

universe u

namespace ModularCurves.YZeroCoarseJ

variable {k : Type u} [Field k]

theorem nativeField_finite_residueField (E : EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField, Module.Finite k v.residueField := by
  let _ := E.π.functionFieldBaseAlgebra
  let _ := nativeFieldPolynomialAlgebra E
  let _ := nativeFieldRatFuncAlgebra E
  let _ := nativeFieldPolynomial_baseTower E
  let _ := nativeFieldRatFunc_polynomialTower E
  let _ := nativeField_functionField E
  let _ := nativeField_isSeparable E
  dsimp only
  intro v
  exact FunctionField.Place.finite_residueField k E.E.functionField v

theorem nativeField_place_degree_pos (E : EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField, 0 < v.degree := by
  let _ := E.π.functionFieldBaseAlgebra
  dsimp only
  intro v
  let _ := nativeField_finite_residueField E v
  exact Module.finrank_pos

example (E : EllipticCurve (Spec (.of k))) :
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField, Module.Finite k v.residueField :=
  nativeField_finite_residueField E

example (W : WeierstrassCurve k) [W.IsElliptic] :
    let E := modelEllipticCurve W
    let _ := E.π.functionFieldBaseAlgebra
    ∀ v : FunctionField.Place k E.E.functionField, 0 < v.degree :=
  nativeField_place_degree_pos (modelEllipticCurve W)

#print axioms nativeField_finite_residueField
#print axioms nativeField_place_degree_pos
#print axioms FunctionField.Place.finite_residueField
#print axioms nativeField_functionField
#print axioms nativeField_isSeparable
#print axioms nativeFieldPolynomial_baseTower
#print axioms nativeFieldRatFunc_polynomialTower
#print axioms Module.finrank_pos

end ModularCurves.YZeroCoarseJ
