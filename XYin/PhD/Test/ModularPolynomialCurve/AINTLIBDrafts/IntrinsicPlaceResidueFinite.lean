/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import ModularCurves.Vendored.RiemannRoch.CoordinateFree.Divisor

/-!
# IntrinsicPlaceResidueFinite

Every intrinsic place of an actual finite separable function field has
finite residue extension and positive residue degree. The proof uses
the genuine finite/infinite chart classification and residue equivalences.
The original constant-field algebra is preserved.
-/

@[expose] public section

open scoped Polynomial RatFunc

namespace FunctionField.Place

variable (k K : Type*) [Field k] [Field K]
  [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]

theorem finite_residueField (v : Place k K) : Module.Finite k v.residueField := by
  obtain ⟨w, rfl⟩ := exists_chart k K v
  rcases w with w | w
  · exact (finiteResidueAlgEquiv k K w).toLinearEquiv.finiteDimensional
  · exact (infiniteResidueAlgEquiv k K w).toLinearEquiv.finiteDimensional

theorem degree_pos (v : Place k K) : 0 < v.degree := by
  let _ := finite_residueField k K v
  exact Module.finrank_pos

example (v : Place k K) : Module.Finite k v.residueField := finite_residueField k K v

example (v : Place k K) : v.degree ≠ 0 := (degree_pos k K v).ne'

#print axioms finite_residueField
#print axioms degree_pos
#print axioms exists_chart
#print axioms finiteResidueAlgEquiv
#print axioms infiniteResidueAlgEquiv
#print axioms FunctionField.Chart.PlaceA.finiteDimensionalResidueFieldFinite
#print axioms FunctionField.Chart.PlaceA.finiteDimensionalResidueFieldInfinite

end FunctionField.Place
