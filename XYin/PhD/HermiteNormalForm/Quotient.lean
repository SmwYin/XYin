/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.HermiteNormalForm.Content
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Pi

/-! # Matrix content and cyclic lattice quotients

Content is independent of both bases of a linear map. For an inclusion between free integer
modules of rank two, the quotient is cyclic exactly when the inclusion matrix has content one.
These statements do not assume a Hermite normal form.
-/

open Module Matrix

namespace LinearMap

variable {M N ι κ : Type*} [AddCommGroup M] [AddCommGroup N]
  [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- Changing either integer basis preserves the content of a linear map's matrix. -/
theorem content_toMatrix_eq (f : M →ₗ[ℤ] N)
    (b b' : Basis ι ℤ M) (c c' : Basis κ ℤ N) :
    (toMatrix b c f).content = (toMatrix b' c' f).content := by
  classical
  rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b b' c c' f,
    content_mul_of_isUnit_det _
      (Matrix.isUnit_det_of_right_inverse (b'.toMatrix_mul_toMatrix_flip b)),
    content_isUnit_det_mul
      (Matrix.isUnit_det_of_right_inverse (c.toMatrix_mul_toMatrix_flip c'))]

end LinearMap

namespace Submodule

variable {M : Type*} [AddCommGroup M]

/-- In Smith bases, the matrix of the inclusion has the Smith coefficients on its diagonal. -/
theorem toMatrix_subtype_smithNormalForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Submodule ℤ M) (b : Basis ι ℤ M)
    (h : Module.finrank ℤ N = Module.finrank ℤ M) :
    LinearMap.toMatrix (N.smithNormalFormBotBasis b h) (N.smithNormalFormTopBasis b h)
      N.subtype = Matrix.diagonal (N.smithNormalFormCoeffs b h) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [LinearMap.toMatrix_apply, Submodule.smithNormalFormBotBasis_def]
  · simp [LinearMap.toMatrix_apply, Submodule.smithNormalFormBotBasis_def, hij]

/-- A rank-two lattice quotient is cyclic exactly when its two Smith coefficients are coprime. -/
theorem quotient_isAddCyclic_iff_coprime_smithNormalFormCoeffs
    (N : Submodule ℤ M) (b : Basis (Fin 2) ℤ M)
    (h : Module.finrank ℤ N = Module.finrank ℤ M) :
    IsAddCyclic (M ⧸ N) ↔
      (N.smithNormalFormCoeffs b h 0).natAbs.Coprime
        (N.smithNormalFormCoeffs b h 1).natAbs := by
  let e := (N.quotientEquivPiZMod b h).trans
    (LinearEquiv.piFinTwo ℤ (fun i ↦ ZMod (N.smithNormalFormCoeffs b h i).natAbs)).toAddEquiv
  rw [e.isAddCyclic, AddGroup.isAddCyclic_prod_iff]
  simp [show IsAddCyclic (ZMod (N.smithNormalFormCoeffs b h 0).natAbs) from inferInstance,
    show IsAddCyclic (ZMod (N.smithNormalFormCoeffs b h 1).natAbs) from inferInstance]

end Submodule

namespace Module.Basis

variable {M : Type*} [AddCommGroup M]

/-- A full-rank integer lattice in dimension two has cyclic quotient exactly when the content
of its inclusion matrix is one. -/
theorem quotient_isAddCyclic_iff_content_toMatrix_eq_one (bM : Basis (Fin 2) ℤ M)
    (N : Submodule ℤ M) (bN : Basis (Fin 2) ℤ N) :
    IsAddCyclic (M ⧸ N) ↔ (LinearMap.toMatrix bN bM N.subtype).content = 1 := by
  have h : Module.finrank ℤ N = Module.finrank ℤ M := by
    rw [Module.finrank_eq_card_basis bN, Module.finrank_eq_card_basis bM]
  rw [N.quotient_isAddCyclic_iff_coprime_smithNormalFormCoeffs bM h,
    N.subtype.content_toMatrix_eq bN (N.smithNormalFormBotBasis bM h) bM
      (N.smithNormalFormTopBasis bM h), N.toMatrix_subtype_smithNormalForm bM h,
    Matrix.content_diagonal_fin_two]
end Module.Basis
