/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.HermiteNormalForm.RankTwo
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Row Hermite bases of integer submodules

The rows of the transpose of an inclusion matrix are the coordinates of its basis vectors.
Changing the submodule basis therefore performs row operations on this transpose. This file
deduces rank-two basis existence from row HNF and supplies coordinate facts independent of HNF.
-/

open Module Matrix

namespace Matrix

/-- A square coordinate matrix over a domain is nonsingular exactly when its linear map
between the two based modules is injective. -/
theorem toLin_injective_iff_det_ne_zero {R M₁ M₂ n : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [IsDomain R] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]
    (b₁ : Basis n R M₁) (b₂ : Basis n R M₂) {A : Matrix n n R} :
    Function.Injective (toLin b₁ b₂ A) ↔ A.det ≠ 0 := by
  have hcoord : b₂.equivFun ∘ toLin b₁ b₂ A = A.mulVec ∘ b₁.equivFun := by
    funext x
    exact repr_toLin b₁ b₂ A x
  rw [← b₂.equivFun.injective.of_comp_iff, hcoord,
    Function.Injective.of_comp_iff' _ b₁.equivFun.bijective]
  change Function.Injective (toLin' A) ↔ _
  rw [← LinearMap.ker_eq_bot, ← not_ne_iff,
    ← LinearMap.det_eq_zero_iff_ker_ne_bot, ← LinearMap.det_toMatrix']
  simp

end Matrix

namespace Module.Basis

variable {M : Type*} [AddCommGroup M] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The index of an integer submodule is the absolute determinant of its inclusion matrix.
No normal-form condition on either chosen basis is needed. -/
theorem index_eq_natAbs_det_toMatrix (bM : Basis ι ℤ M) (N : Submodule ℤ M)
    (bN : Basis ι ℤ N) :
    N.toAddSubgroup.index = (LinearMap.toMatrix bN bM N.subtype).det.natAbs := by
  rw [AddSubgroup.index_eq_natAbs_det bM N.toAddSubgroup bN, Basis.det_apply]
  congr 2
  ext i j
  simp only [Basis.toMatrix_apply, LinearMap.toMatrix_apply, Submodule.subtype_apply]

end Module.Basis

namespace Submodule

variable {M : Type*} [AddCommGroup M]

/-- A full-rank submodule of a rank-two integer module has a basis whose coordinate rows
are in Hermite normal form relative to the specified ambient basis. -/
theorem exists_basis_isHermiteNormalForm (bM : Basis (Fin 2) ℤ M)
    (N : Submodule ℤ M) (hN : Module.finrank ℤ N = 2) :
    ∃ bN : Basis (Fin 2) ℤ N,
      (LinearMap.toMatrix bN bM N.subtype)ᵀ.IsHermiteNormalForm := by
  let := Module.Free.of_basis bM
  let := Module.Finite.of_basis bM
  let b : Basis (Fin 2) ℤ N := (Module.finBasis ℤ N).reindex (finCongr hN)
  let A := LinearMap.toMatrix b bM N.subtype
  have hA : A.det ≠ 0 := (Matrix.toLin_injective_iff_det_ne_zero b bM).mp (by
    simpa only [A, Matrix.toLin_toMatrix] using N.subtype_injective)
  obtain ⟨U, hU, hH⟩ :=
    Matrix.exists_isUnit_det_mul_isHermiteNormalForm_fin_two Aᵀ (by simpa using hA)
  let e := Matrix.toLinearEquiv b Uᵀ (by simpa using hU)
  refine ⟨b.map e, ?_⟩
  have hmatrix : LinearMap.toMatrix (b.map e) bM N.subtype = A * Uᵀ := by
    rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_comp b b bM]
    congr 1
    exact LinearMap.toMatrix_toLin b b Uᵀ
  simpa only [hmatrix, Matrix.transpose_mul, Matrix.transpose_transpose] using hH

end Submodule
