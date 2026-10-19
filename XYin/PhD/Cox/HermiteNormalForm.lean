/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.HermiteNormalForm.Basis
import XYin.PhD.HermiteNormalForm.Quotient
import XYin.PhD.Cox.MatrixCoordinates

/-!
# Normalized inclusion bases for Cox's period convention

Row Hermite normal form acts on lists of generators. Cox orders the generators as
`[d ω₁, b ω₁ + a ω₂]`, so the matrix acting on the upper half-plane is the anti-transpose
of the inclusion matrix. This file derives that convention from the row HNF API.

`Cox.InclusionNormalForm` records a basis and its row HNF certificate. Its inclusion
matrix is computed from the basis; it is not independent stored data.
-/

open Module

noncomputable section

namespace Cox

/-- A normalized basis of a rank-two inclusion, with the generator order used by Cox. -/
structure InclusionNormalForm {M : Type*} [AddCommGroup M]
    (bM : Basis (Fin 2) ℤ M) (N : Submodule ℤ M) where
  /-- The generators of the sublattice, in period order. -/
  basis : Basis (Fin 2) ℤ N
  /-- Reversing both coordinate orders turns the inclusion into a row HNF. -/
  isHermiteNormalForm :
    (LinearMap.toMatrix basis bM N.subtype).antiTranspose.IsHermiteNormalForm

namespace InclusionNormalForm

variable {M : Type*} [AddCommGroup M] {bM : Basis (Fin 2) ℤ M} {N : Submodule ℤ M}

/-- The inclusion matrix determined by the normalized basis. -/
def matrix (h : InclusionNormalForm bM N) : Matrix (Fin 2) (Fin 2) ℤ :=
  LinearMap.toMatrix h.basis bM N.subtype

@[simp]
theorem repr_apply (h : InclusionNormalForm bM N) (i j : Fin 2) :
    bM.repr (h.basis j : M) i = h.matrix i j := by
  simp only [matrix, LinearMap.toMatrix_apply, Submodule.subtype_apply]

/-- The coordinate matrix carries the row-normality certificate. -/
theorem matrix_isHermiteNormalForm (h : InclusionNormalForm bM N) :
    h.matrix.antiTranspose.IsHermiteNormalForm := h.isHermiteNormalForm

/-- Inclusion matrices of bases have nonzero determinant. -/
theorem det_ne_zero (h : InclusionNormalForm bM N) : h.matrix.det ≠ 0 := by
  apply (Matrix.toLin_injective_iff_det_ne_zero h.basis bM).mp
  simpa only [matrix, Matrix.toLin_toMatrix] using N.subtype_injective

/-- The normalized inclusion has positive determinant. -/
theorem det_pos (h : InclusionNormalForm bM N) : 0 < h.matrix.det := by
  have hn : h.matrix.antiTranspose.det ≠ 0 := by simpa using h.det_ne_zero
  simpa only [Matrix.det_antiTranspose] using h.matrix_isHermiteNormalForm.det_pos hn

@[simp]
theorem one_zero (h : InclusionNormalForm bM N) : h.matrix 1 0 = 0 := by
  have hz := h.matrix_isHermiteNormalForm.isUpperTriangular
    (show (0 : Fin 2) < 1 by decide)
  exact hz

theorem zero_zero_pos (h : InclusionNormalForm bM N) : 0 < h.matrix 0 0 := by
  have hn : h.matrix.antiTranspose.det ≠ 0 := by simpa using h.det_ne_zero
  exact h.matrix_isHermiteNormalForm.diagonal_pos hn 1

theorem one_one_pos (h : InclusionNormalForm bM N) : 0 < h.matrix 1 1 := by
  have hn : h.matrix.antiTranspose.det ≠ 0 := by simpa using h.det_ne_zero
  exact h.matrix_isHermiteNormalForm.diagonal_pos hn 0

theorem zero_one_mem (h : InclusionNormalForm bM N) :
    h.matrix 0 1 ∈ Set.Ico 0 (h.matrix 0 0) := by
  have hn : h.matrix.antiTranspose.det ≠ 0 := by simpa using h.det_ne_zero
  have hr := h.matrix_isHermiteNormalForm.reduced (show (0 : Fin 2) < 1 by decide)
    (h.matrix_isHermiteNormalForm.isRowEchelon.isLeadingEntry_diag hn 1)
  exact hr

/-- Coordinates in the ambient basis are obtained by applying the inclusion matrix. -/
theorem repr_eq_mulVec (h : InclusionNormalForm bM N) (y : N) :
    ⇑(bM.repr (y : M)) = h.matrix.mulVec ⇑(h.basis.repr y) :=
  (LinearMap.toMatrix_mulVec_repr h.basis bM N.subtype y).symm

/-- Cramer's identity for the inclusion coordinates. -/
theorem det_smul_repr (h : InclusionNormalForm bM N) (y : N) :
    h.matrix.det • ⇑(h.basis.repr y) = h.matrix.adjugate.mulVec ⇑(bM.repr (y : M)) := by
  rw [h.repr_eq_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The inclusion matrix has image equal to the represented submodule. -/
theorem range_toLin_matrix_eq (h : InclusionNormalForm bM N) :
    LinearMap.range (Matrix.toLin bM bM h.matrix) = N := by
  let e := bM.equiv h.basis (Equiv.refl (Fin 2))
  have he : Matrix.toLin bM bM h.matrix = N.subtype.comp e.toLinearMap := by
    apply (LinearMap.toMatrix bM bM).injective
    simp [matrix, LinearMap.toMatrix_comp bM h.basis bM,
      LinearMap.toMatrix_basis_equiv, e]
  rw [he, e.range_comp, Submodule.range_subtype]

/-- A normal matrix and an injective map determine a normalized basis of its image. -/
def ofToLin {K : Type*} [AddCommGroup K] (bK : Basis (Fin 2) ℤ K)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.antiTranspose.IsHermiteNormalForm)
    (hf : Function.Injective (Matrix.toLin bK bM A)) :
    InclusionNormalForm bM (LinearMap.range (Matrix.toLin bK bM A)) where
  basis := bK.map (LinearEquiv.ofInjective _ hf)
  isHermiteNormalForm := by
    convert hA using 1
    rw [LinearMap.toMatrix_map_left]
    exact congrArg Matrix.antiTranspose (LinearMap.toMatrix_toLin bK bM A)

@[simp]
theorem ofToLin_matrix {K : Type*} [AddCommGroup K] (bK : Basis (Fin 2) ℤ K)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.antiTranspose.IsHermiteNormalForm)
    (hf : Function.Injective (Matrix.toLin bK bM A)) :
    (ofToLin bK hA hf).matrix = A := by
  dsimp [matrix, ofToLin]
  rw [LinearMap.toMatrix_map_left]
  exact LinearMap.toMatrix_toLin bK bM A

/-- The index is the absolute determinant of the inclusion matrix. -/
theorem index_eq_natAbs_det (h : InclusionNormalForm bM N) :
    N.toAddSubgroup.index = h.matrix.det.natAbs := by
  exact Module.Basis.index_eq_natAbs_det_toMatrix bM N h.basis

/-- Positivity of the normal form removes the absolute value in the index formula. -/
theorem det_eq_index (h : InclusionNormalForm bM N) :
    h.matrix.det = N.toAddSubgroup.index := by
  rw [h.index_eq_natAbs_det, Int.natCast_natAbs, abs_of_pos h.det_pos]

/-- The quotient is cyclic precisely when the inclusion matrix has content one. -/
theorem quotient_isAddCyclic_iff_content_eq_one (h : InclusionNormalForm bM N) :
    IsAddCyclic (M ⧸ N) ↔ h.matrix.content = 1 :=
  Module.Basis.quotient_isAddCyclic_iff_content_toMatrix_eq_one bM N h.basis

/-- Row HNF uniqueness makes the normalized inclusion matrix canonical. -/
theorem matrix_eq (h h' : InclusionNormalForm bM N) : h.matrix = h'.matrix := by
  have hm : h.matrix * h.basis.toMatrix h'.basis = h'.matrix :=
    linearMap_toMatrix_mul_basis_toMatrix h'.basis h.basis bM N.subtype
  have hu : IsUnit (h.basis.toMatrix h'.basis).antiTranspose.det := by
    rw [Matrix.det_antiTranspose]
    exact Matrix.isUnit_det_of_right_inverse (h.basis.toMatrix_mul_toMatrix_flip h'.basis)
  have he := h.matrix_isHermiteNormalForm.eq_of_isUnit_det_mul_fin_two
    h'.matrix_isHermiteNormalForm
    (by simpa using h.det_ne_zero) hu
    (by rw [← Matrix.antiTranspose_mul, hm])
  simpa using congrArg Matrix.antiTranspose he

/-- The normalized generators themselves are canonical. -/
theorem basis_eq (h h' : InclusionNormalForm bM N) : h.basis = h'.basis := by
  apply DFunLike.ext
  intro j
  apply Subtype.ext
  apply bM.repr.injective
  ext i
  rw [h.repr_apply, h'.repr_apply, h.matrix_eq h']

end InclusionNormalForm

/-- Row-normalize in reversed ambient coordinates, then restore Cox's period order. -/
theorem exists_inclusionNormalForm {M : Type*} [AddCommGroup M]
    (bM : Basis (Fin 2) ℤ M) (N : Submodule ℤ M) (hN : Module.finrank ℤ N = 2) :
    Nonempty (InclusionNormalForm bM N) := by
  obtain ⟨bN, hbN⟩ :=
    N.exists_basis_isHermiteNormalForm (bM.reindex Fin.revPerm) hN
  refine ⟨⟨bN.reindex Fin.revPerm, ?_⟩⟩
  convert hbN using 1
  ext i j
  simp [Matrix.antiTranspose, LinearMap.toMatrix_apply, Basis.reindex_apply,
    Fin.revPerm]

/-- The unique normalized inclusion basis, chosen using row HNF existence. -/
def inclusionNormalForm {M : Type*} [AddCommGroup M]
    (bM : Basis (Fin 2) ℤ M) (N : Submodule ℤ M) (hN : Module.finrank ℤ N = 2) :
    InclusionNormalForm bM N :=
  Classical.choice (exists_inclusionNormalForm bM N hN)

end Cox
