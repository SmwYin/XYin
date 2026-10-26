/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.HermiteNormalForm.HermiteNormalForm

/-!
# Tests for integer Hermite normal forms

These examples exercise rectangular and empty shapes, canonical remainder conventions,
the distinction from RREF, and a unimodular reduction preserving an integer row lattice.
-/

namespace HermiteNormalFormTests

open Matrix

-- Negative entries are allowed in nonpivot columns, and zero rows are allowed at the bottom.
private def rectangular : Matrix (Fin 3) (Fin 4) ℤ :=
  !![2, -3, 1, 7; 0, 0, 4, -5; 0, 0, 0, 0]

private theorem rectangular_hnf : rectangular.IsHermiteNormalForm := by decide

example : rectangular.rank = 2 := by
  rw [rectangular_hnf.rank_eq_card_nonzero_rows]
  change Nat.card {i : Fin 3 // (fun j : Fin 4 ↦ rectangular i j) ≠ 0} = 2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

example : rectangular.IsPivotedBy ![↑(0 : Fin 4), ↑(2 : Fin 4), ⊤] := by
  refine ⟨rectangular_hnf.isRowEchelon, ?_⟩
  norm_num [Fin.forall_fin_succ, rectangular]

-- Negative pivots, unreduced entries, and misplaced zero rows are rejected.
example : ¬ (!![-2, 1; 0, 3] : Matrix (Fin 2) (Fin 2) ℤ).IsHermiteNormalForm := by
  decide

example : ¬ (!![2, 3; 0, 3] : Matrix (Fin 2) (Fin 2) ℤ).IsHermiteNormalForm := by
  decide

example : ¬ (!![2, -1; 0, 3] : Matrix (Fin 2) (Fin 2) ℤ).IsHermiteNormalForm := by
  decide

example : ¬ (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).IsHermiteNormalForm := by
  decide

example : ¬ (!![0, 2; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).IsHermiteNormalForm := by
  decide

-- Both kinds of empty rectangular matrix satisfy the definition.
example (A : Matrix (Fin 0) (Fin 4) ℤ) : A.IsHermiteNormalForm := by
  have hA : A = 0 := Subsingleton.elim _ _
  rw [hA]
  exact isHermiteNormalForm_zero

example (A : Matrix (Fin 3) (Fin 0) ℤ) : A.IsHermiteNormalForm := by
  have hA : A = 0 := Subsingleton.elim _ _
  rw [hA]
  exact isHermiteNormalForm_zero

-- RREF permits arbitrary nonpivot columns, but requires all pivots to be one.
example : (!![1, -3, 0, 7; 0, 0, 1, -5; 0, 0, 0, 0] :
    Matrix (Fin 3) (Fin 4) ℤ).IsReducedRowEchelon := by
  apply IsHermiteNormalForm.isReducedRowEchelon
  · decide
  · norm_num [IsLeadingEntry, Fin.forall_fin_succ]

private def input : Matrix (Fin 2) (Fin 2) ℤ := !![2, 3; 1, 4]
private def transform : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 2]
private def normal : Matrix (Fin 2) (Fin 2) ℤ := !![1, 4; 0, 5]

example : ¬ input.IsHermiteNormalForm := by decide

private theorem normal_hnf : normal.IsHermiteNormalForm := by decide

example : ¬ normal.IsReducedRowEchelon := by
  intro h
  have hp : normal.IsLeadingEntry 1 1 := by decide
  have hunit := h.eq_one hp
  norm_num [normal] at hunit

private theorem sample_rowEquivalent : RowEquivalent input normal := by
  refine rowEquivalent_iff_exists_isUnit_det.mpr ⟨transform, ?_, ?_⟩
  · norm_num [transform, Matrix.det_fin_two]
  · decide

-- The row span is over ℤ, so this asserts equality of lattices, not merely rational spans.
example : Submodule.span ℤ (Set.range input) = Submodule.span ℤ (Set.range normal) :=
  sample_rowEquivalent.span_row_eq

example : ∃ w : Fin 2 → ℤ, w ᵥ* normal = ![3, 7] := by
  apply (sample_rowEquivalent.exists_vecMul_eq_iff ![3, 7]).mp
  exact ⟨![1, 1], by decide⟩

example : input.rank = 2 := by
  rw [sample_rowEquivalent.rank_eq, normal_hnf.rank_eq_card_nonzero_rows]
  change Nat.card {i : Fin 2 // (fun j : Fin 2 ↦ normal i j) ≠ 0} = 2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

example : input.det.natAbs = normal.det.natAbs := sample_rowEquivalent.natAbs_det_eq

-- The abstract uniqueness theorem identifies the computed representative.
example (K : Matrix (Fin 2) (Fin 2) ℤ) (hK : K.IsHermiteNormalForm)
    (hAK : RowEquivalent input K) : K = normal := by
  obtain ⟨H, hH, huniq⟩ := existsUnique_rowEquivalent_isHermiteNormalForm_fin_two input
    (by norm_num [input, Matrix.det_fin_two])
  exact (huniq K ⟨hK, hAK⟩).trans (huniq normal ⟨normal_hnf, sample_rowEquivalent⟩).symm

-- Negative determinant requires an orientation-reversing unimodular row operation.
example (K : Matrix (Fin 2) (Fin 2) ℤ) (hK : K.IsHermiteNormalForm)
    (hAK : RowEquivalent !![-2, -3; 1, 4] K) : K = normal := by
  have hAN : RowEquivalent !![-2, -3; 1, 4] normal := by
    refine rowEquivalent_iff_exists_isUnit_det.mpr ⟨!![0, 1; 1, 2], ?_, ?_⟩
    · norm_num [det_fin_two]
    · decide
  exact hK.eq_of_rowEquivalent_fin_two normal_hnf
    (hAK.det_ne_zero_iff.mp (by norm_num [det_fin_two])) (hAK.symm.trans hAN)

-- The first entry may be zero: Bézout reduction still finds a positive first pivot.
example : ∃ U : Matrix (Fin 2) (Fin 2) ℤ,
    IsUnit U.det ∧ (U * !![0, 2; 3, 1]).IsHermiteNormalForm :=
  exists_isUnit_det_mul_isHermiteNormalForm_fin_two _ (by norm_num [det_fin_two])

-- Content is defined on rectangular matrices, independently of normal-form conditions.
example : (!![6, -10, 14; 0, 22, 4] : Matrix (Fin 2) (Fin 3) ℤ).content = 2 := by
  decide

example : input.content = normal.content := by
  have hm : transform * input = normal := by decide
  rw [← hm, content_isUnit_det_mul (show IsUnit transform.det by
    norm_num [transform, det_fin_two])]

-- Cyclicity concerns the inclusion, regardless of whether its chosen matrix is in HNF.
example {M : Type*} [AddCommGroup M] (bM : Module.Basis (Fin 2) ℤ M)
    (N : Submodule ℤ M) (bN : Module.Basis (Fin 2) ℤ N)
    (h : LinearMap.toMatrix bN bM N.subtype = !![2, 1; 0, 2]) : IsAddCyclic (M ⧸ N) := by
  rw [Module.Basis.quotient_isAddCyclic_iff_content_toMatrix_eq_one bM N bN, h]
  norm_num [content_fin_two]

example {M : Type*} [AddCommGroup M] (bM : Module.Basis (Fin 2) ℤ M)
    (N : Submodule ℤ M) (bN : Module.Basis (Fin 2) ℤ N)
    (h : LinearMap.toMatrix bN bM N.subtype = !![2, 0; 0, 2]) : ¬IsAddCyclic (M ⧸ N) := by
  rw [Module.Basis.quotient_isAddCyclic_iff_content_toMatrix_eq_one bM N bN, h]
  norm_num [content_fin_two]

end HermiteNormalFormTests
