/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.HermiteNormalForm.Pivot
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import XYin.PhD.HermiteNormalForm.RowEquivalence

/-!
# Rank-two Hermite normal form

Nonsingular two-by-two integer matrices admit a unique row Hermite normal form.
The construction uses Bézout coefficients to clear the first column, a row sign change
to make the second pivot positive, and Euclidean division to reduce the remaining entry.
All transformations act on rows directly.
-/

open MatrixGroups

namespace Matrix

/-- The full-rank row HNF shape in rank two; the upper-right entry is reduced modulo the
lower-right pivot. -/
theorem isHermiteNormalForm_fin_two {a b d : ℤ} (ha : 0 < a) (hd : 0 < d)
    (hb0 : 0 ≤ b) (hbd : b < d) :
    IsHermiteNormalForm !![a, b; 0, d] := by
  apply isHermiteNormalForm_of_isUpperTriangular
  · intro i j hji
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i <;> assumption
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- A nonsingular rank-two matrix is in row HNF exactly when it has the usual positive
upper-triangular shape and its upper-right entry is reduced modulo the lower-right pivot. -/
theorem isHermiteNormalForm_fin_two_iff {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : A.det ≠ 0) :
    A.IsHermiteNormalForm ↔
      A 1 0 = 0 ∧ 0 < A 0 0 ∧ 0 < A 1 1 ∧ A 0 1 ∈ Set.Ico 0 (A 1 1) := by
  constructor
  · intro hA
    exact ⟨hA.isUpperTriangular (by decide), hA.diagonal_pos hdet 0,
      hA.diagonal_pos hdet 1,
      hA.reduced (by decide) (hA.isRowEchelon.isLeadingEntry_diag hdet 1)⟩
  · rintro ⟨h10, ha, hd, hb⟩
    have hshape : A = !![A 0 0, A 0 1; 0, A 1 1] := by
      conv_lhs => rw [Matrix.eta_fin_two A, h10]
    rw [hshape]
    exact isHermiteNormalForm_fin_two ha hd hb.1 hb.2

/-- Bézout row operations put a nonsingular rank-two matrix in upper-triangular form,
with a positive first diagonal entry, using a determinant-one matrix. -/
theorem exists_det_one_mul_upperTriangular_fin_two
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det ≠ 0) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℤ,
      U.det = 1 ∧ (U * A) 1 0 = 0 ∧ 0 < (U * A) 0 0 := by
  let g : ℤ := Int.gcd (A 0 0) (A 1 0)
  have hg : 0 < g := by
    have hn : Int.gcd (A 0 0) (A 1 0) ≠ 0 := by
      intro h
      obtain ⟨h00, h10⟩ := Int.gcd_eq_zero_iff.mp h
      exact hdet (by simp [det_fin_two, h00, h10])
    dsimp [g]
    exact_mod_cast Nat.pos_of_ne_zero hn
  obtain ⟨a, ha⟩ := Int.gcd_dvd_left (A 0 0) (A 1 0)
  obtain ⟨c, hc⟩ := Int.gcd_dvd_right (A 0 0) (A 1 0)
  change A 0 0 = g * a at ha
  change A 1 0 = g * c at hc
  let p := Int.gcdA (A 0 0) (A 1 0)
  let q := Int.gcdB (A 0 0) (A 1 0)
  have hbez : A 0 0 * p + A 1 0 * q = g := (Int.gcd_eq_gcd_ab ..).symm
  have hunit : p * a + q * c = 1 := by
    apply mul_left_cancel₀ (ne_of_gt hg)
    calc
      g * (p * a + q * c) = A 0 0 * p + A 1 0 * q := by rw [ha, hc]; ring
      _ = g * 1 := by rw [hbez, mul_one]
  refine ⟨!![p, q; -c, a], ?_, ?_, ?_⟩
  · simpa only [det_fin_two, of_apply, cons_val_zero, cons_val_one, cons_val_fin_one,
      mul_neg, sub_neg_eq_add] using hunit
  · simp only [mul_apply, Fin.sum_univ_two, of_apply, cons_val_zero, cons_val_one,
      cons_val_fin_one]
    rw [ha, hc]
    ring
  · simpa only [mul_apply, Fin.sum_univ_two, of_apply, cons_val_zero, cons_val_one,
      cons_val_fin_one, mul_comm p, mul_comm q, hbez] using hg

/-- One row subtraction reduces the upper-right entry of a positive upper-triangular
rank-two matrix to the interval required for row Hermite normal form. -/
theorem isHermiteNormalForm_reduce_fin_two {a b d : ℤ} (ha : 0 < a) (hd : 0 < d) :
    (!![1, -(b / d); 0, 1] * !![a, b; 0, d]).IsHermiteNormalForm := by
  have hmul : !![1, -(b / d); 0, 1] * !![a, b; 0, d] = !![a, b % d; 0, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, Int.emod_def, mul_comm, sub_eq_add_neg]
  rw [hmul]
  exact isHermiteNormalForm_fin_two ha hd (Int.emod_nonneg _ (ne_of_gt hd))
    (Int.emod_lt_of_pos _ hd)

/-- A nonzero second diagonal entry can be made positive, and the other entry in its
column can be reduced, using unimodular row operations. -/
theorem exists_isUnit_det_mul_isHermiteNormalForm_upperTriangular_fin_two
    {a b d : ℤ} (ha : 0 < a) (hd : d ≠ 0) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit U.det ∧ (U * !![a, b; 0, d]).IsHermiteNormalForm := by
  obtain ⟨s, hs, hsd⟩ : ∃ s : ℤ, IsUnit s ∧ 0 < s * d := by
    rcases lt_or_gt_of_ne hd with hd | hd
    · exact ⟨-1, isUnit_neg_one, by simpa using neg_pos.mpr hd⟩
    · exact ⟨1, isUnit_one, by simpa using hd⟩
  let U : Matrix (Fin 2) (Fin 2) ℤ := !![1, -(b / (s * d)) * s; 0, s]
  have hmul : U * !![a, b; 0, d] = !![a, b % (s * d); 0, s * d] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, mul_apply, Fin.sum_univ_two, Int.emod_def]
    ring
  refine ⟨U, ?_, ?_⟩
  · simpa [U, det_fin_two] using hs
  · rw [hmul]
    exact isHermiteNormalForm_fin_two ha hsd (Int.emod_nonneg _ (ne_of_gt hsd))
      (Int.emod_lt_of_pos _ hsd)

/-- A nonsingular rank-two integer matrix admits row HNF by unimodular left multiplication. -/
theorem exists_isUnit_det_mul_isHermiteNormalForm_fin_two
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det ≠ 0) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℤ, IsUnit U.det ∧ (U * A).IsHermiteNormalForm := by
  obtain ⟨U, hU, h10, h00⟩ := exists_det_one_mul_upperTriangular_fin_two A hdet
  have h11 : (U * A) 1 1 ≠ 0 := by
    intro h
    apply hdet
    have hdetUA : (U * A).det = 0 := by rw [det_fin_two, h10, h]; simp
    simpa [det_mul, hU] using hdetUA
  have hshape : U * A = !![(U * A) 0 0, (U * A) 0 1; 0, (U * A) 1 1] := by
    conv_lhs => rw [eta_fin_two (U * A), h10]
  obtain ⟨V, hV, hH⟩ :=
    exists_isUnit_det_mul_isHermiteNormalForm_upperTriangular_fin_two h00 h11
  refine ⟨V * U, by simpa [det_mul, hU] using hV, ?_⟩
  rw [mul_assoc, hshape]
  exact hH

/-- A positive-determinant rank-two matrix can be reduced using determinant-one row operations. -/
theorem exists_SL2_mul_isHermiteNormalForm
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : 0 < A.det) :
    ∃ U : SL(2, ℤ), (U.1 * A).IsHermiteNormalForm := by
  obtain ⟨U, hU, hH⟩ := exists_isUnit_det_mul_isHermiteNormalForm_fin_two A (ne_of_gt hdet)
  have hpos : 0 < (U * A).det := hH.det_pos (by
    rw [det_mul]
    exact mul_ne_zero hU.ne_zero (ne_of_gt hdet))
  have hU1 : U.det = 1 := by
    rcases Int.isUnit_iff.mp hU with h | h
    · exact h
    · rw [det_mul, h, neg_one_mul] at hpos
      omega
  exact ⟨⟨U, hU1⟩, hH⟩

/-- Nonsingular rank-two row HNF is unchanged by a unimodular change of rows that remains
in row HNF. -/
theorem IsHermiteNormalForm.eq_of_isUnit_det_mul_fin_two
    {A B U : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.IsHermiteNormalForm)
    (hB : B.IsHermiteNormalForm) (hdet : A.det ≠ 0) (hU : IsUnit U.det)
    (hmul : U * A = B) : A = B := by
  have hdetB : B.det ≠ 0 := by
    rw [← hmul, det_mul]
    exact mul_ne_zero hU.ne_zero hdet
  obtain ⟨hA10, hA00, hA11, hA01⟩ := (isHermiteNormalForm_fin_two_iff hdet).mp hA
  obtain ⟨hB10, hB00, hB11, hB01⟩ := (isHermiteNormalForm_fin_two_iff hdetB).mp hB
  have hU10 : U 1 0 = 0 := by
    have h := congrArg (fun M ↦ M 1 0) hmul
    simp only [mul_apply, Fin.sum_univ_two, hA10, hB10, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (ne_of_gt hA00)
  have hdiag : IsUnit (U 0 0 * U 1 1) := by
    simpa only [det_fin_two, hU10, mul_zero, sub_zero] using hU
  have h00 := congrArg (fun M ↦ M 0 0) hmul
  have h11 := congrArg (fun M ↦ M 1 1) hmul
  simp only [mul_apply, Fin.sum_univ_two, hA10, mul_zero, add_zero] at h00
  simp only [mul_apply, Fin.sum_univ_two, hU10, zero_mul, zero_add] at h11
  have hU00 : U 0 0 = 1 := by
    rcases Int.isUnit_iff.mp (isUnit_of_mul_isUnit_left hdiag) with h | h
    · exact h
    · rw [h, neg_one_mul] at h00
      omega
  have hU11 : U 1 1 = 1 := by
    rcases Int.isUnit_iff.mp (isUnit_of_mul_isUnit_right hdiag) with h | h
    · exact h
    · rw [h, neg_one_mul] at h11
      omega
  simp only [hU00, one_mul] at h00
  simp only [hU11, one_mul] at h11
  have h01 := congrArg (fun M ↦ M 0 1) hmul
  simp only [mul_apply, Fin.sum_univ_two, hU00, one_mul] at h01
  have hentry : A 0 1 = B 0 1 := by
    calc
      A 0 1 = A 0 1 % A 1 1 := (Int.emod_eq_of_lt hA01.1 hA01.2).symm
      _ = B 0 1 % A 1 1 := by rw [← h01]; simp
      _ = B 0 1 := by rw [h11]; exact Int.emod_eq_of_lt hB01.1 hB01.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

/-- Two nonsingular rank-two row HNFs in the same row-equivalence class are equal. -/
theorem IsHermiteNormalForm.eq_of_rowEquivalent_fin_two
    {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.IsHermiteNormalForm)
    (hB : B.IsHermiteNormalForm) (hdet : A.det ≠ 0) (hAB : RowEquivalent A B) : A = B := by
  obtain ⟨U, hU, hmul⟩ := rowEquivalent_iff_exists_isUnit_det.mp hAB
  exact hA.eq_of_isUnit_det_mul_fin_two hB hdet hU hmul

/-- Every nonsingular rank-two integer matrix is row-equivalent to a unique row HNF. -/
theorem existsUnique_rowEquivalent_isHermiteNormalForm_fin_two
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det ≠ 0) :
    ∃! H : Matrix (Fin 2) (Fin 2) ℤ, H.IsHermiteNormalForm ∧ RowEquivalent A H := by
  obtain ⟨U, hU, hH⟩ := exists_isUnit_det_mul_isHermiteNormalForm_fin_two A hdet
  have hAH : RowEquivalent A (U * A) :=
    rowEquivalent_iff_exists_isUnit_det.mpr ⟨U, hU, rfl⟩
  refine ⟨U * A, ⟨hH, hAH⟩, ?_⟩
  rintro B ⟨hB, hAB⟩
  apply Eq.symm
  apply hH.eq_of_rowEquivalent_fin_two hB
  · rw [det_mul]
    exact mul_ne_zero hU.ne_zero hdet
  · exact hAH.symm.trans hAB

end Matrix
