/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
module

public import XYin.ForMathlib.LinearAlgebra.Matrix.HermiteNormalForm.Existence

import Mathlib.Data.Finset.Sort

/-!
# Uniqueness of the Hermite normal form

Two row equivalent integer matrices in Hermite normal form are equal. Hence the Hermite normal form
is a complete invariant of row equivalence over `ℤ`.

## Main results

* `Matrix.IsRowEchelon.eq_zero_of_vecMul_eq_zero`: the nonzero rows of a row echelon matrix are
  linearly independent, if the coefficients have no zero divisors.
* `Matrix.IsHermiteNormalForm.eq_of_rowEquivalent`: row equivalent matrices in Hermite normal form
  are equal.
* `Matrix.existsUnique_rowEquivalent_isHermiteNormalForm`: every integer matrix is row equivalent
  to a unique matrix in Hermite normal form.
* `Matrix.rowEquivalent_iff_hermiteNormalForm_H_eq`: two integer matrices are row equivalent if and
  only if they have the same Hermite normal form.

## Implementation notes

The proof of uniqueness is by induction on the number of columns. If `U * A = B` and `A` and `B`
agree on the first `l` columns, then `U - 1` vanishes on the rows of `A` which are nonzero on these
columns, since those rows are linearly independent. It follows that the last columns of `A` and `B`
differ by a multiple of the entry of `A` in the first row vanishing on the first `l` columns.

## Tags

matrix, echelon form, Hermite normal form, unimodular
-/

public section

namespace Matrix

variable {m n : Type*}

/-- If `x ᵥ* A = 0` for a row echelon matrix `A` whose coefficients have no zero divisors, then `x`
vanishes on the nonzero rows of `A`. In other words, the nonzero rows of `A` are linearly
independent. -/
theorem IsRowEchelon.eq_zero_of_vecMul_eq_zero {R : Type*} [Semiring R] [NoZeroDivisors R]
    [Fintype m] [LinearOrder m] [LT n] [WellFoundedLT n] {A : Matrix m n R} (hA : A.IsRowEchelon)
    {x : m → R} (hx : x ᵥ* A = 0) {i : m} (hi : A i ≠ 0) : x i = 0 := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    obtain ⟨c, hc⟩ := row_ne_zero_iff_exists_isLeadingEntry.1 hi
    have hsum : ∑ k, x k * A k c = 0 := congrFun hx c
    rw [Finset.sum_eq_single i] at hsum
    · exact (mul_eq_zero.1 hsum).resolve_right hc.2
    · intro k _ hk
      obtain hlt | hlt := hk.lt_or_gt
      · rw [ih k hlt fun h ↦ hi (hA.row_eq_zero_of_lt hlt h), zero_mul]
      · rw [hA hlt hc.1, mul_zero]
    · simp

section Fin

variable [LinearOrder m] {l : ℕ}

private theorem IsHermiteNormalForm.submatrix_castSucc {A : Matrix m (Fin (l + 1)) ℤ}
    (h : A.IsHermiteNormalForm) : (A.submatrix id Fin.castSucc).IsHermiteNormalForm := by
  have hzero {i : m} {j : Fin l} (hz : ∀ j₁ < j, A i j₁.castSucc = 0) :
      ∀ j₁ < j.castSucc, A i j₁ = 0 := fun j₁ hj₁ ↦ by
    induction j₁ using Fin.lastCases with
    | last => exact absurd hj₁ (not_lt.2 (Fin.le_last _))
    | cast j' => exact hz j' (Fin.castSucc_lt_castSucc_iff.1 hj₁)
  exact ⟨fun _ _ hlt _ hz ↦ h.isRowEchelon hlt (hzero hz), fun _ _ hc ↦ h.pos ⟨hzero hc.1, hc.2⟩,
    fun _ _ _ hlt hc ↦ h.mem_Ico hlt ⟨hzero hc.1, hc.2⟩⟩

omit [LinearOrder m] in
/-- If a row vanishes on the first `l` columns, then it vanishes to the left of the last column. -/
private theorem forall_lt_last {X : Matrix m (Fin (l + 1)) ℤ} {i : m}
    (hs : ∀ j : Fin l, X i j.castSucc = 0) : ∀ j < Fin.last l, X i j = 0 := fun j hj ↦ by
  induction j using Fin.lastCases with
  | last => exact absurd hj (lt_irrefl _)
  | cast j' => exact hs j'

/-- The last entry of any row of `X` vanishing on the first `l` columns is divisible by the last
entry of the first such row `i₀`. -/
private theorem dvd_last_of_forall_le {X : Matrix m (Fin (l + 1)) ℤ} (hX : X.IsRowEchelon) {i₀ : m}
    (hi₀ : ∀ j : Fin l, X i₀ j.castSucc = 0)
    (hmin : ∀ k, (∀ j : Fin l, X k j.castSucc = 0) → i₀ ≤ k)
    (k : m) (hk : ∀ j : Fin l, X k j.castSucc = 0) : X i₀ (Fin.last l) ∣ X k (Fin.last l) := by
  obtain rfl | hne := eq_or_ne k i₀
  · exact dvd_rfl
  · rw [hX (lt_of_le_of_ne (hmin k hk) hne.symm) (forall_lt_last hi₀)]
    exact dvd_zero _

/-- The last entry of a row of `X` vanishing on the first `l` columns is nonnegative. -/
private theorem IsHermiteNormalForm.nonneg_last {X : Matrix m (Fin (l + 1)) ℤ}
    (hX : X.IsHermiteNormalForm) {i : m} (hs : ∀ j : Fin l, X i j.castSucc = 0) :
    0 ≤ X i (Fin.last l) := by
  by_cases hc : X i (Fin.last l) = 0
  · exact hc.ge
  · exact (hX.pos ⟨forall_lt_last hs, hc⟩).le

variable [Fintype m]

/-- Suppose `U * A = B`, where `A` and `B` agree on the first `l` columns and `A` is in row echelon
form. If `g` divides the last entry of each row of `A` vanishing on the first `l` columns, then `g`
divides the difference of the last columns of `A` and `B`. -/
private theorem dvd_sub_last {A B : Matrix m (Fin (l + 1)) ℤ}
    (hA : (A.submatrix id Fin.castSucc).IsRowEchelon) (U : GL m ℤ) (hU : U • A = B)
    (hsub : A.submatrix id Fin.castSucc = B.submatrix id Fin.castSucc) {g : ℤ}
    (hg : ∀ k, (∀ j : Fin l, A k j.castSucc = 0) → g ∣ A k (Fin.last l)) (i : m) :
    g ∣ B i (Fin.last l) - A i (Fin.last l) := by
  let W : Matrix m m ℤ := (U : Matrix m m ℤ) - 1
  have hW : W * A = B - A := by
    rw [Matrix.sub_mul, Matrix.one_mul, ← hU]
    rfl
  have hx : W i ᵥ* A.submatrix id Fin.castSucc = 0 := by
    ext j
    have h := congrFun₂ hW i j.castSucc
    have h' := congrFun₂ hsub i j
    simp only [Matrix.mul_apply, Matrix.sub_apply, submatrix_apply, id] at h h'
    simp only [vecMul, dotProduct, submatrix_apply, id, Pi.zero_apply]
    rw [h, ← h', sub_self]
  have hsum : B i (Fin.last l) - A i (Fin.last l) = ∑ k, W i k * A k (Fin.last l) := by
    rw [← Matrix.sub_apply, ← hW, Matrix.mul_apply]
  rw [hsum]
  refine Finset.dvd_sum fun k _ ↦ ?_
  by_cases hk : ∀ j : Fin l, A k j.castSucc = 0
  · exact (hg k hk).mul_left _
  · have hne : (A.submatrix id Fin.castSucc) k ≠ 0 := fun h ↦ hk fun j ↦ congrFun h j
    rw [hA.eq_zero_of_vecMul_eq_zero hx hne, zero_mul]
    exact dvd_zero _

private theorem IsHermiteNormalForm.eq_of_smul_fin {A B : Matrix m (Fin l) ℤ}
    (hA : A.IsHermiteNormalForm) (hB : B.IsHermiteNormalForm) (U : GL m ℤ) (hU : U • A = B) :
    A = B := by
  induction l with
  | zero =>
    ext _ j
    exact j.elim0
  | succ l ih =>
    have hA' := hA.submatrix_castSucc
    have hB' := hB.submatrix_castSucc
    have hsub : A.submatrix id Fin.castSucc = B.submatrix id Fin.castSucc := by
      refine ih hA' hB' ?_
      ext i j
      simpa [Matrix.mul_apply] using congrFun₂ hU i j.castSucc
    have hUinv : U⁻¹ • B = A := by rw [← hU, inv_smul_smul]
    have hsame {k : m} (j : Fin l) : A k j.castSucc = B k j.castSucc := congrFun₂ hsub k j
    suffices hlast : ∀ i, A i (Fin.last l) = B i (Fin.last l) by
      ext i j
      induction j using Fin.lastCases with
      | last => exact hlast i
      | cast j => exact hsame j
    let S : Finset m := {i | ∀ j : Fin l, A i j.castSucc = 0}
    have hS {i : m} : i ∈ S ↔ ∀ j : Fin l, A i j.castSucc = 0 := by simp [S]
    obtain hemp | hne := S.eq_empty_or_nonempty
    · intro i
      have hd := dvd_sub_last hA'.isRowEchelon U hU hsub (g := 0)
        (fun k hk ↦ by simpa [hemp] using hS.2 hk) i
      rw [zero_dvd_iff, sub_eq_zero] at hd
      exact hd.symm
    let i₀ := S.min' hne
    have hi₀ : ∀ j : Fin l, A i₀ j.castSucc = 0 := hS.1 (S.min'_mem hne)
    have hi₀' : ∀ j : Fin l, B i₀ j.castSucc = 0 := fun j ↦ hsame j ▸ hi₀ j
    have hminA (k : m) (hk : ∀ j : Fin l, A k j.castSucc = 0) : i₀ ≤ k := S.min'_le _ (hS.2 hk)
    have hminB (k : m) (hk : ∀ j : Fin l, B k j.castSucc = 0) : i₀ ≤ k :=
      hminA k fun j ↦ (hsame j).trans (hk j)
    have hdA := dvd_sub_last hA'.isRowEchelon U hU hsub
      (dvd_last_of_forall_le hA.isRowEchelon hi₀ hminA)
    have hdB := dvd_sub_last hB'.isRowEchelon U⁻¹ hUinv hsub.symm
      (dvd_last_of_forall_le hB.isRowEchelon hi₀' hminB)
    have hab : A i₀ (Fin.last l) = B i₀ (Fin.last l) :=
      Int.dvd_antisymm (hA.nonneg_last hi₀) (hB.nonneg_last hi₀') ((dvd_sub_self_right).1 (hdA i₀))
        ((dvd_sub_self_right).1 (hdB i₀))
    intro i
    obtain hlt | rfl | hlt := lt_trichotomy i i₀
    · have hd := hdA i
      by_cases hc : A i₀ (Fin.last l) = 0
      · rw [hc, zero_dvd_iff, sub_eq_zero] at hd
        exact hd.symm
      · have h₁ := hA.mem_Ico hlt ⟨forall_lt_last hi₀, hc⟩
        have h₂ := hB.mem_Ico hlt ⟨forall_lt_last hi₀', hab ▸ hc⟩
        rw [← hab] at h₂
        have hx := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.2 ⟨by grind, by grind⟩)
        grind
    · exact hab
    · rw [hA.isRowEchelon hlt (forall_lt_last hi₀), hB.isRowEchelon hlt (forall_lt_last hi₀')]

end Fin

variable [Fintype m] [LinearOrder m] [Finite n] [LinearOrder n]

/-- Two row equivalent integer matrices in Hermite normal form are equal. -/
theorem IsHermiteNormalForm.eq_of_rowEquivalent {A B : Matrix m n ℤ} (hA : A.IsHermiteNormalForm)
    (hB : B.IsHermiteNormalForm) (h : RowEquivalent A B) : A = B := by
  cases nonempty_fintype n
  obtain ⟨U, rfl⟩ := h
  let e := Fintype.orderIsoFinOfCardEq n rfl
  have hsub := (hA.submatrix_orderIso (OrderIso.refl m) e).eq_of_smul_fin
    (hB.submatrix_orderIso (OrderIso.refl m) e) U (by ext i j; simp [Matrix.mul_apply])
  ext i j
  simpa using congrFun₂ hsub i (e.symm j)

/-- Every integer matrix is row equivalent to a unique matrix in Hermite normal form. -/
theorem existsUnique_rowEquivalent_isHermiteNormalForm (A : Matrix m n ℤ) :
    ∃! H, RowEquivalent A H ∧ H.IsHermiteNormalForm := by
  obtain ⟨H, hAH, hH⟩ := exists_rowEquivalent_isHermiteNormalForm A
  exact ⟨H, ⟨hAH, hH⟩, fun H' ⟨hAH', hH'⟩ ↦ hH'.eq_of_rowEquivalent hH (hAH'.symm.trans hAH)⟩

/-- Any two Hermite normal forms of a matrix have the same matrix `H`. -/
theorem HermiteNormalForm.H_unique {A : Matrix m n ℤ} (h₁ h₂ : A.HermiteNormalForm) :
    h₁.H = h₂.H :=
  h₁.isHermiteNormalForm.eq_of_rowEquivalent h₂.isHermiteNormalForm
    (h₁.rowEquivalent.symm.trans h₂.rowEquivalent)

/-- A matrix in Hermite normal form is equal to its Hermite normal form. -/
theorem IsHermiteNormalForm.hermiteNormalForm_H {A : Matrix m n ℤ} (hA : A.IsHermiteNormalForm) :
    A.hermiteNormalForm.H = A :=
  HermiteNormalForm.H_unique _ hA.hermiteNormalForm

/-- Two integer matrices are row equivalent if and only if they have the same Hermite normal
form. -/
theorem rowEquivalent_iff_hermiteNormalForm_H_eq {A B : Matrix m n ℤ} :
    RowEquivalent A B ↔ A.hermiteNormalForm.H = B.hermiteNormalForm.H := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact A.hermiteNormalForm.isHermiteNormalForm.eq_of_rowEquivalent
      B.hermiteNormalForm.isHermiteNormalForm
      (A.hermiteNormalForm.rowEquivalent.symm.trans (h.trans B.hermiteNormalForm.rowEquivalent))
  · exact A.hermiteNormalForm.rowEquivalent.trans
      (h ▸ B.hermiteNormalForm.rowEquivalent.symm)

end Matrix
