/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic

/-!
# Hermite normal form of integer matrices

This file defines the row-style Hermite normal form of a rectangular integer matrix: the integer
analogue of reduced row echelon form, where row operations are restricted to those invertible
over `ℤ`.

## Main definitions

* `Matrix.IsHermiteNormalForm`: the predicate that an integer matrix is in Hermite normal form.
  It is in row echelon form, its leading entries are positive, and the entries above a leading
  entry are nonnegative and strictly smaller than it.

## References

* <https://en.wikipedia.org/wiki/Hermite_normal_form>

## Tags

matrix, echelon form, Hermite normal form
-/

@[expose] public section

namespace Matrix

variable {m n : Type*}

/-- An integer matrix is in (row) Hermite normal form if it is in row echelon form, its leading
entries are positive, and each entry above a leading entry is nonnegative and strictly smaller
than that leading entry. -/
@[mk_iff isHermiteNormalForm_iff]
structure IsHermiteNormalForm [LT m] [LT n] (A : Matrix m n ℤ) : Prop where
  isRowEchelon : A.IsRowEchelon
  pos ⦃i : m⦄ ⦃c : n⦄ (hA : A.IsLeadingEntry i c) : 0 < A i c
  mem_Ico ⦃i₁ i₂ : m⦄ ⦃c : n⦄ (hlt : i₁ < i₂) (hA : A.IsLeadingEntry i₂ c) :
    A i₁ c ∈ Set.Ico 0 (A i₂ c)

section LT

variable [LT m] [LT n] {A : Matrix m n ℤ}

@[simp]
theorem isHermiteNormalForm_zero : (0 : Matrix m n ℤ).IsHermiteNormalForm where
  isRowEchelon _ _ _ _ _ := rfl
  pos _ _ h := (h.2 rfl).elim
  mem_Ico _ _ _ _ h := (h.2 rfl).elim

/-- An integer matrix in reduced row echelon form is in Hermite normal form. -/
theorem IsReducedRowEchelon.isHermiteNormalForm (h : A.IsReducedRowEchelon) :
    A.IsHermiteNormalForm where
  isRowEchelon := h.isRowEchelon
  pos i c hc := by simp [h.eq_one hc]
  mem_Ico i₁ i₂ c hlt hc := by simp [h.eq_zero hlt hc, h.eq_one hc]

/-- An integer matrix is in reduced row echelon form if and only if it is in Hermite normal form
and all of its leading entries are `1`. -/
theorem isReducedRowEchelon_iff_isHermiteNormalForm :
    A.IsReducedRowEchelon ↔
      A.IsHermiteNormalForm ∧ ∀ ⦃i c⦄, A.IsLeadingEntry i c → A i c = 1 := by
  refine ⟨fun h ↦ ⟨h.isHermiteNormalForm, fun _ _ hc ↦ h.eq_one hc⟩, fun ⟨h, hp⟩ ↦ ?_⟩
  refine ⟨h.isRowEchelon, hp, fun i₁ i₂ c hlt hc ↦ ?_⟩
  have := h.mem_Ico hlt hc
  rw [hp hc] at this
  grind

end LT

section LinearOrder

variable [LinearOrder m] [LT n] {A : Matrix m n ℤ}

/-- Every entry of a pivot column of a Hermite normal form is nonnegative. -/
theorem IsHermiteNormalForm.nonneg_of_isLeadingEntry {i : m} {c : n}
    (h : A.IsHermiteNormalForm) (hc : A.IsLeadingEntry i c) (k : m) : 0 ≤ A k c := by
  rcases lt_trichotomy k i with hlt | rfl | hlt
  · exact (h.mem_Ico hlt hc).1
  · exact (h.pos hc).le
  · exact (h.isRowEchelon hlt hc.1).ge

/-- In a pivot column of a Hermite normal form, every entry other than the pivot is nonnegative
and strictly smaller than the pivot. -/
theorem IsHermiteNormalForm.mem_Ico_of_ne_of_isLeadingEntry {i k : m} {c : n}
    (h : A.IsHermiteNormalForm) (hne : k ≠ i) (hc : A.IsLeadingEntry i c) :
    A k c ∈ Set.Ico 0 (A i c) := by
  rcases hne.lt_or_gt with hlt | hlt
  · exact h.mem_Ico hlt hc
  · rw [h.isRowEchelon hlt hc.1]
    exact ⟨le_rfl, h.pos hc⟩

end LinearOrder

section Reindex

variable {m' n' : Type*} [Preorder m] [Preorder n] [Preorder m'] [Preorder n'] {A : Matrix m n ℤ}

theorem isLeadingEntry_submatrix_orderIso (f : m' ≃o m) (e : n' ≃o n) {i : m'} {c : n'} :
    (A.submatrix f e).IsLeadingEntry i c ↔ A.IsLeadingEntry (f i) (e c) := by
  refine and_congr_left' ⟨fun h j hj ↦ ?_, fun h j hj ↦ h _ (e.lt_iff_lt.2 hj)⟩
  simpa using h (e.symm j) (e.symm_apply_apply c ▸ e.symm.lt_iff_lt.2 hj)

/-- Hermite normal form is preserved by reindexing rows and columns along order isomorphisms. -/
theorem IsHermiteNormalForm.submatrix_orderIso (h : A.IsHermiteNormalForm) (f : m' ≃o m)
    (e : n' ≃o n) : (A.submatrix f e).IsHermiteNormalForm where
  isRowEchelon i₁ i₂ hlt j₂ hz := h.isRowEchelon (f.lt_iff_lt.2 hlt) fun j hj ↦ by
    simpa using hz (e.symm j) (e.symm_apply_apply j₂ ▸ e.symm.lt_iff_lt.2 hj)
  pos _ _ hc := h.pos ((isLeadingEntry_submatrix_orderIso f e).1 hc)
  mem_Ico _ _ _ hlt hc :=
    h.mem_Ico (f.lt_iff_lt.2 hlt) ((isLeadingEntry_submatrix_orderIso f e).1 hc)

end Reindex

section Square

variable [LinearOrder n] {A : Matrix n n ℤ}

/-- An upper triangular matrix with positive diagonal is in Hermite normal form if each entry above
the diagonal is nonnegative and strictly smaller than the diagonal entry of its column. -/
theorem isHermiteNormalForm_of_isUpperTriangular (ht : A.IsUpperTriangular)
    (hp : ∀ i, 0 < A i i) (hr : ∀ ⦃i j⦄, i < j → A i j ∈ Set.Ico 0 (A j j)) :
    A.IsHermiteNormalForm := by
  have hlead (i : n) : A.IsLeadingEntry i i := ⟨fun _ hj ↦ ht hj, (hp i).ne'⟩
  refine ⟨fun i₁ i₂ hi j hz ↦ ?_, fun i c hc ↦ ?_, fun i₁ i₂ c hi hc ↦ ?_⟩
  · exact ht ((le_of_not_gt fun hlt ↦ (hp i₁).ne' (hz i₁ hlt)).trans_lt hi)
  · obtain rfl := hc.unique (hlead i)
    exact hp _
  · obtain rfl := hc.unique (hlead i₂)
    exact hr hi

/-- A diagonal matrix with positive diagonal entries is in Hermite normal form. -/
theorem isHermiteNormalForm_diagonal {d : n → ℤ} (hd : ∀ i, 0 < d i) :
    (diagonal d).IsHermiteNormalForm := by
  refine isHermiteNormalForm_of_isUpperTriangular (fun i j hj ↦ diagonal_apply_ne _ hj.ne')
    (by simpa using hd) fun i j hij ↦ ?_
  simp [diagonal_apply_ne _ hij.ne, hd j]

@[simp]
theorem isHermiteNormalForm_one : (1 : Matrix n n ℤ).IsHermiteNormalForm := by
  simpa only [diagonal_one] using isHermiteNormalForm_diagonal fun _ : n ↦ zero_lt_one

end Square

section Decidable

variable [Fintype m] [Fintype n] [LT m] [DecidableLT m] [LT n] [DecidableLT n]

instance instDecidableIsRowEchelon {R : Type*} [Zero R] [DecidableEq R] (A : Matrix m n R) :
    Decidable A.IsRowEchelon :=
  -- instance resolution cannot nest `Fintype.decidableForallFintype` under another binder
  have (i₁ i₂ : m) : DecidablePred fun j₂ : n ↦ (∀ j₁ < j₂, A i₁ j₁ = 0) → A i₂ j₂ = 0 :=
    fun _ ↦ inferInstance
  have (i₁ : m) : DecidablePred fun i₂ : m ↦
      i₁ < i₂ → ∀ j₂, (∀ j₁ < j₂, A i₁ j₁ = 0) → A i₂ j₂ = 0 :=
    fun _ ↦ inferInstance
  decidable_of_iff (∀ i₁ i₂, i₁ < i₂ → ∀ j₂, (∀ j₁ < j₂, A i₁ j₁ = 0) → A i₂ j₂ = 0) Iff.rfl

instance (A : Matrix m n ℤ) : Decidable A.IsHermiteNormalForm :=
  -- instance resolution cannot nest `Fintype.decidableForallFintype` under another binder
  have (i : m) : DecidablePred fun c : n ↦ A.IsLeadingEntry i c → 0 < A i c :=
    fun _ ↦ inferInstance
  have (i₁ i₂ : m) : DecidablePred fun c : n ↦
      i₁ < i₂ → A.IsLeadingEntry i₂ c → A i₁ c ∈ Set.Ico 0 (A i₂ c) :=
    fun _ ↦ inferInstance
  have (i₁ : m) : DecidablePred fun i₂ : m ↦
      ∀ c, i₁ < i₂ → A.IsLeadingEntry i₂ c → A i₁ c ∈ Set.Ico 0 (A i₂ c) :=
    fun _ ↦ inferInstance
  decidable_of_iff (A.IsRowEchelon ∧ (∀ i c, A.IsLeadingEntry i c → 0 < A i c) ∧
      ∀ i₁ i₂ c, i₁ < i₂ → A.IsLeadingEntry i₂ c → A i₁ c ∈ Set.Ico 0 (A i₂ c))
    (isHermiteNormalForm_iff A).symm

end Decidable

end Matrix
