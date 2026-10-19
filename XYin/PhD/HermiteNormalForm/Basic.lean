/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Int.Basic

/-!
# Integer row Hermite normal form

`Matrix.IsHermiteNormalForm` follows mathlib's `Matrix.IsReducedRowEchelon`: it is a
predicate on a matrix, with echelon shape, positive leading entries, and canonical remainders
above each leading entry. It applies to rectangular and singular matrices; zero rows are allowed.
In full rank two its shape is `!![a, b; 0, d]` with `0 < a`, `0 < d`, and `0 ≤ b < d`.

`RankTwo` proves existence and uniqueness directly by integer row operations. `Pivot` supplies
mathlib pivot certificates and rank; `RowEquivalence` supplies row-span invariance. Coordinate
conventions for particular applications are kept outside this definition.
-/

namespace Matrix

variable {m n : Type*}

/-- An integer matrix is in row Hermite normal form if it is in row echelon form,
its leading entries are positive, and entries above a leading entry are reduced modulo it.
Zero rows occur last, as required by `isRowEchelon`. -/
structure IsHermiteNormalForm [LT m] [LT n] (A : Matrix m n ℤ) : Prop where
  /-- The nonzero rows have strictly increasing leading positions; zero rows occur last. -/
  isRowEchelon : A.IsRowEchelon
  /-- Every leading entry is positive. -/
  pos ⦃i : m⦄ ⦃c : n⦄ (hA : A.IsLeadingEntry i c) : 0 < A i c
  /-- Entries above a leading entry are its canonical nonnegative remainders. -/
  reduced ⦃i₁ i₂ : m⦄ ⦃c : n⦄ (hlt : i₁ < i₂) (hA : A.IsLeadingEntry i₂ c) :
    A i₁ c ∈ Set.Ico 0 (A i₂ c)

section LT

variable [LT m] [LT n] {A : Matrix m n ℤ}

theorem isHermiteNormalForm_iff :
    A.IsHermiteNormalForm ↔ A.IsRowEchelon ∧
      (∀ i c, A.IsLeadingEntry i c → 0 < A i c) ∧
      ∀ i₁ i₂ c, i₁ < i₂ → A.IsLeadingEntry i₂ c → A i₁ c ∈ Set.Ico 0 (A i₂ c) :=
  ⟨fun h ↦ ⟨h.isRowEchelon, fun _ _ hc ↦ h.pos hc, fun _ _ _ hi hc ↦ h.reduced hi hc⟩,
    fun ⟨he, hp, hr⟩ ↦ ⟨he, fun {_ _} ↦ hp _ _, fun {_ _ _} ↦ hr _ _ _⟩⟩

@[simp]
theorem isHermiteNormalForm_zero : (0 : Matrix m n ℤ).IsHermiteNormalForm where
  isRowEchelon := fun _ _ _ _ _ ↦ rfl
  pos := fun _ _ h ↦ (h.2 rfl).elim
  reduced := fun _ _ _ _ h ↦ (h.2 rfl).elim

/-- Entries below a pivot vanish by the echelon condition. -/
theorem IsHermiteNormalForm.eq_zero_of_lt_of_isLeadingEntry {i₁ i₂ : m} {c : n}
    (h : A.IsHermiteNormalForm) (hlt : i₁ < i₂) (hc : A.IsLeadingEntry i₁ c) :
    A i₂ c = 0 :=
  h.isRowEchelon hlt hc.1

/-- An entry above a pivot is already its remainder modulo that pivot. -/
theorem IsHermiteNormalForm.emod_eq {i₁ i₂ : m} {c : n}
    (h : A.IsHermiteNormalForm) (hlt : i₁ < i₂) (hc : A.IsLeadingEntry i₂ c) :
    A i₁ c % A i₂ c = A i₁ c :=
  Int.emod_eq_of_lt (h.reduced hlt hc).1 (h.reduced hlt hc).2

/-- Integer reduced row echelon form is a special case of Hermite normal form. -/
theorem IsReducedRowEchelon.isHermiteNormalForm (h : A.IsReducedRowEchelon) :
    A.IsHermiteNormalForm where
  isRowEchelon := h.isRowEchelon
  pos := by intro i c hc; rw [h.eq_one hc]; exact zero_lt_one
  reduced := by intro i₁ i₂ c hlt hc; simp [h.eq_zero hlt hc, h.eq_one hc]

/-- A Hermite normal form with unit pivots is reduced row echelon form. -/
theorem IsHermiteNormalForm.isReducedRowEchelon (h : A.IsHermiteNormalForm)
    (hp : ∀ i c, A.IsLeadingEntry i c → A i c = 1) : A.IsReducedRowEchelon where
  isRowEchelon := h.isRowEchelon
  eq_one := fun i c hc ↦ hp i c hc
  eq_zero := by
    intro i₁ i₂ c hlt hc
    have hr := h.reduced hlt hc
    rw [hp _ _ hc] at hr
    obtain ⟨h0, h1⟩ := hr
    omega

theorem isReducedRowEchelon_iff_isHermiteNormalForm :
    A.IsReducedRowEchelon ↔ A.IsHermiteNormalForm ∧
      ∀ i c, A.IsLeadingEntry i c → A i c = 1 :=
  ⟨fun h ↦ ⟨h.isHermiteNormalForm, fun _ _ hc ↦ h.eq_one hc⟩,
    fun ⟨h, hp⟩ ↦ h.isReducedRowEchelon hp⟩

end LT

section LinearOrder

variable [LinearOrder m] [LT n] {A : Matrix m n ℤ}

/-- Every entry of a pivot column is nonnegative, including its zero entries below the pivot. -/
theorem IsHermiteNormalForm.nonneg_of_isLeadingEntry {i : m} {c : n}
    (h : A.IsHermiteNormalForm) (hc : A.IsLeadingEntry i c) (k : m) : 0 ≤ A k c := by
  rcases lt_trichotomy k i with hlt | rfl | hlt
  · exact (h.reduced hlt hc).1
  · exact (h.pos hc).le
  · rw [h.eq_zero_of_lt_of_isLeadingEntry hlt hc]

/-- Apart from the pivot itself, entries in its column lie in the pivot's remainder interval. -/
theorem IsHermiteNormalForm.mem_Ico_of_ne_of_isLeadingEntry {i k : m} {c : n}
    (h : A.IsHermiteNormalForm) (hne : k ≠ i) (hc : A.IsLeadingEntry i c) :
    A k c ∈ Set.Ico 0 (A i c) := by
  rcases hne.lt_or_gt with hlt | hlt
  · exact h.reduced hlt hc
  · rw [h.eq_zero_of_lt_of_isLeadingEntry hlt hc]
    exact ⟨le_rfl, h.pos hc⟩

/-- Selecting rows in their original order preserves Hermite normal form. -/
theorem IsHermiteNormalForm.submatrix_rows {m' : Type*} [LinearOrder m']
    (h : A.IsHermiteNormalForm) (f : m' ↪o m) :
    (A.submatrix f id).IsHermiteNormalForm where
  isRowEchelon := fun _ _ hlt _ hz ↦ h.isRowEchelon (f.strictMono hlt) hz
  pos := fun _ _ hc ↦ h.pos hc
  reduced := fun _ _ _ hlt hc ↦ h.reduced (f.strictMono hlt) hc

end LinearOrder

section Square

variable [LinearOrder n] {A : Matrix n n ℤ}

/-- For an upper triangular matrix with positive diagonal, the HNF conditions are just
the remainder bounds above the diagonal. -/
theorem isHermiteNormalForm_of_isUpperTriangular (ht : A.IsUpperTriangular)
    (hp : ∀ i, 0 < A i i) (hr : ∀ i j, i < j → A i j ∈ Set.Ico 0 (A j j)) :
    A.IsHermiteNormalForm := by
  have hlead (i : n) : A.IsLeadingEntry i i := ⟨fun _ hj ↦ ht hj, (hp i).ne'⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i₁ i₂ hi j hz
    have hji : j ≤ i₁ := le_of_not_gt fun hlt ↦ (hp i₁).ne' (hz i₁ hlt)
    exact ht (hji.trans_lt hi)
  · intro i c hc
    have heq := hc.unique (hlead i)
    simpa only [heq] using hp i
  · intro i₁ i₂ c hi hc
    obtain rfl := hc.unique (hlead i₂)
    exact hr _ _ hi

/-- Positive diagonal matrices are in Hermite normal form. -/
theorem isHermiteNormalForm_diagonal {d : n → ℤ} (hd : ∀ i, 0 < d i) :
    (diagonal d).IsHermiteNormalForm := by
  apply isHermiteNormalForm_of_isUpperTriangular
  · intro i j hj
    exact diagonal_apply_ne _ hj.ne'
  · simpa using hd
  · intro i j hij
    simp [diagonal_apply_ne _ hij.ne, hd j]

@[simp]
theorem isHermiteNormalForm_one : (1 : Matrix n n ℤ).IsHermiteNormalForm := by
  simpa only [diagonal_one] using isHermiteNormalForm_diagonal (fun _ : n ↦ zero_lt_one)

end Square

section Decidable

variable [Fintype m] [Fintype n] [LT m] [DecidableLT m] [LT n] [DecidableLT n]

instance (A : Matrix m n ℤ) : Decidable A.IsHermiteNormalForm := by
  letI (i₁ i₂ : m) : DecidablePred (fun j₂ : n ↦
      (∀ j₁ < j₂, A i₁ j₁ = 0) → A i₂ j₂ = 0) := fun _ ↦ inferInstance
  letI (i₁ : m) : DecidablePred (fun i₂ : m ↦
      i₁ < i₂ → ∀ j₂, (∀ j₁ < j₂, A i₁ j₁ = 0) → A i₂ j₂ = 0) :=
    fun _ ↦ inferInstance
  letI : Decidable A.IsRowEchelon := inferInstanceAs
    (Decidable (∀ i₁ i₂, i₁ < i₂ → ∀ j₂, (∀ j₁ < j₂, A i₁ j₁ = 0) → A i₂ j₂ = 0))
  letI (i₁ i₂ : m) : DecidablePred (fun c : n ↦
      i₁ < i₂ → A.IsLeadingEntry i₂ c → A i₁ c ∈ Set.Ico 0 (A i₂ c)) :=
    fun _ ↦ inferInstance
  letI (i₁ : m) : DecidablePred (fun i₂ : m ↦
      ∀ c, i₁ < i₂ → A.IsLeadingEntry i₂ c → A i₁ c ∈ Set.Ico 0 (A i₂ c)) :=
    fun _ ↦ inferInstance
  letI (i : m) : DecidablePred (fun c : n ↦ A.IsLeadingEntry i c → 0 < A i c) :=
    fun _ ↦ inferInstance
  exact decidable_of_iff (A.IsRowEchelon ∧
    (∀ i c, A.IsLeadingEntry i c → 0 < A i c) ∧
      ∀ i₁ i₂ c, i₁ < i₂ → A.IsLeadingEntry i₂ c → A i₁ c ∈ Set.Ico 0 (A i₂ c))
    isHermiteNormalForm_iff.symm

end Decidable

end Matrix
