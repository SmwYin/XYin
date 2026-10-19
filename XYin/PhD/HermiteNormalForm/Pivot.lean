/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.HermiteNormalForm.Basic
import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot

/-!
# Pivots and rank of Hermite normal forms

Every row echelon matrix with well-founded column order admits mathlib's pivot certificate.
In particular, an integer Hermite normal form inherits the existing API for zero rows, ordered
pivots, and rank. Square echelon matrices are upper triangular, so nonsingular Hermite normal
forms have positive diagonal entries and positive determinant.
-/

namespace Matrix

variable {m n : Type*} {R : Type*}

/-- Every row echelon matrix with well-founded column order has a pivot map, with `⊤` marking
its zero rows. This allows the entire `Matrix.IsPivotedBy` API to be used without storing
redundant pivot data in the echelon predicate. -/
theorem IsRowEchelon.exists_isPivotedBy [Zero R] [LT m] [LT n] [WellFoundedLT n]
    {A : Matrix m n R} (hA : A.IsRowEchelon) : ∃ l : m → WithTop n, A.IsPivotedBy l := by
  classical
  have hrow (i : m) : ∃ p : WithTop n,
      (∀ j : n, (j : WithTop n) < p → A i j = 0) ∧
        ∀ c : n, p = c → A i c ≠ 0 := by
    by_cases hi : A i = 0
    · refine ⟨⊤, fun j _ ↦ congrFun hi j, ?_⟩
      intro c hc
      exact (WithTop.top_ne_coe hc).elim
    · obtain ⟨c, hc⟩ := row_ne_zero_iff_exists_isLeadingEntry.mp hi
      refine ⟨c, fun j hj ↦ hc.1 j (WithTop.coe_lt_coe.mp hj), ?_⟩
      intro j hj
      have h := WithTop.coe_injective hj
      subst j
      exact hc.2
  choose l hl using hrow
  exact ⟨l, hA, hl⟩

/-- A square row echelon matrix indexed by a well-founded order is upper triangular. -/
theorem IsRowEchelon.isUpperTriangular [Zero R] [LT n] [WellFoundedLT n]
    {A : Matrix n n R} (hA : A.IsRowEchelon) : A.IsUpperTriangular := by
  have hz : ∀ j : n, ∀ i : n, j < i → A i j = 0 := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      intro i hji
      exact hA hji fun k hkj ↦ ih k hkj j hkj
  exact fun {i j} hji ↦ hz j i hji

/-- The rank of an echelon matrix is the number of its nonzero rows. -/
theorem IsRowEchelon.rank_eq_card_nonzero_rows [Finite m] [Fintype n]
    [LinearOrder m] [LinearOrder n] [CommRing R] [IsDomain R]
    {A : Matrix m n R} (hA : A.IsRowEchelon) : A.rank = Nat.card {i // A i ≠ 0} := by
  classical
  let := Fintype.ofFinite m
  obtain ⟨l, hl⟩ := hA.exists_isPivotedBy
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, ne_eq, hl.eq_top_iff]
    using hl.rank_eq

/-- In a nonsingular square echelon matrix, the diagonal entry is the leading entry of each
row. -/
theorem IsRowEchelon.isLeadingEntry_diag [Fintype n] [LinearOrder n]
    [CommRing R] {A : Matrix n n R} (hA : A.IsRowEchelon)
    (hdet : A.det ≠ 0) (i : n) : A.IsLeadingEntry i i := by
  refine ⟨fun j hji ↦ hA.isUpperTriangular hji, ?_⟩
  rw [det_of_isUpperTriangular hA.isUpperTriangular] at hdet
  exact fun hi ↦ hdet (Finset.prod_eq_zero (Finset.mem_univ i) hi)

namespace IsHermiteNormalForm

variable {A : Matrix m n ℤ}

/-- A Hermite normal form admits mathlib's pivot certificate, whose API provides increasing
pivots, the position of zero rows, and the rank formula. -/
theorem exists_isPivotedBy [LT m] [LT n] [WellFoundedLT n] (hA : A.IsHermiteNormalForm) :
    ∃ l : m → WithTop n, A.IsPivotedBy l :=
  hA.isRowEchelon.exists_isPivotedBy

/-- The rank of an integer Hermite normal form is the number of its nonzero rows. -/
theorem rank_eq_card_nonzero_rows [Finite m] [Fintype n] [LinearOrder m] [LinearOrder n]
    (hA : A.IsHermiteNormalForm) : A.rank = Nat.card {i // A i ≠ 0} :=
  hA.isRowEchelon.rank_eq_card_nonzero_rows

section Square

variable [LinearOrder n] {A : Matrix n n ℤ}

/-- A square Hermite normal form is upper triangular. -/
theorem isUpperTriangular [WellFoundedLT n] (hA : A.IsHermiteNormalForm) :
    A.IsUpperTriangular :=
  hA.isRowEchelon.isUpperTriangular

variable [Fintype n]

/-- The determinant of a square Hermite normal form is the product of its diagonal entries. -/
theorem det_eq_prod_diagonal (hA : A.IsHermiteNormalForm) : A.det = ∏ i, A i i :=
  det_of_isUpperTriangular hA.isUpperTriangular

/-- Every diagonal entry in a nonsingular Hermite normal form is strictly positive. -/
theorem diagonal_pos (hA : A.IsHermiteNormalForm) (hdet : A.det ≠ 0) (i : n) :
    0 < A i i :=
  hA.pos (hA.isRowEchelon.isLeadingEntry_diag hdet i)

/-- A nonsingular Hermite normal form has positive determinant. -/
theorem det_pos (hA : A.IsHermiteNormalForm) (hdet : A.det ≠ 0) : 0 < A.det := by
  rw [hA.det_eq_prod_diagonal]
  exact Finset.prod_pos fun i _ ↦ hA.diagonal_pos hdet i

/-- The determinant of a square Hermite normal form is nonnegative, including the singular
case. -/
theorem det_nonneg (hA : A.IsHermiteNormalForm) : 0 ≤ A.det := by
  by_cases hdet : A.det = 0
  · exact hdet ▸ le_rfl
  · exact (hA.det_pos hdet).le

end Square

end IsHermiteNormalForm

end Matrix
