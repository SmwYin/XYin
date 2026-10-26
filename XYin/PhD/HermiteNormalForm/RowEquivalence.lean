/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.Data.Int.Order.Units
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Row equivalence and integer row lattices

The span of the rows of an integer matrix is its integer row lattice. Unimodular row
operations preserve this submodule, as well as rank and the absolute value of the determinant.
These lemmas connect mathlib's `Matrix.RowEquivalent` with the invariants used in Hermite
normal form. Elementary operations themselves are supplied by
`Matrix.rowEquivalent_swap`, `Matrix.rowEquivalent_rowScale`, and
`Matrix.rowEquivalent_transvection`.
-/

namespace Matrix

variable {R m n : Type*} [CommRing R] [Fintype m] [DecidableEq m]

/-- Row equivalence is multiplication on the left by a matrix with unit determinant. -/
theorem rowEquivalent_iff_exists_isUnit_det {A B : Matrix m n R} :
    RowEquivalent A B ↔ ∃ U : Matrix m m R, IsUnit U.det ∧ U * A = B := by
  constructor
  · rintro ⟨U, hU⟩
    exact ⟨U, isUnits_det_units U, hU⟩
  · rintro ⟨U, hU, hUA⟩
    obtain ⟨u, rfl⟩ := (isUnit_iff_isUnit_det U).mpr hU
    exact ⟨u, hUA⟩

namespace RowEquivalent

variable {A B : Matrix m n R}

/-- Row equivalence preserves the image of the map taking coefficients to a row combination. -/
theorem range_vecMulLinear_eq (h : RowEquivalent A B) :
    LinearMap.range A.vecMulLinear = LinearMap.range B.vecMulLinear := by
  have range_le {C D : Matrix m n R} (hCD : RowEquivalent C D) :
      LinearMap.range D.vecMulLinear ≤ LinearMap.range C.vecMulLinear := by
    rcases hCD with ⟨U, rfl⟩
    rintro v ⟨w, rfl⟩
    exact ⟨w ᵥ* (U : Matrix m m R), vecMul_vecMul w (U : Matrix m m R) C⟩
  exact le_antisymm (range_le h.symm) (range_le h)

/-- Row equivalent matrices have the same row span, over the original coefficient ring. -/
theorem span_row_eq (h : RowEquivalent A B) :
    Submodule.span R (Set.range A.row) = Submodule.span R (Set.range B.row) := by
  simpa only [range_vecMulLinear] using h.range_vecMulLinear_eq

/-- Membership in the row lattice is unchanged by row equivalence. -/
theorem mem_span_row_iff (h : RowEquivalent A B) (v : n → R) :
    v ∈ Submodule.span R (Set.range A.row) ↔ v ∈ Submodule.span R (Set.range B.row) := by
  rw [h.span_row_eq]

/-- An equation expressing a vector as a row combination is solvable for either matrix. -/
theorem exists_vecMul_eq_iff (h : RowEquivalent A B) (v : n → R) :
    (∃ w, w ᵥ* A = v) ↔ ∃ w, w ᵥ* B = v := by
  change v ∈ LinearMap.range A.vecMulLinear ↔ v ∈ LinearMap.range B.vecMulLinear
  rw [h.range_vecMulLinear_eq]

/-- Row equivalence preserves rank, including over commutative rings such as `ℤ`. -/
theorem rank_eq [Fintype n] (h : RowEquivalent A B) : A.rank = B.rank := by
  obtain ⟨U, hU, rfl⟩ := rowEquivalent_iff_exists_isUnit_det.mp h
  exact (rank_mul_eq_right_of_isUnit_det U A hU).symm

/-- A change of coefficient ring preserves row equivalence. -/
theorem map {S : Type*} [CommRing S] (h : RowEquivalent A B) (f : R →+* S) :
    RowEquivalent (A.map f) (B.map f) := by
  rcases h with ⟨U, rfl⟩
  refine ⟨U.map f, ?_⟩
  simp [GeneralLinearGroup.smul_def, Matrix.map_mul]

/-- A unimodular row transformation preserves whether the determinant vanishes. -/
theorem det_eq_zero_iff {A B : Matrix m m R} (h : RowEquivalent A B) :
    A.det = 0 ↔ B.det = 0 := by
  obtain ⟨U, hU, rfl⟩ := rowEquivalent_iff_exists_isUnit_det.mp h
  rw [det_mul, hU.mul_right_eq_zero]

/-- A unimodular row transformation preserves nonsingularity. -/
theorem det_ne_zero_iff {A B : Matrix m m R} (h : RowEquivalent A B) :
    A.det ≠ 0 ↔ B.det ≠ 0 :=
  not_congr h.det_eq_zero_iff

end RowEquivalent

/-- An integer row transformation is unimodular precisely when its determinant is `1` or `-1`. -/
theorem rowEquivalent_iff_exists_det_eq_one_or_neg_one {A B : Matrix m n ℤ} :
    RowEquivalent A B ↔ ∃ U : Matrix m m ℤ, (U.det = 1 ∨ U.det = -1) ∧ U * A = B := by
  simp only [rowEquivalent_iff_exists_isUnit_det, Int.isUnit_iff]

namespace RowEquivalent

variable {A B : Matrix m m ℤ}

/-- Row equivalent square integer matrices have determinants equal up to sign. -/
theorem det_eq_or_eq_neg_det (h : RowEquivalent A B) :
    B.det = A.det ∨ B.det = -A.det := by
  obtain ⟨U, hU, rfl⟩ := rowEquivalent_iff_exists_det_eq_one_or_neg_one.mp h
  rcases hU with hU | hU
  · exact Or.inl (by rw [det_mul, hU, one_mul])
  · exact Or.inr (by rw [det_mul, hU, neg_one_mul])

/-- Row equivalence preserves the natural absolute value of the determinant. -/
theorem natAbs_det_eq (h : RowEquivalent A B) : A.det.natAbs = B.det.natAbs := by
  rcases h.det_eq_or_eq_neg_det with hdet | hdet <;> simp [hdet]

/-- Row equivalence preserves the absolute value of the determinant. -/
theorem abs_det_eq (h : RowEquivalent A B) : |A.det| = |B.det| := by
  rcases h.det_eq_or_eq_neg_det with hdet | hdet <;> simp [hdet]

end RowEquivalent

end Matrix
