/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Content of integer matrices

The content is the nonnegative greatest common divisor of all matrix entries. Its divisibility
characterization makes it independent of index order and invariant under unimodular operations.
-/

namespace Matrix

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- The nonnegative greatest common divisor of the entries of an integer matrix. -/
def content (A : Matrix m n ℤ) : ℕ :=
  Finset.univ.gcd fun ij : m × n ↦ (A ij.1 ij.2).natAbs

theorem dvd_content_iff {A : Matrix m n ℤ} {d : ℕ} :
    d ∣ A.content ↔ ∀ i j, d ∣ (A i j).natAbs := by
  simp [content, Finset.dvd_gcd_iff]

theorem content_dvd_entry (A : Matrix m n ℤ) (i : m) (j : n) :
    A.content ∣ (A i j).natAbs :=
  dvd_content_iff.mp dvd_rfl i j

theorem dvd_content {A : Matrix m n ℤ} {d : ℕ}
    (h : ∀ i j, d ∣ (A i j).natAbs) : d ∣ A.content :=
  dvd_content_iff.mpr h

@[simp]
theorem content_zero : (0 : Matrix m n ℤ).content = 0 := by
  simp [content, Finset.gcd_eq_zero_iff]

@[simp]
theorem content_eq_zero_iff {A : Matrix m n ℤ} : A.content = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    exact Int.natAbs_eq_zero.mp (Finset.gcd_eq_zero_iff.mp h (i, j) (Finset.mem_univ _))
  · rintro rfl
    exact content_zero

theorem content_dvd_mul_right (A : Matrix l m ℤ) (B : Matrix m n ℤ) :
    A.content ∣ (A * B).content := by
  refine dvd_content fun i j ↦ Int.natCast_dvd.mp ?_
  exact Finset.dvd_sum fun k _ ↦
    dvd_mul_of_dvd_left (Int.natCast_dvd.mpr (A.content_dvd_entry i k)) _

theorem content_dvd_mul_left (A : Matrix l m ℤ) (B : Matrix m n ℤ) :
    B.content ∣ (A * B).content := by
  refine dvd_content fun i j ↦ Int.natCast_dvd.mp ?_
  exact Finset.dvd_sum fun k _ ↦
    dvd_mul_of_dvd_right (Int.natCast_dvd.mpr (B.content_dvd_entry k j)) _

theorem content_mul_of_isUnit_det [DecidableEq n] (A : Matrix m n ℤ)
    {U : Matrix n n ℤ} (hU : IsUnit U.det) : (A * U).content = A.content := by
  apply Nat.dvd_antisymm
  · simpa only [Matrix.mul_assoc, mul_nonsing_inv U hU, Matrix.mul_one] using
      content_dvd_mul_right (A * U) U⁻¹
  · exact content_dvd_mul_right A U

theorem content_isUnit_det_mul [DecidableEq m] {U : Matrix m m ℤ}
    (hU : IsUnit U.det) (A : Matrix m n ℤ) : (U * A).content = A.content := by
  apply Nat.dvd_antisymm
  · simpa only [← Matrix.mul_assoc, nonsing_inv_mul U hU, Matrix.one_mul] using
      content_dvd_mul_left U⁻¹ (U * A)
  · exact content_dvd_mul_left U A

@[simp]
theorem content_transpose (A : Matrix m n ℤ) : A.transpose.content = A.content := by
  apply Nat.dvd_antisymm
  · exact dvd_content fun i j ↦ A.transpose.content_dvd_entry j i
  · exact dvd_content fun i j ↦ A.content_dvd_entry j i

@[simp]
theorem content_submatrix_equiv {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m n ℤ) (e : m' ≃ m) (f : n' ≃ n) :
    (A.submatrix e f).content = A.content := by
  apply Nat.dvd_antisymm
  · exact dvd_content fun i j ↦ by
      simpa using (A.submatrix e f).content_dvd_entry (e.symm i) (f.symm j)
  · exact dvd_content fun i j ↦ A.content_dvd_entry (e i) (f j)

/-- An explicit formula for content in dimension two. -/
theorem content_fin_two (A : Matrix (Fin 2) (Fin 2) ℤ) :
    A.content = Nat.gcd (Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
      (A 1 0).natAbs) (A 1 1).natAbs := by
  apply Nat.dvd_antisymm
  · simp only [Nat.dvd_gcd_iff]
    exact ⟨⟨⟨A.content_dvd_entry 0 0, A.content_dvd_entry 0 1⟩,
      A.content_dvd_entry 1 0⟩, A.content_dvd_entry 1 1⟩
  · apply dvd_content
    simp only [Fin.forall_fin_two]
    exact ⟨⟨(Nat.gcd_dvd_left _ _).trans ((Nat.gcd_dvd_left _ _).trans
      (Nat.gcd_dvd_left _ _)), (Nat.gcd_dvd_left _ _).trans
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))⟩,
      ⟨(Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _), Nat.gcd_dvd_right _ _⟩⟩

@[simp]
theorem content_diagonal_fin_two (a : Fin 2 → ℤ) :
    (Matrix.diagonal a).content = Nat.gcd (a 0).natAbs (a 1).natAbs := by
  simp [content_fin_two]

@[simp]
theorem content_adjugate (A : Matrix (Fin 2) (Fin 2) ℤ) :
    A.adjugate.content = A.content := by
  simp [content_fin_two, Matrix.adjugate_fin_two, Nat.gcd_comm, Nat.gcd_left_comm]

end Matrix
