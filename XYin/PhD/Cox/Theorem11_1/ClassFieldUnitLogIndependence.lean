/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnitOrbit
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # The logarithmic independence step of Janusz V.2.3

Janusz applies I.(11.17) and I.11.18 to the actual intermediate unit family.
Rows of the matrix below are evaluation places; columns are units. Deleting a
place gives positive column sums and negative off-diagonal entries. The final
conclusion concerns the full weighted logarithms of the original units, with
any one member deleted. Relation normalization and finite index are separate.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise

noncomputable section
namespace Cox.ClassFieldTheory
variable (L : Type*) [Field L] [NumberField L]

/-- The genuine principal-ideal-kernel units satisfy the weighted logarithmic product formula. -/
theorem principalUnit_sum_weightedLog (a : (toPrincipalIdeal (𝓞 L) L).ker) :
    ∑ v : InfinitePlace L, (v.mult : ℝ) * Real.log (v ((a : Lˣ) : L)) = 0 := by
  obtain ⟨e, he⟩ := (principalIdeal_eq_one_iff L _).mp (MonoidHom.mem_ker.mp a.2)
  have h := NumberField.Units.sum_mult_mul_log e
  rw [← he]
  exact h

/-- The logarithmic matrix after deleting one place and its corresponding unit.
Rows are evaluation places, and columns are the supplied multiplicative units. -/
def unitLogMinor (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker)
    (v₀ : InfinitePlace L) :
    Matrix {v : InfinitePlace L // v ≠ v₀} {v : InfinitePlace L // v ≠ v₀} ℝ :=
  fun i j => (i.val.mult : ℝ) * Real.log (i.val ((u j.val : Lˣ) : L))

variable (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker)
  (v₀ : InfinitePlace L)

/-- Smallness at every other place gives negative off-diagonal weighted logarithms. -/
theorem unitLogMinor_offDiagonal_neg
    (hu : ∀ v v' : InfinitePlace L, v' ≠ v → v' ((u v : Lˣ) : L) < 1) :
    Pairwise (fun i j => unitLogMinor L u v₀ i j < 0) := by
  intro i j hij
  have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  have hpos : 0 < i.val ((u j.val : Lˣ) : L) := InfinitePlace.pos_iff.mpr (Units.ne_zero _)
  exact mul_neg_of_pos_of_neg (Nat.cast_pos.mpr InfinitePlace.mult_pos)
    (Real.log_neg hpos (hu j.val i.val hne))

open scoped Classical in
/-- A truncated column sums to the negative of its omitted, strictly negative coordinate. -/
theorem unitLogMinor_column_sum_pos
    (hu : ∀ v v' : InfinitePlace L, v' ≠ v → v' ((u v : Lˣ) : L) < 1) :
    ∀ j, 0 < ∑ i, unitLogMinor L u v₀ i j := by
  intro j
  have hsum := principalUnit_sum_weightedLog L (u j.val)
  rw [Fintype.sum_eq_add_sum_subtype_ne _ v₀] at hsum
  have hpos : 0 < v₀ ((u j.val : Lˣ) : L) := InfinitePlace.pos_iff.mpr (Units.ne_zero _)
  have hneg : (v₀.mult : ℝ) * Real.log (v₀ ((u j.val : Lˣ) : L)) < 0 :=
    mul_neg_of_pos_of_neg (Nat.cast_pos.mpr InfinitePlace.mult_pos)
      (Real.log_neg hpos (hu j.val v₀ fun h => j.2 h.symm))
  have h : ∑ i, unitLogMinor L u v₀ i j =
      ∑ i : {i : InfinitePlace L // i ≠ v₀},
        (i.val.mult : ℝ) * Real.log (i.val ((u j.val : Lˣ) : L)) := rfl
  rw [h]
  linarith

open scoped Classical in
/-- Janusz I.11.18 applied to the actual deleted-place matrix; the empty determinant is allowed. -/
theorem unitLogMinor_det_ne_zero
    (hu : ∀ v v' : InfinitePlace L, v' ≠ v → v' ((u v : Lˣ) : L) < 1) :
    (unitLogMinor L u v₀).det ≠ 0 := by
  exact Matrix.det_ne_zero_of_sum_col_pos (unitLogMinor_offDiagonal_neg L u v₀ hu)
    (unitLogMinor_column_sum_pos L u v₀ hu)

/-- Deleting any one unit leaves linearly independent full weighted logarithmic vectors. -/
theorem linearIndependent_weightedLog_delete
    (hu : ∀ v v' : InfinitePlace L, v' ≠ v → v' ((u v : Lˣ) : L) < 1) :
    LinearIndependent ℝ (fun j : {v : InfinitePlace L // v ≠ v₀} =>
      fun v : InfinitePlace L => (v.mult : ℝ) * Real.log (v ((u j.val : Lˣ) : L))) := by
  classical
  have hcols :=
    Matrix.linearIndependent_cols_of_det_ne_zero (unitLogMinor_det_ne_zero L u v₀ hu)
  apply LinearIndependent.of_comp
    (LinearMap.funLeft ℝ ℝ (Subtype.val : {v : InfinitePlace L // v ≠ v₀} → InfinitePlace L))
  convert hcols using 1

end Cox.ClassFieldTheory
