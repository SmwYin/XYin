/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
module

public import XYin.PhD.HermiteNormalForm.ForMathlib.Basic
public import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations

import Mathlib.Data.Finset.Sort

/-!
# Existence of the Hermite normal form

Every integer matrix, with finite linearly ordered rows and columns, has a Hermite normal form.

## Main definitions

* `Matrix.HermiteNormalForm`: a Hermite normal form of `A`, bundling a unimodular matrix `U`, a
  matrix `H` in Hermite normal form, and the equation `H = U * A`.

## Main results

* `Matrix.exists_rowEquivalent_isHermiteNormalForm`: every integer matrix is row equivalent to a
  matrix in Hermite normal form.
* `Matrix.hermiteNormalForm`: a choice of Hermite normal form of an integer matrix.

## Implementation notes

`Matrix.HermiteNormalForm A` is data rather than a proposition, since `U` is not determined by `A`
when the rows of `A` are linearly dependent.

The proof of existence is by induction on the number of columns. Suppose the first `l` columns
are in Hermite normal form, and let `S` be the set of rows vanishing on those columns. A Euclidean
reduction on the rows in `S` leaves at most one nonzero entry of the last column in `S`, in the
first row of `S`. This row is zero outside the last column, so subtracting multiples of it from
the rows above only changes the last column.

## Tags

matrix, echelon form, Hermite normal form, unimodular
-/

public section

namespace Matrix

variable {m n : Type*}

section Bundled

variable [Fintype m] [DecidableEq m] [LT m] [LT n]

/-- A Hermite normal form of an integer matrix `A`: a unimodular matrix `U` and a matrix `H` in
Hermite normal form such that `H = U * A`. -/
structure HermiteNormalForm (A : Matrix m n ℤ) where
  /-- The unimodular matrix taking `A` to `H`. -/
  U : GL m ℤ
  /-- The matrix in Hermite normal form. -/
  H : Matrix m n ℤ
  /-- The matrix `H` is in Hermite normal form. -/
  isHermiteNormalForm : H.IsHermiteNormalForm
  /-- The matrix `H` is obtained from `A` by left multiplication by `U`. -/
  H_eq : H = (U : Matrix m m ℤ) * A

variable {A : Matrix m n ℤ}

/-- A matrix in Hermite normal form is its own Hermite normal form, with `U = 1`. -/
@[expose] def IsHermiteNormalForm.hermiteNormalForm (hA : A.IsHermiteNormalForm) :
    A.HermiteNormalForm where
  U := 1
  H := A
  isHermiteNormalForm := hA
  H_eq := by simp

namespace HermiteNormalForm

/-- A Hermite normal form is determined by its unimodular matrix. -/
@[ext]
theorem ext {h₁ h₂ : A.HermiteNormalForm} (hU : h₁.U = h₂.U) : h₁ = h₂ := by
  obtain ⟨U₁, H₁, _, rfl⟩ := h₁
  obtain ⟨U₂, H₂, _, rfl⟩ := h₂
  simp_all

variable (h : A.HermiteNormalForm)

theorem rowEquivalent : RowEquivalent A h.H :=
  ⟨h.U, h.H_eq.symm⟩

theorem isUnit_det_U : IsUnit (h.U : Matrix m m ℤ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 h.U.isUnit

/-- The matrix `A` is recovered from its Hermite normal form using the inverse of `U`. -/
theorem eq_inv_mul : A = ((h.U⁻¹ : GL m ℤ) : Matrix m m ℤ) * h.H := by
  rw [h.H_eq, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

end HermiteNormalForm

/-- A Hermite normal form of `A` exists if and only if `A` is row equivalent to a matrix in
Hermite normal form. -/
theorem nonempty_hermiteNormalForm_iff :
    Nonempty A.HermiteNormalForm ↔ ∃ H, RowEquivalent A H ∧ H.IsHermiteNormalForm := by
  refine ⟨fun ⟨h⟩ ↦ ⟨h.H, h.rowEquivalent, h.isHermiteNormalForm⟩, ?_⟩
  rintro ⟨_, ⟨U, rfl⟩, hH⟩
  exact ⟨⟨U, _, hH, rfl⟩⟩

end Bundled

section RowOps

variable [Fintype m] [DecidableEq m]

/-- `B'` is obtained from `B` using row operations supported on the rows in `S`. -/
private structure RowOpsOn (S : Finset m) (B B' : Matrix m n ℤ) : Prop where
  rowEquivalent : RowEquivalent B B'
  row_eq ⦃i : m⦄ (hi : i ∉ S) : B' i = B i
  eq_zero ⦃j : n⦄ (hj : ∀ i ∈ S, B i j = 0) ⦃i : m⦄ (hi : i ∈ S) : B' i j = 0

private theorem RowOpsOn.refl (S : Finset m) (B : Matrix m n ℤ) : RowOpsOn S B B :=
  ⟨.refl B, fun _ _ ↦ rfl, fun _ hj _ hi ↦ hj _ hi⟩

private theorem RowOpsOn.trans {S : Finset m} {B₁ B₂ B₃ : Matrix m n ℤ}
    (h₁₂ : RowOpsOn S B₁ B₂) (h₂₃ : RowOpsOn S B₂ B₃) : RowOpsOn S B₁ B₃ :=
  ⟨h₁₂.rowEquivalent.trans h₂₃.rowEquivalent, fun _ hi ↦ (h₂₃.row_eq hi).trans (h₁₂.row_eq hi),
    fun _ hj _ hi ↦ h₂₃.eq_zero (fun _ hk ↦ h₁₂.eq_zero hj hk) hi⟩

private theorem RowOpsOn.transvection {S : Finset m} {i k : m} (hi : i ∈ S) (hk : k ∈ S)
    (hne : i ≠ k) (c : ℤ) (B : Matrix m n ℤ) : RowOpsOn S B (Matrix.transvection i k c * B) where
  rowEquivalent := rowEquivalent_transvection B i k hne c
  row_eq a ha := by
    ext b
    exact transvection_mul_apply_of_ne i k a b (ne_of_mem_of_not_mem hi ha).symm c B
  eq_zero j hj a ha := by
    obtain rfl | hai := eq_or_ne a i
    · simp [transvection_mul_apply_same, hj _ ha, hj _ hk]
    · rw [transvection_mul_apply_of_ne i k a j hai c B, hj _ ha]

private theorem RowOpsOn.swap {S : Finset m} {i k : m} (hi : i ∈ S) (hk : k ∈ S)
    (B : Matrix m n ℤ) : RowOpsOn S B (Matrix.swap ℤ i k * B) where
  rowEquivalent := rowEquivalent_swap B i k
  row_eq a ha := by
    ext b
    exact swap_mul_of_ne (ne_of_mem_of_not_mem hi ha).symm (ne_of_mem_of_not_mem hk ha).symm B
  eq_zero j hj a ha := by
    obtain rfl | hai := eq_or_ne a i
    · rw [swap_mul_apply_left, hj _ hk]
    obtain rfl | hak := eq_or_ne a k
    · rw [swap_mul_apply_right, hj _ hi]
    · rw [swap_mul_of_ne hai hak, hj _ ha]

private theorem RowOpsOn.neg {S : Finset m} {i : m} (hi : i ∈ S) (B : Matrix m n ℤ) :
    RowOpsOn S B (rowScale i ((-1 : ℤˣ) : ℤ) * B) where
  rowEquivalent := rowEquivalent_rowScale B i (-1)
  row_eq a ha := by
    ext b
    simp [rowScale_mul, updateRow_apply, (ne_of_mem_of_not_mem hi ha).symm]
  eq_zero j hj a ha := by
    rw [rowScale_mul, updateRow_apply]
    split_ifs with hai
    · simp [hai ▸ hj a ha]
    · exact hj a ha

/-- A Euclidean reduction on the rows in `S` leaves at most one nonzero entry of column `c` among
these rows. -/
private theorem exists_rowOpsOn_eq_of_ne_zero (S : Finset m) (c : n) (B : Matrix m n ℤ) :
    ∃ B', RowOpsOn S B B' ∧ ∀ i₁ ∈ S, ∀ i₂ ∈ S, B' i₁ c ≠ 0 → B' i₂ c ≠ 0 → i₁ = i₂ := by
  induction hN : ∑ i ∈ S, (B i c).natAbs using Nat.strong_induction_on generalizing B with
  | _ N ih =>
    by_cases hex : ∃ i₁ ∈ S, ∃ i₂ ∈ S, i₁ ≠ i₂ ∧ B i₁ c ≠ 0 ∧ (B i₁ c).natAbs ≤ (B i₂ c).natAbs
    · obtain ⟨i₁, h₁, i₂, h₂, hne, hc, hle⟩ := hex
      have hstep := RowOpsOn.transvection h₂ h₁ hne.symm (-(B i₂ c / B i₁ c)) B
      set B₁ := Matrix.transvection i₂ i₁ (-(B i₂ c / B i₁ c)) * B with hB₁
      have hsame : B₁ i₂ c = B i₂ c % B i₁ c := by
        rw [hB₁, transvection_mul_apply_same, Int.emod_def]
        ring
      have hother (i : m) (hi : i ≠ i₂) : B₁ i c = B i c :=
        transvection_mul_apply_of_ne i₂ i₁ i c hi _ B
      have hlt : ∑ i ∈ S, (B₁ i c).natAbs < N := by
        rw [← hN]
        refine Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨i₂, h₂, ?_⟩
        · obtain rfl | hi := eq_or_ne i i₂
          · rw [hsame]
            have h₀ := Int.emod_nonneg (B i c) hc
            have h₃ := Int.emod_lt_abs (B i c) hc
            rw [Int.abs_eq_natAbs] at h₃
            omega
          · rw [hother i hi]
        · rw [hsame]
          have h₀ := Int.emod_nonneg (B i₂ c) hc
          have h₃ := Int.emod_lt_abs (B i₂ c) hc
          rw [Int.abs_eq_natAbs] at h₃
          omega
      obtain ⟨B', hB', h⟩ := ih _ hlt B₁ rfl
      exact ⟨B', hstep.trans hB', h⟩
    · refine ⟨B, .refl S B, fun i₁ h₁ i₂ h₂ ha hb ↦ ?_⟩
      by_contra hne
      obtain hle | hle := le_total (B i₁ c).natAbs (B i₂ c).natAbs
      · exact hex ⟨i₁, h₁, i₂, h₂, hne, ha, hle⟩
      · exact hex ⟨i₂, h₂, i₁, h₁, Ne.symm hne, hb, hle⟩

/-- Row operations on the rows in `S` can move the only nonzero entry of column `c` among these
rows to any chosen row in `S`, and make it nonnegative. -/
private theorem exists_rowOpsOn_pivot {S : Finset m} {i₀ : m} (h₀ : i₀ ∈ S) (c : n)
    (B : Matrix m n ℤ) :
    ∃ B', RowOpsOn S B B' ∧ 0 ≤ B' i₀ c ∧ ∀ i ∈ S, i ≠ i₀ → B' i c = 0 := by
  obtain ⟨B₁, h₁, hs⟩ := exists_rowOpsOn_eq_of_ne_zero S c B
  obtain ⟨B₂, h₂, hz⟩ : ∃ B₂, RowOpsOn S B B₂ ∧ ∀ i ∈ S, i ≠ i₀ → B₂ i c = 0 := by
    by_cases hex : ∀ i ∈ S, B₁ i c = 0
    · exact ⟨B₁, h₁, fun i hi _ ↦ hex i hi⟩
    · obtain ⟨i₁, hi₁, hc⟩ : ∃ i₁ ∈ S, B₁ i₁ c ≠ 0 := by simpa using hex
      have hzero (i : m) (hi : i ∈ S) (hne : i ≠ i₁) : B₁ i c = 0 := by
        by_contra hi'
        exact hne (hs _ hi _ hi₁ hi' hc)
      refine ⟨Matrix.swap ℤ i₀ i₁ * B₁, h₁.trans (.swap h₀ hi₁ B₁), fun i hi hne ↦ ?_⟩
      obtain rfl | hi' := eq_or_ne i i₁
      · rw [swap_mul_apply_right, hzero _ h₀ hne.symm]
      · rw [swap_mul_of_ne hne hi', hzero _ hi hi']
  obtain hnn | hnp := le_total 0 (B₂ i₀ c)
  · exact ⟨B₂, h₂, hnn, hz⟩
  · refine ⟨rowScale i₀ ((-1 : ℤˣ) : ℤ) * B₂, h₂.trans (.neg h₀ B₂), ?_, fun i hi hne ↦ ?_⟩
    · simpa [rowScale_mul] using hnp
    · simp [rowScale_mul, updateRow_apply, hne, hz i hi hne]

/-- Adding multiples of row `i₀` to the other rows is a row equivalence. -/
private theorem rowEquivalent_add_mul_row (A : Matrix m n ℤ) (i₀ : m) (q : m → ℤ) (hq : q i₀ = 0) :
    RowEquivalent A (of fun i j ↦ A i j + q i * A i₀ j) := by
  let E : Matrix m m ℤ := vecMulVec q (Pi.single i₀ 1)
  have hE : E * E = 0 := by
    ext i j
    simp [E, Matrix.mul_apply, vecMulVec_apply, Pi.single_apply, hq]
  refine ⟨⟨1 + E, 1 - E, by simp [Matrix.mul_sub, Matrix.add_mul, hE],
    by simp [Matrix.sub_mul, Matrix.mul_add, hE]⟩, ?_⟩
  change (1 + E) * A = _
  rw [Matrix.add_mul, Matrix.one_mul]
  ext i j
  simp [Matrix.mul_apply, E, vecMulVec_apply, Pi.single_apply]

end RowOps

section Exists

variable [LinearOrder m]

/-- If the first `l` columns of `B` are in Hermite normal form then so is `B`, as long as its last
column satisfies the echelon, positivity and reducedness conditions on the rows which vanish on
the first `l` columns. -/
private theorem isHermiteNormalForm_of_submatrix_castSucc {l : ℕ} {B : Matrix m (Fin (l + 1)) ℤ}
    (h : (B.submatrix id Fin.castSucc).IsHermiteNormalForm)
    (he : ∀ ⦃i₁ i₂⦄, i₁ < i₂ → (∀ j : Fin l, B i₁ j.castSucc = 0) → B i₂ (Fin.last l) = 0)
    (hp : ∀ ⦃i⦄, (∀ j : Fin l, B i j.castSucc = 0) → B i (Fin.last l) ≠ 0 →
      0 < B i (Fin.last l) ∧ ∀ ⦃i'⦄, i' < i → B i' (Fin.last l) ∈ Set.Ico 0 (B i (Fin.last l))) :
    B.IsHermiteNormalForm := by
  have hlead {i : m} {j : Fin l} (hc : B.IsLeadingEntry i j.castSucc) :
      (B.submatrix id Fin.castSucc).IsLeadingEntry i j :=
    ⟨fun j' hj' ↦ hc.1 _ (Fin.castSucc_lt_castSucc_iff.2 hj'), hc.2⟩
  have hzero {i : m} (hc : B.IsLeadingEntry i (Fin.last l)) (j : Fin l) : B i j.castSucc = 0 :=
    hc.1 _ j.castSucc_lt_last
  refine ⟨fun i₁ i₂ hlt j₂ hz ↦ ?_, fun i c hc ↦ ?_, fun i₁ i₂ c hlt hc ↦ ?_⟩
  · induction j₂ using Fin.lastCases with
    | last => exact he hlt fun j ↦ hz _ j.castSucc_lt_last
    | cast j =>
      exact h.isRowEchelon hlt (j₂ := j) fun j₁ hj₁ ↦ hz _ (Fin.castSucc_lt_castSucc_iff.2 hj₁)
  · induction c using Fin.lastCases with
    | last => exact (hp (hzero hc) hc.2).1
    | cast j => exact h.pos (hlead hc)
  · induction c using Fin.lastCases with
    | last => exact (hp (hzero hc) hc.2).2 hlt
    | cast j => exact h.mem_Ico hlt (hlead hc)

variable [Fintype m]

/-- A matrix whose first `l` columns are in Hermite normal form is row equivalent to a matrix in
Hermite normal form. -/
private theorem exists_rowEquivalent_isHermiteNormalForm_of_submatrix_castSucc {l : ℕ}
    (B : Matrix m (Fin (l + 1)) ℤ) (hH : (B.submatrix id Fin.castSucc).IsHermiteNormalForm) :
    ∃ H, RowEquivalent B H ∧ H.IsHermiteNormalForm := by
  let S : Finset m := {i | ∀ j : Fin l, B i j.castSucc = 0}
  have hS {i : m} : i ∈ S ↔ ∀ j : Fin l, B i j.castSucc = 0 := by simp [S]
  have hup {i₁ i₂ : m} (hlt : i₁ < i₂) (hi : i₁ ∈ S) : i₂ ∈ S :=
    hS.2 fun j ↦ hH.isRowEchelon hlt (j₂ := j) fun j₁ _ ↦ hS.1 hi j₁
  obtain hemp | hne := S.eq_empty_or_nonempty
  · refine ⟨B, .refl B, isHermiteNormalForm_of_submatrix_castSucc hH (fun i₁ _ _ hz ↦ ?_)
      fun i hz ↦ ?_⟩ <;> simpa [hemp] using hS.2 hz
  let i₀ := S.min' hne
  have hi₀ : i₀ ∈ S := S.min'_mem hne
  obtain ⟨B₁, hB₁, hnn, hz⟩ := exists_rowOpsOn_pivot hi₀ (Fin.last l) B
  have hcol {i : m} (hi : i ∈ S) (j : Fin l) : B₁ i j.castSucc = 0 :=
    hB₁.eq_zero (fun _ hk ↦ hS.1 hk j) hi
  let g := B₁ i₀ (Fin.last l)
  let q : m → ℤ := fun i ↦ if i ∈ S then 0 else -(B₁ i (Fin.last l) / g)
  have hq₀ : q i₀ = 0 := by simp [q, hi₀]
  have hqS {i : m} (hi : i ∈ S) : q i = 0 := by simp [q, hi]
  refine ⟨_, hB₁.rowEquivalent.trans (rowEquivalent_add_mul_row B₁ i₀ q hq₀), ?_⟩
  set B₂ : Matrix m (Fin (l + 1)) ℤ := of fun i j ↦ B₁ i j + q i * B₁ i₀ j with hB₂
  have hold (i : m) (j : Fin l) : B₂ i j.castSucc = B i j.castSucc := by
    by_cases hi : i ∈ S
    · simp [hB₂, hcol hi, hcol hi₀, hS.1 hi]
    · simp [hB₂, hcol hi₀, congrFun (hB₁.row_eq hi) j.castSucc]
  have hlast {i : m} (hi : i ∈ S) : B₂ i (Fin.last l) = B₁ i (Fin.last l) := by
    simp [hB₂, hqS hi]
  have hzS {i : m} : (∀ j : Fin l, B₂ i j.castSucc = 0) ↔ i ∈ S := by simp [hold, hS]
  have hsub₂ : B₂.submatrix id Fin.castSucc = B.submatrix id Fin.castSucc := by
    ext i j
    simp [hold]
  refine isHermiteNormalForm_of_submatrix_castSucc (hsub₂ ▸ hH) (fun i₁ i₂ hlt h ↦ ?_)
    fun i h hc ↦ ?_
  · have hi₁ := hzS.1 h
    have hne' : i₂ ≠ i₀ := ((S.min'_le _ hi₁).trans_lt hlt).ne'
    rw [hlast (hup hlt hi₁), hz _ (hup hlt hi₁) hne']
  · have hi := hzS.1 h
    obtain rfl : i = i₀ := by
      by_contra hne'
      exact hc (by rw [hlast hi, hz _ hi hne'])
    rw [hlast hi₀] at hc ⊢
    have hg : 0 < g := lt_of_le_of_ne hnn (Ne.symm hc)
    refine ⟨hg, fun i' hlt ↦ ?_⟩
    have hi' : i' ∉ S := fun h' ↦ absurd (S.min'_le _ h') (not_le.2 hlt)
    have heq : B₂ i' (Fin.last l) = B₁ i' (Fin.last l) % g := by
      simp only [hB₂, of_apply, q, hi', ite_false, Int.emod_def]
      ring
    rw [heq]
    exact ⟨Int.emod_nonneg _ hg.ne', Int.emod_lt_of_pos _ hg⟩

private theorem exists_rowEquivalent_isHermiteNormalForm_fin (l : ℕ) (A : Matrix m (Fin l) ℤ) :
    ∃ H, RowEquivalent A H ∧ H.IsHermiteNormalForm := by
  induction l with
  | zero => exact ⟨A, .refl A, fun _ _ _ j ↦ j.elim0, fun _ j ↦ j.elim0, fun _ _ j ↦ j.elim0⟩
  | succ l ih =>
    obtain ⟨_, ⟨U, rfl⟩, hH⟩ := ih (A.submatrix id Fin.castSucc)
    have hsub : (U • A).submatrix id Fin.castSucc = U • A.submatrix id Fin.castSucc := by
      ext i j
      simp [Matrix.mul_apply]
    obtain ⟨H, hB, hH'⟩ := exists_rowEquivalent_isHermiteNormalForm_of_submatrix_castSucc (U • A)
      (by rw [hsub]; exact hH)
    exact ⟨H, RowEquivalent.trans ⟨U, rfl⟩ hB, hH'⟩

variable [Finite n] [LinearOrder n]

/-- Every integer matrix is row equivalent to a matrix in Hermite normal form. -/
theorem exists_rowEquivalent_isHermiteNormalForm (A : Matrix m n ℤ) :
    ∃ H, RowEquivalent A H ∧ H.IsHermiteNormalForm := by
  cases nonempty_fintype n
  let e := Fintype.orderIsoFinOfCardEq n rfl
  obtain ⟨_, ⟨U, rfl⟩, hH⟩ := exists_rowEquivalent_isHermiteNormalForm_fin _ (A.submatrix id e)
  refine ⟨U • A, ⟨U, rfl⟩, ?_⟩
  convert hH.submatrix_orderIso (OrderIso.refl m) e.symm using 1
  ext i j
  simp [Matrix.mul_apply]

instance (A : Matrix m n ℤ) : Nonempty A.HermiteNormalForm :=
  nonempty_hermiteNormalForm_iff.2 (exists_rowEquivalent_isHermiteNormalForm A)

/-- A choice of Hermite normal form of an integer matrix. -/
noncomputable def hermiteNormalForm (A : Matrix m n ℤ) : A.HermiteNormalForm :=
  Classical.arbitrary _

end Exists

end Matrix
