/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Algebra.Ring.Fin
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.LinearCombination

/-!
# Hermite normal form for full-rank integer submodules

This file develops the Hermite-normal-form API needed in Cox, Chapter 11.  Unlike Smith normal
form, Hermite normal form is canonical only after fixing the ambient basis, so that basis is an
explicit parameter of `Module.Basis.HermiteNormalForm`.  The bundled definition is available in
arbitrary finite rank; the constructive existence theorem currently supplies the rank-two case
used by Cox.

## Main results

* `Matrix.IsColumnHermiteNormalForm.det_eq_prod_diagonal`: a column HNF is upper triangular, so
  its determinant is the product of its (positive) pivots.
* `Matrix.exists_right_mul_SL2_isColumnHermiteNormalForm`: every positive-determinant `2 × 2`
  integer matrix has a column HNF in its right `SL₂(ℤ)`-orbit; the left-multiplication version
  is `Matrix.exists_SL2_mul_eq_upperTriangular`.
* `Matrix.IsColumnHermiteNormalForm.eq_of_mul_isUnit_det`: uniqueness of the rank-two column HNF.
* `Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one`: the quotient by
  a rank-two sublattice is cyclic iff its HNF matrix is primitive.
-/

open Module MatrixGroups

noncomputable section

namespace Matrix

/-- A square integer matrix is in column Hermite normal form when it is upper triangular,
has positive pivots, and each entry above a pivot is the canonical nonnegative remainder.

With columns interpreted as generators, the rank-two shape is `!![d, b; 0, a]` with
`0 < d`, `0 < a`, and `0 ≤ b < d`.
-/
structure IsColumnHermiteNormalForm {ι : Type*} [Preorder ι]
    (A : Matrix ι ι ℤ) : Prop where
  /-- Entries below the diagonal vanish. -/
  belowDiagonal_eq_zero : ∀ i j, j < i → A i j = 0
  /-- Every diagonal pivot is strictly positive. -/
  diagonal_pos : ∀ i, 0 < A i i
  /-- Entries above a pivot are its canonical nonnegative remainders. -/
  reduced : ∀ i j, i < j → A i j ∈ Set.Ico 0 (A i i)

namespace IsColumnHermiteNormalForm

section LinearOrder

variable {ι : Type*} [LinearOrder ι] {A : Matrix ι ι ℤ}

/-- A column Hermite normal form is upper triangular. -/
theorem blockTriangular (h : A.IsColumnHermiteNormalForm) : A.BlockTriangular id :=
  fun i j hji ↦ h.belowDiagonal_eq_zero i j hji

variable [Fintype ι]

/-- The determinant of a column Hermite normal form is the product of its pivots. -/
theorem det_eq_prod_diagonal (h : A.IsColumnHermiteNormalForm) : A.det = ∏ i, A i i :=
  det_of_upperTriangular h.blockTriangular

/-- A column Hermite normal form has positive determinant. -/
theorem det_pos (h : A.IsColumnHermiteNormalForm) : 0 < A.det :=
  h.det_eq_prod_diagonal ▸ Finset.prod_pos fun i _ ↦ h.diagonal_pos i

end LinearOrder

section FinTwo

variable {A : Matrix (Fin 2) (Fin 2) ℤ}

theorem one_zero (h : A.IsColumnHermiteNormalForm) : A 1 0 = 0 :=
  h.belowDiagonal_eq_zero 1 0 Fin.zero_lt_one

theorem zero_zero_pos (h : A.IsColumnHermiteNormalForm) : 0 < A 0 0 :=
  h.diagonal_pos 0

theorem one_one_pos (h : A.IsColumnHermiteNormalForm) : 0 < A 1 1 :=
  h.diagonal_pos 1

theorem zero_one_mem (h : A.IsColumnHermiteNormalForm) : A 0 1 ∈ Set.Ico 0 (A 0 0) :=
  h.reduced 0 1 Fin.zero_lt_one

/-- A rank-two column Hermite normal form is `!![d, b; 0, a]`. -/
theorem eq_fin_two (h : A.IsColumnHermiteNormalForm) : A = !![A 0 0, A 0 1; 0, A 1 1] := by
  conv_lhs => rw [eta_fin_two A, h.one_zero]

theorem det_eq (h : A.IsColumnHermiteNormalForm) : A.det = A 0 0 * A 1 1 := by
  simp [h.det_eq_prod_diagonal, Fin.prod_univ_two]

end FinTwo

end IsColumnHermiteNormalForm

/-- The explicit form of a rank-two column Hermite normal form. -/
theorem isColumnHermiteNormalForm_fin_two_iff (A : Matrix (Fin 2) (Fin 2) ℤ) :
    A.IsColumnHermiteNormalForm ↔
      A 1 0 = 0 ∧ 0 < A 0 0 ∧ 0 < A 1 1 ∧ A 0 1 ∈ Set.Ico 0 (A 0 0) := by
  refine ⟨fun h ↦ ⟨h.one_zero, h.zero_zero_pos, h.one_one_pos, h.zero_one_mem⟩,
    fun ⟨h10, h00, h11, h01⟩ ↦ ⟨fun i j hji ↦ ?_, fun i ↦ ?_, fun i j hij ↦ ?_⟩⟩ <;>
    fin_cases i <;> (try fin_cases j) <;> simp_all

/-- The defining inequalities for a rank-two column HNF matrix. -/
theorem isColumnHermiteNormalForm_fin_two {d r a : ℤ} (hd : 0 < d) (ha : 0 < a)
    (hr0 : 0 ≤ r) (hrd : r < d) :
    IsColumnHermiteNormalForm !![d, r; 0, a] :=
  (isColumnHermiteNormalForm_fin_two_iff _).2 ⟨rfl, hd, ha, hr0, hrd⟩

/-- The gcd of the four entries of a two-by-two integer matrix, i.e. its first determinantal
divisor `D₁(A)`.

In rank two `D₁ = D_{n-1}`, so `rankTwoContent A = 1` is exactly the criterion for the quotient
by the column span to be cyclic
(`Module.Basis.HermiteNormalForm.quotient_isAddCyclic_iff_rankTwoContent_eq_one`). In rank
`n ≥ 3` the correct criterion is `D_{n-1}(A) = 1` (the gcd of the `(n-1)`-minors); the gcd of
the entries being `1` is not enough, e.g. `diag(1, 2, 2)` has entry gcd `1` but quotient
`ℤ/2 × ℤ/2`. -/
def rankTwoContent (A : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  Nat.gcd (Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
    (A 1 0).natAbs) (A 1 1).natAbs

theorem rankTwoContent_fin_two_of (a b c d : ℤ) :
    rankTwoContent !![a, b; c, d] =
      Nat.gcd (Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs) d.natAbs :=
  rfl

/-- The content is the `Finset.gcd` of the absolute values of the entries. -/
theorem rankTwoContent_eq_finset_gcd (A : Matrix (Fin 2) (Fin 2) ℤ) :
    A.rankTwoContent = Finset.univ.gcd fun p : Fin 2 × Fin 2 ↦ (A p.1 p.2).natAbs := by
  rw [show (Finset.univ : Finset (Fin 2 × Fin 2)) = {(0, 0), (0, 1), (1, 0), (1, 1)} from rfl]
  simp [rankTwoContent, Finset.gcd_insert, normalize_eq, gcd_eq_nat_gcd, Nat.gcd_assoc]

theorem rankTwoContent_dvd_entry (A : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) :
    A.rankTwoContent ∣ (A i j).natAbs :=
  A.rankTwoContent_eq_finset_gcd ▸ Finset.gcd_dvd (Finset.mem_univ (i, j))

theorem dvd_rankTwoContent {A : Matrix (Fin 2) (Fin 2) ℤ} {k : ℕ}
    (h : ∀ i j, k ∣ (A i j).natAbs) : k ∣ A.rankTwoContent :=
  A.rankTwoContent_eq_finset_gcd ▸ Finset.dvd_gcd fun p _ ↦ h p.1 p.2

/-- The content of an integer matrix divides the content of every right multiple. -/
theorem rankTwoContent_dvd_mul_right (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    A.rankTwoContent ∣ (A * B).rankTwoContent := by
  refine dvd_rankTwoContent fun i j ↦ ?_
  rw [← Int.natCast_dvd, Matrix.mul_apply, Fin.sum_univ_two]
  exact dvd_add
    (dvd_mul_of_dvd_left (Int.natCast_dvd.mpr (rankTwoContent_dvd_entry A i 0)) _)
    (dvd_mul_of_dvd_left (Int.natCast_dvd.mpr (rankTwoContent_dvd_entry A i 1)) _)

/-- The content of an integer matrix divides the content of every left multiple. -/
theorem rankTwoContent_dvd_mul_left (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    B.rankTwoContent ∣ (A * B).rankTwoContent := by
  refine dvd_rankTwoContent fun i j ↦ ?_
  rw [← Int.natCast_dvd, Matrix.mul_apply, Fin.sum_univ_two]
  exact dvd_add
    (dvd_mul_of_dvd_right (Int.natCast_dvd.mpr (rankTwoContent_dvd_entry B 0 j)) _)
    (dvd_mul_of_dvd_right (Int.natCast_dvd.mpr (rankTwoContent_dvd_entry B 1 j)) _)

/-- The content is invariant under unimodular column operations. -/
theorem rankTwoContent_mul_of_isUnit_det (A : Matrix (Fin 2) (Fin 2) ℤ)
    {U : Matrix (Fin 2) (Fin 2) ℤ} (hU : IsUnit U.det) :
    (A * U).rankTwoContent = A.rankTwoContent :=
  Nat.dvd_antisymm
    (by simpa [Matrix.mul_assoc, mul_nonsing_inv U hU] using
      rankTwoContent_dvd_mul_right (A * U) U⁻¹)
    (rankTwoContent_dvd_mul_right A U)

/-- The content is invariant under unimodular row operations. -/
theorem rankTwoContent_isUnit_det_mul {U : Matrix (Fin 2) (Fin 2) ℤ} (hU : IsUnit U.det)
    (A : Matrix (Fin 2) (Fin 2) ℤ) :
    (U * A).rankTwoContent = A.rankTwoContent :=
  Nat.dvd_antisymm
    (by simpa [← Matrix.mul_assoc, nonsing_inv_mul U hU] using
      rankTwoContent_dvd_mul_left U⁻¹ (U * A))
    (rankTwoContent_dvd_mul_left U A)

/-- The content of a rank-two column Hermite normal form, in the order of Cox's primitivity
condition `gcd(a, b, d) = 1`. -/
theorem IsColumnHermiteNormalForm.rankTwoContent_eq {A : Matrix (Fin 2) (Fin 2) ℤ}
    (h : A.IsColumnHermiteNormalForm) :
    A.rankTwoContent = Nat.gcd (Nat.gcd (A 1 1).natAbs (A 0 1).natAbs) (A 0 0).natAbs := by
  rw [rankTwoContent, h.one_zero, Int.natAbs_zero, Nat.gcd_zero_right]
  ac_rfl

private lemma exists_unit_mul_pos_aux (x : ℤ) (hx : x ≠ 0) :
    ∃ s : ℤ, IsUnit s ∧ 0 < x * s := by
  by_cases h : 0 < x
  · exact ⟨1, isUnit_one, by simpa using h⟩
  · refine ⟨-1, isUnit_neg_one, ?_⟩
    simp only [mul_neg, mul_one]
    omega

private lemma hnf_transform_det_aux (cg dg u v q s : ℤ) (h : cg * u + dg * v = 1) :
    Matrix.det !![dg * s, u - q * (dg * s); -(cg * s), v + q * (cg * s)] = s := by
  rw [Matrix.det_fin_two_of]
  linear_combination s * h

private lemma hnf_transform_mul_aux (a b c d cg dg u v q r g s : ℤ)
    (hcg : cg * g = c) (hdg : dg * g = d) (hbezout : g = c * u + d * v)
    (her : r + ((a * dg - b * cg) * s) * q = a * u + b * v) :
    !![a, b; c, d] * !![dg * s, u - q * (dg * s); -(cg * s), v + q * (cg * s)] =
      !![(a * dg - b * cg) * s, r; 0, g] := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp
  · ring
  · linear_combination -her
  · linear_combination s * (cg * hdg - dg * hcg)
  · linear_combination -hbezout + q * s * (dg * hcg - cg * hdg)

private theorem exists_hnf_transform (a b c d : ℤ) (hdet : a * d - b * c ≠ 0) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℤ, IsUnit B.det ∧
      (!![a, b; c, d] * B).IsColumnHermiteNormalForm := by
  let g : ℤ := c.gcd d
  have hcd : c ≠ 0 ∨ d ≠ 0 := by grind
  have hgpos : 0 < g := by
    dsimp [g]
    exact_mod_cast hcd.elim (fun hc ↦ Int.gcd_pos_of_ne_zero_left d hc)
      (fun hd ↦ Int.gcd_pos_of_ne_zero_right c hd)
  have hg0 : g ≠ 0 := ne_of_gt hgpos
  let cg : ℤ := c / g
  let dg : ℤ := d / g
  have hcg : cg * g = c := Int.ediv_mul_cancel (by simpa [g] using Int.gcd_dvd_left c d)
  have hdg : dg * g = d := Int.ediv_mul_cancel (by simpa [g] using Int.gcd_dvd_right c d)
  let u : ℤ := c.gcdA d
  let v : ℤ := c.gcdB d
  have hbezout : g = c * u + d * v := by
    simpa [g, u, v] using Int.gcd_eq_gcd_ab c d
  have huv : cg * u + dg * v = 1 := by
    apply mul_left_cancel₀ hg0
    linear_combination u * hcg + v * hdg - hbezout
  let pivot : ℤ := a * dg - b * cg
  have hdet_pivot : pivot * g = a * d - b * c := by
    dsimp [pivot]
    linear_combination a * hdg - b * hcg
  have hpivot0 : pivot ≠ 0 := left_ne_zero_of_mul (hdet_pivot ▸ hdet)
  obtain ⟨s, hsunit, hpositivePivot⟩ := exists_unit_mul_pos_aux pivot hpivot0
  let positivePivot : ℤ := pivot * s
  change 0 < positivePivot at hpositivePivot
  let e : ℤ := a * u + b * v
  let q : ℤ := e / positivePivot
  let r : ℤ := e % positivePivot
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hpositivePivot)
  have hrp : r < positivePivot := Int.emod_lt_of_pos _ hpositivePivot
  have her : r + positivePivot * q = e := by
    simpa [r, q] using Int.emod_add_mul_ediv e positivePivot
  let B : Matrix (Fin 2) (Fin 2) ℤ :=
    !![dg * s, u - q * (dg * s); -(cg * s), v + q * (cg * s)]
  have hBdet : B.det = s := hnf_transform_det_aux cg dg u v q s huv
  have hmul : !![a, b; c, d] * B = !![positivePivot, r; 0, g] := by
    simpa only [B, positivePivot, pivot, e] using
      hnf_transform_mul_aux a b c d cg dg u v q r g s hcg hdg hbezout her
  refine ⟨B, ?_, ?_⟩
  · rw [hBdet]
    exact hsunit
  · rw [hmul]
    exact isColumnHermiteNormalForm_fin_two hpositivePivot hgpos hr0 hrp

/-- Every nonsingular two-by-two integer matrix can be brought to column Hermite normal form
by a unimodular change of columns. -/
theorem exists_right_mul_isColumnHermiteNormalForm
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det ≠ 0) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℤ, IsUnit B.det ∧
      (A * B).IsColumnHermiteNormalForm := by
  simpa only [← Matrix.eta_fin_two A] using
    exists_hnf_transform (A 0 0) (A 0 1) (A 1 0) (A 1 1)
      (by simpa only [Matrix.det_fin_two] using hdet)

/-- A positive-determinant two-by-two integer matrix can be brought to column Hermite normal
form by right multiplication by an element of `SL₂(ℤ)`. -/
theorem exists_right_mul_SL2_isColumnHermiteNormalForm
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : 0 < A.det) :
    ∃ U : SL(2, ℤ), (A * U.1).IsColumnHermiteNormalForm := by
  obtain ⟨B, hBunit, hH⟩ := exists_right_mul_isColumnHermiteNormalForm A hdet.ne'
  refine ⟨⟨B, (Int.isUnit_iff.mp hBunit).resolve_right fun hB ↦ ?_⟩, hH⟩
  have := hH.det_pos
  rw [det_mul, hB] at this
  linarith

/-- Two elements of `[0, d)` that are congruent modulo `d` are equal. -/
private lemma eq_of_mem_Ico_of_mul_add_eq {d r r' q : ℤ} (hr : r ∈ Set.Ico 0 d)
    (hr' : r' ∈ Set.Ico 0 d) (e : d * q + r = r') : r = r' := by
  calc
    r = r % d := (Int.emod_eq_of_lt hr.1 hr.2).symm
    _ = r' % d := by rw [← e]; simp [Int.add_emod]
    _ = r' := Int.emod_eq_of_lt hr'.1 hr'.2

/-- Uniqueness of the rank-two column Hermite normal form: two column HNF matrices which differ
by a unimodular change of columns are equal. -/
theorem IsColumnHermiteNormalForm.eq_of_mul_isUnit_det {A B U : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : A.IsColumnHermiteNormalForm) (hB : B.IsColumnHermiteNormalForm)
    (hU : IsUnit U.det) (hmul : A * U = B) : A = B := by
  have e (i j : Fin 2) : B i j = A i 0 * U 0 j + A i 1 * U 1 j := by
    rw [← hmul, mul_apply, Fin.sum_univ_two]
  have hU10 : U 1 0 = 0 := by
    have h := e 1 0
    rw [hA.one_zero, hB.one_zero, zero_mul, zero_add, eq_comm, mul_eq_zero] at h
    exact h.resolve_left hA.one_one_pos.ne'
  have e00 : B 0 0 = A 0 0 * U 0 0 := by simpa [hU10] using e 0 0
  have e11 : B 1 1 = A 1 1 * U 1 1 := by simpa [hA.one_zero] using e 1 1
  have hU00 : 0 < U 0 0 := pos_of_mul_pos_right (e00 ▸ hB.zero_zero_pos) hA.zero_zero_pos.le
  have hU11 : 0 < U 1 1 := pos_of_mul_pos_right (e11 ▸ hB.one_one_pos) hA.one_one_pos.le
  have hdet : U 0 0 * U 1 1 = 1 := by
    rcases Int.isUnit_iff.mp hU with h | h <;>
      rw [det_fin_two, hU10, mul_zero, sub_zero] at h
    · exact h
    · nlinarith
  have h00 : U 0 0 = 1 := Int.eq_one_of_mul_eq_one_right hU00.le hdet
  have h11 : U 1 1 = 1 := Int.eq_one_of_mul_eq_one_left hU11.le hdet
  have h01 : A 0 1 = B 0 1 :=
    eq_of_mem_Ico_of_mul_add_eq (q := U 0 1) hA.zero_one_mem
      (by simpa [e00, h00] using hB.zero_one_mem) (by rw [e 0 1, h11, mul_one])
  rw [hA.eq_fin_two, hB.eq_fin_two, e00, e11, h00, h11, h01, mul_one, mul_one]

/-- The anti-transpose `!![d, b; c, a]` of `!![a, b; c, d]`, i.e. the reflection of a
two-by-two matrix in its anti-diagonal.  It reverses products and preserves determinants, and
it exchanges column operations with row operations. -/
def antiTranspose {α : Type*} (A : Matrix (Fin 2) (Fin 2) α) : Matrix (Fin 2) (Fin 2) α :=
  !![A 1 1, A 0 1; A 1 0, A 0 0]

section antiTranspose

variable {α : Type*}

theorem antiTranspose_eq_submatrix_transpose (A : Matrix (Fin 2) (Fin 2) α) :
    A.antiTranspose = (A.submatrix Fin.revPerm Fin.revPerm)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp]
theorem antiTranspose_antiTranspose (A : Matrix (Fin 2) (Fin 2) α) :
    A.antiTranspose.antiTranspose = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem antiTranspose_mul [CommSemiring α] (A B : Matrix (Fin 2) (Fin 2) α) :
    (A * B).antiTranspose = B.antiTranspose * A.antiTranspose := by
  simp only [antiTranspose_eq_submatrix_transpose, ← transpose_mul, submatrix_mul_equiv]

@[simp]
theorem det_antiTranspose [CommRing α] (A : Matrix (Fin 2) (Fin 2) α) :
    A.antiTranspose.det = A.det := by
  rw [antiTranspose_eq_submatrix_transpose, det_transpose, det_submatrix_equiv_self]

theorem rankTwoContent_antiTranspose (A : Matrix (Fin 2) (Fin 2) ℤ) :
    A.antiTranspose.rankTwoContent = A.rankTwoContent := by
  simp only [antiTranspose, rankTwoContent_fin_two_of]
  unfold rankTwoContent
  ac_rfl

end antiTranspose

/-- The content of the adjugate of a two-by-two integer matrix is its content. -/
theorem rankTwoContent_adjugate (A : Matrix (Fin 2) (Fin 2) ℤ) :
    A.adjugate.rankTwoContent = A.rankTwoContent := by
  simp only [adjugate_fin_two, rankTwoContent_fin_two_of, Int.natAbs_neg]
  unfold rankTwoContent
  ac_rfl

/-- Every positive-determinant two-by-two integer matrix is left `SL₂(ℤ)`-equivalent to an
upper-triangular matrix `!![a, b; 0, d]` with `0 < a`, `0 < d` and `0 ≤ b < d`. -/
theorem exists_SL2_mul_eq_upperTriangular (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : 0 < M.det) :
    ∃ (γ : SL(2, ℤ)) (a b d : ℤ), 0 < a ∧ 0 < d ∧ b ∈ Set.Ico 0 d ∧ a * d = M.det ∧
      γ.1 * M = !![a, b; 0, d] := by
  obtain ⟨U, hU⟩ :=
    exists_right_mul_SL2_isColumnHermiteNormalForm M.antiTranspose (by simpa using hdet)
  refine ⟨⟨U.1.antiTranspose, by simp⟩, _, _, _, hU.one_one_pos, hU.zero_zero_pos,
    hU.zero_one_mem, ?_, ?_⟩
  · rw [mul_comm, ← hU.det_eq, det_mul, det_antiTranspose, SpecialLinearGroup.det_coe, mul_one]
  · rw [← antiTranspose_antiTranspose M, ← antiTranspose_mul, hU.eq_fin_two]
    rfl

/-- Nonsingular square matrices over a domain induce injective linear maps. -/
theorem toLin_injective_iff_det_ne_zero {R M₁ M₂ n : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [IsDomain R] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]
    (v₁ : Basis n R M₁) (v₂ : Basis n R M₂) {A : Matrix n n R} :
    Function.Injective (toLin v₁ v₂ A) ↔ A.det ≠ 0 := by
  rw [Ne, ← exists_mulVec_eq_zero_iff, injective_iff_map_eq_zero]
  simp only [toLin_apply_eq_zero_iff, not_exists, not_and]
  have hrepr (v : n → R) : ⇑(v₁.repr (v₁.equivFun.symm v)) = v := by
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨fun h v hv hAv ↦ hv ?_, fun h x hx ↦ by_contra fun hx0 ↦ h _ ?_ (funext hx)⟩
  · exact (LinearEquiv.map_eq_zero_iff _).mp
      (h (v₁.equivFun.symm v) (by rw [hrepr]; exact congrFun hAv))
  · simpa [← Basis.equivFun_apply] using hx0

end Matrix

namespace Matrix.SpecialLinearGroup

variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]

theorem mul_coe_mul_coe_inv (A : Matrix n n R) (U : SpecialLinearGroup n R) :
    A * U.1 * (U⁻¹ : SpecialLinearGroup n R).1 = A := by
  rw [Matrix.mul_assoc, ← coe_mul, mul_inv_cancel, coe_one, Matrix.mul_one]

theorem coe_mul_coe_inv_mul (U : SpecialLinearGroup n R) (A : Matrix n n R) :
    U.1 * ((U⁻¹ : SpecialLinearGroup n R).1 * A) = A := by
  rw [← Matrix.mul_assoc, ← coe_mul, mul_inv_cancel, coe_one, Matrix.one_mul]

end Matrix.SpecialLinearGroup

namespace Module.Basis

variable {M : Type*} [AddCommGroup M]

/-- A Hermite-normal-form basis for `N ≤ M` relative to the fixed ambient basis `bM`,
parallel to `Module.Basis.SmithNormalForm` but recording the full inclusion matrix. -/
structure HermiteNormalForm {n : ℕ} (bM : Basis (Fin n) ℤ M)
    (N : Submodule ℤ M) where
  /-- The basis of the submodule. -/
  bN : Basis (Fin n) ℤ N
  /-- The matrix of `N.subtype` from `bN` to the fixed ambient basis `bM`. -/
  matrix : Matrix (Fin n) (Fin n) ℤ
  /-- The matrix really represents the inclusion `N ↪ M`. -/
  toMatrix_eq : LinearMap.toMatrix bN bM N.subtype = matrix
  /-- The inclusion matrix is in column Hermite normal form. -/
  isColumnHermiteNormalForm : matrix.IsColumnHermiteNormalForm

namespace HermiteNormalForm

variable {n : ℕ} {bM : Basis (Fin n) ℤ M} {N : Submodule ℤ M}

/-- Coordinates of an HNF submodule basis vector in the ambient basis. -/
@[simp]
theorem repr_apply (h : HermiteNormalForm bM N) (i j : Fin n) :
    bM.repr (h.bN j : M) i = h.matrix i j := by
  rw [← h.toMatrix_eq, LinearMap.toMatrix_apply, Submodule.subtype_apply]

/-- The ambient coordinates of an element of `N` are the HNF matrix applied to its
coordinates in the HNF basis. -/
theorem repr_eq_mulVec (h : HermiteNormalForm bM N) (y : N) :
    ⇑(bM.repr (y : M)) = h.matrix.mulVec ⇑(h.bN.repr y) := by
  rw [← h.toMatrix_eq, LinearMap.toMatrix_mulVec_repr, Submodule.subtype_apply]

/-- Cramer's rule for an HNF basis: multiplying the HNF coordinates of `y ∈ N` by the
determinant gives the adjugate applied to its ambient coordinates. -/
theorem det_smul_repr (h : HermiteNormalForm bM N) (y : N) :
    h.matrix.det • ⇑(h.bN.repr y) = h.matrix.adjugate.mulVec ⇑(bM.repr (y : M)) := by
  rw [h.repr_eq_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec]

/-- The column space of an HNF inclusion matrix, interpreted in the ambient basis, is exactly
the represented submodule. -/
theorem range_toLin_matrix_eq (h : HermiteNormalForm bM N) :
    LinearMap.range (Matrix.toLin bM bM h.matrix) = N := by
  let e : M ≃ₗ[ℤ] N := bM.equiv h.bN (Equiv.refl (Fin n))
  have hfg : Matrix.toLin bM bM h.matrix = N.subtype.comp e.toLinearMap := by
    apply (LinearMap.toMatrix bM bM).injective
    rw [LinearMap.toMatrix_toLin, LinearMap.toMatrix_comp bM h.bN bM,
      LinearMap.toMatrix_basis_equiv, h.toMatrix_eq, Matrix.mul_one]
  rw [hfg, e.range_comp, Submodule.range_subtype]

/-- The HNF of the column space of an injective column-HNF matrix map. -/
def ofToLin {K : Type*} [AddCommGroup K] (bK : Basis (Fin n) ℤ K)
    {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsColumnHermiteNormalForm)
    (hf : Function.Injective (Matrix.toLin bK bM A)) :
    HermiteNormalForm bM (LinearMap.range (Matrix.toLin bK bM A)) where
  bN := bK.map (LinearEquiv.ofInjective _ hf)
  matrix := A
  toMatrix_eq := by
    rw [LinearMap.toMatrix_map_left]
    exact LinearMap.toMatrix_toLin _ _ _
  isColumnHermiteNormalForm := hA

@[simp]
theorem ofToLin_matrix {K : Type*} [AddCommGroup K] (bK : Basis (Fin n) ℤ K)
    {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsColumnHermiteNormalForm)
    (hf : Function.Injective (Matrix.toLin bK bM A)) :
    (ofToLin bK hA hf).matrix = A :=
  rfl

/-- The index of a full-rank HNF submodule is the absolute determinant of its inclusion
matrix (Cox, Exercise 7.15 in the rank-two case). -/
theorem index_eq_natAbs_det (h : HermiteNormalForm bM N) :
    N.toAddSubgroup.index = h.matrix.det.natAbs := by
  rw [AddSubgroup.index_eq_natAbs_det bM N.toAddSubgroup h.bN, Basis.det_apply]
  apply congrArg (Int.natAbs ∘ Matrix.det)
  ext i j
  exact h.repr_apply i j

/-- The determinant of an HNF inclusion matrix is the index of the submodule. -/
theorem det_eq_index (h : HermiteNormalForm bM N) :
    h.matrix.det = N.toAddSubgroup.index := by
  rw [h.index_eq_natAbs_det, Int.natCast_natAbs, abs_of_pos h.isColumnHermiteNormalForm.det_pos]

variable {bM : Basis (Fin 2) ℤ M}

private lemma matrix_mul_toMatrix_eq (h h' : HermiteNormalForm bM N) :
    h.matrix * h.bN.toMatrix h'.bN = h'.matrix := by
  rw [← h.toMatrix_eq, ← h'.toMatrix_eq]
  exact linearMap_toMatrix_mul_basis_toMatrix h'.bN h.bN bM N.subtype

/-- In rank two, the HNF matrix of a fixed submodule relative to a fixed ambient basis is
unique. -/
theorem matrix_eq (h h' : HermiteNormalForm bM N) : h.matrix = h'.matrix :=
  h.isColumnHermiteNormalForm.eq_of_mul_isUnit_det h'.isColumnHermiteNormalForm
    (Matrix.isUnit_det_of_right_inverse (h.bN.toMatrix_mul_toMatrix_flip h'.bN))
    (matrix_mul_toMatrix_eq h h')

/-- In rank two, the submodule basis occurring in HNF is unique as well. -/
theorem bN_eq (h h' : HermiteNormalForm bM N) : h.bN = h'.bN := by
  refine DFunLike.ext _ _ fun j ↦ Subtype.ext <| bM.repr.injective <| Finsupp.ext fun i ↦ ?_
  rw [h.repr_apply, h'.repr_apply, h.matrix_eq h']

/-- In rank two, the quotient is cyclic exactly when its inclusion matrix in any two chosen
bases is primitive (Cox, Exercise 11.16). -/
theorem quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one
    (bM : Basis (Fin 2) ℤ M) (N : Submodule ℤ M) (bN : Basis (Fin 2) ℤ N) :
    IsAddCyclic (M ⧸ N) ↔
      Matrix.rankTwoContent (LinearMap.toMatrix bN bM N.subtype) = 1 := by
  let A := LinearMap.toMatrix bN bM N.subtype
  have hRank : Module.finrank ℤ N = Module.finrank ℤ M := by
    rw [Module.finrank_eq_card_basis bN, Module.finrank_eq_card_basis bM]
  let bS : Basis (Fin 2) ℤ M := N.smithNormalFormTopBasis bM hRank
  let bNS : Basis (Fin 2) ℤ N := N.smithNormalFormBotBasis bM hRank
  let c : Fin 2 → ℤ := N.smithNormalFormCoeffs bM hRank
  let D : Matrix (Fin 2) (Fin 2) ℤ := Matrix.diagonal c
  have hD : LinearMap.toMatrix bNS bS N.subtype = D := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    by_cases hij : i = j <;>
      simp [bNS, bS, c, D, Submodule.smithNormalFormBotBasis_def, hij]
  have hDA : bS.toMatrix bM * A * bN.toMatrix bNS = D := by
    rw [← hD]
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bNS bN bS bM N.subtype
  have hcontent : A.rankTwoContent = Nat.gcd (c 0).natAbs (c 1).natAbs := by
    rw [← Matrix.rankTwoContent_isUnit_det_mul
        (Matrix.isUnit_det_of_right_inverse (bS.toMatrix_mul_toMatrix_flip bM)),
      ← Matrix.rankTwoContent_mul_of_isUnit_det _
        (Matrix.isUnit_det_of_right_inverse (bN.toMatrix_mul_toMatrix_flip bNS)), hDA]
    simp [D, Matrix.rankTwoContent]
  let e := N.quotientEquivPiZMod bM hRank
  let ep := (RingEquiv.piFinTwo fun i ↦ ZMod (c i).natAbs).toAddEquiv
  rw [e.isAddCyclic, ep.isAddCyclic, AddGroup.isAddCyclic_prod_iff]
  have hc0 : IsAddCyclic (ZMod (c 0).natAbs) := inferInstance
  have hc1 : IsAddCyclic (ZMod (c 1).natAbs) := inferInstance
  simp only [hc0, hc1, true_and, Nat.card_zmod, Nat.coprime_iff_gcd_eq_one]
  change Nat.gcd (c 0).natAbs (c 1).natAbs = 1 ↔ A.rankTwoContent = 1
  rw [hcontent]

/-- In rank two, the quotient is cyclic exactly when the entries of its HNF inclusion matrix
are primitive. -/
theorem quotient_isAddCyclic_iff_rankTwoContent_eq_one
    {bM : Basis (Fin 2) ℤ M} {N : Submodule ℤ M}
    (h : HermiteNormalForm bM N) :
    IsAddCyclic (M ⧸ N) ↔ Matrix.rankTwoContent h.matrix = 1 := by
  simpa only [h.toMatrix_eq] using
    quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one bM N h.bN

end HermiteNormalForm

end Module.Basis

namespace Submodule

variable {M : Type*} [AddCommGroup M]

/-- Every full-rank rank-two integer submodule admits an HNF basis relative to a fixed
ambient basis. -/
theorem exists_hermiteNormalForm (bM : Basis (Fin 2) ℤ M)
    (N : Submodule ℤ M) (hN : Module.finrank ℤ N = 2) :
    Nonempty (Module.Basis.HermiteNormalForm bM N) := by
  letI : Module.Free ℤ M := Module.Free.of_basis bM
  letI : Module.Finite ℤ M := Module.Finite.of_basis bM
  let bN₀ : Basis (Fin 2) ℤ N := hN ▸ Module.finBasis ℤ N
  let A : Matrix (Fin 2) (Fin 2) ℤ := LinearMap.toMatrix bN₀ bM N.subtype
  have hAdet : A.det ≠ 0 :=
    (Matrix.toLin_injective_iff_det_ne_zero bN₀ bM).mp <| by
      simpa only [A, Matrix.toLin_toMatrix] using N.subtype_injective
  obtain ⟨B, hBunit, hAB⟩ :=
    Matrix.exists_right_mul_isColumnHermiteNormalForm A hAdet
  let bN : Basis (Fin 2) ℤ N := bN₀.map (Matrix.toLinearEquiv bN₀ B hBunit)
  have hrelation : LinearMap.toMatrix bN bM N.subtype = A * B := by
    rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_comp bN₀ bN₀ bM]
    congr 1
    exact LinearMap.toMatrix_toLin bN₀ bN₀ B
  exact ⟨⟨bN, A * B, hrelation, hAB⟩⟩

/-- The canonical HNF chosen from `exists_hermiteNormalForm`. -/
noncomputable def hermiteNormalForm (bM : Basis (Fin 2) ℤ M)
    (N : Submodule ℤ M) (hN : Module.finrank ℤ N = 2) :
    Module.Basis.HermiteNormalForm bM N :=
  Classical.choice (N.exists_hermiteNormalForm bM hN)

end Submodule
