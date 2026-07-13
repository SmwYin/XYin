/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Algebra.Ring.Fin
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Hermite normal form for full-rank integer submodules

This file develops the Hermite-normal-form API needed in Cox, Chapter 11.  Unlike Smith normal
form, Hermite normal form is canonical only after fixing the ambient basis, so that basis is an
explicit parameter of `Module.Basis.HermiteNormalForm`.  The bundled definition is available in
arbitrary finite rank; the constructive existence theorem currently supplies the rank-two case
used by Cox.
-/

open Module

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

/-- The gcd of the four entries of a two-by-two integer matrix. -/
def rankTwoContent (A : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  Nat.gcd (Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
    (A 1 0).natAbs) (A 1 1).natAbs

private lemma rankTwoContent_dvd_entry (A : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) :
    A.rankTwoContent ∣ (A i j).natAbs := by
  fin_cases i <;> fin_cases j
  · change A.rankTwoContent ∣ (A 0 0).natAbs
    exact (Nat.gcd_dvd_left _ _).trans
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
  · change A.rankTwoContent ∣ (A 0 1).natAbs
    exact (Nat.gcd_dvd_left _ _).trans
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
  · change A.rankTwoContent ∣ (A 1 0).natAbs
    exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  · change A.rankTwoContent ∣ (A 1 1).natAbs
    exact Nat.gcd_dvd_right _ _

private lemma dvd_rankTwoContent {A : Matrix (Fin 2) (Fin 2) ℤ} {k : ℕ}
    (h : ∀ i j, k ∣ (A i j).natAbs) : k ∣ A.rankTwoContent :=
  Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (h 0 0) (h 0 1)) (h 1 0)) (h 1 1)

private lemma rankTwoContent_dvd_mul_right (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    A.rankTwoContent ∣ (A * B).rankTwoContent := by
  apply dvd_rankTwoContent
  intro i j
  rw [← Int.natCast_dvd, Matrix.mul_apply, Fin.sum_univ_two]
  exact dvd_add
    (dvd_mul_of_dvd_left (Int.natCast_dvd.mpr (rankTwoContent_dvd_entry A i 0)) _)
    (dvd_mul_of_dvd_left (Int.natCast_dvd.mpr (rankTwoContent_dvd_entry A i 1)) _)

private lemma rankTwoContent_dvd_mul_left (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    B.rankTwoContent ∣ (A * B).rankTwoContent := by
  apply dvd_rankTwoContent
  intro i j
  rw [← Int.natCast_dvd, Matrix.mul_apply, Fin.sum_univ_two]
  exact dvd_add
    (dvd_mul_of_dvd_right (Int.natCast_dvd.mpr (rankTwoContent_dvd_entry B 0 j)) _)
    (dvd_mul_of_dvd_right (Int.natCast_dvd.mpr (rankTwoContent_dvd_entry B 1 j)) _)

/-- The defining inequalities for a rank-two column HNF matrix. -/
theorem isColumnHermiteNormalForm_fin_two {d r a : ℤ} (hd : 0 < d) (ha : 0 < a)
    (hr0 : 0 ≤ r) (hrd : r < d) :
    IsColumnHermiteNormalForm !![d, r; 0, a] := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hji
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i <;> simp_all
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Set.mem_Ico]

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
  calc
    dg * s * (v + q * (cg * s)) - (u - q * (dg * s)) * -(cg * s) =
        s * (cg * u + dg * v) := by ring
    _ = s := by rw [h, mul_one]

private lemma hnf_transform_mul_aux (a b c d cg dg u v q r g s : ℤ)
    (hcg : cg * g = c) (hdg : dg * g = d) (hbezout : g = c * u + d * v)
    (her : r + ((a * dg - b * cg) * s) * q = a * u + b * v) :
    !![a, b; c, d] * !![dg * s, u - q * (dg * s); -(cg * s), v + q * (cg * s)] =
      !![(a * dg - b * cg) * s, r; 0, g] := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · change a * (dg * s) + b * -(cg * s) = (a * dg - b * cg) * s
    ring
  · change a * (u - q * (dg * s)) + b * (v + q * (cg * s)) = r
    calc
      a * (u - q * (dg * s)) + b * (v + q * (cg * s)) =
          a * u + b * v - q * ((a * dg - b * cg) * s) := by ring
      _ = r := by rw [← her]; ring
  · change c * (dg * s) + d * -(cg * s) = 0
    rw [← hcg, ← hdg]
    ring
  · change c * (u - q * (dg * s)) + d * (v + q * (cg * s)) = g
    rw [hbezout, ← hcg, ← hdg]
    ring

private theorem exists_hnf_transform (a b c d : ℤ) (hdet : a * d - b * c ≠ 0) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℤ, IsUnit B.det ∧
      (!![a, b; c, d] * B).IsColumnHermiteNormalForm := by
  let g : ℤ := c.gcd d
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_cases hc : c = 0
    · exact Or.inr fun hd ↦ hdet <| by simp [hc, hd]
    · exact Or.inl hc
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
    rw [mul_one]
    calc
      g * (cg * u + dg * v) = (cg * g) * u + (dg * g) * v := by ring
      _ = c * u + d * v := by rw [hcg, hdg]
      _ = g := hbezout.symm
  let pivot : ℤ := a * dg - b * cg
  have hdet_pivot : pivot * g = a * d - b * c := by
    dsimp [pivot]
    calc
      (a * dg - b * cg) * g = a * (dg * g) - b * (cg * g) := by ring
      _ = a * d - b * c := by rw [hdg, hcg]
  have hpivot0 : pivot ≠ 0 := by
    exact fun h ↦ hdet <| by rw [← hdet_pivot, h, zero_mul]
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
  have hBdet : B.det = s := by
    exact hnf_transform_det_aux cg dg u v q s huv
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
  have hA : !![A 0 0, A 0 1; A 1 0, A 1 1] = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [← hA] at hdet ⊢
  rw [Matrix.det_fin_two_of] at hdet
  exact exists_hnf_transform _ _ _ _ hdet

end Matrix

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
    bM.repr (N.subtype (h.bN j)) i = h.matrix i j := by
  rw [← h.toMatrix_eq, LinearMap.toMatrix_apply]

/-- The column space of an HNF inclusion matrix, interpreted in the ambient basis, is exactly
the represented submodule. -/
theorem range_toLin_matrix_eq (h : HermiteNormalForm bM N) :
    LinearMap.range (Matrix.toLin bM bM h.matrix) = N := by
  let e : M ≃ₗ[ℤ] N := bM.equiv h.bN (Equiv.refl (Fin n))
  let f : M →ₗ[ℤ] M := Matrix.toLin bM bM h.matrix
  let g : M →ₗ[ℤ] M := N.subtype.comp e.toLinearMap
  have hfg : f = g := by
    apply (LinearMap.toMatrix bM bM).injective
    rw [show LinearMap.toMatrix bM bM f = h.matrix by
      exact LinearMap.toMatrix_toLin _ _ _]
    rw [show LinearMap.toMatrix bM bM g =
        LinearMap.toMatrix h.bN bM N.subtype *
          LinearMap.toMatrix bM h.bN e.toLinearMap by
      exact LinearMap.toMatrix_comp _ _ _ _ _]
    rw [show LinearMap.toMatrix bM h.bN e.toLinearMap = 1 by
      exact LinearMap.toMatrix_basis_equiv h.bN bM]
    simp only [h.toMatrix_eq, Matrix.mul_one]
  change LinearMap.range f = N
  rw [hfg]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (e y).property
  · intro hx
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    simp [g]

variable {bM : Basis (Fin 2) ℤ M} {N : Submodule ℤ M}

private lemma matrix_mul_toMatrix_eq (h h' : HermiteNormalForm bM N) :
    h.matrix * h.bN.toMatrix h'.bN = h'.matrix := by
  rw [← h.toMatrix_eq, ← h'.toMatrix_eq]
  exact linearMap_toMatrix_mul_basis_toMatrix h'.bN h.bN bM N.subtype

private lemma reduced_eq_of_eq_add_mul {d r r' q : ℤ} (hr : r ∈ Set.Ico 0 d)
    (hr' : r' ∈ Set.Ico 0 d) (e : d * q + r = r') : r = r' := by
  calc
    r = r % d := (Int.emod_eq_of_lt hr.1 hr.2).symm
    _ = r' % d := by rw [← e]; simp [Int.add_emod]
    _ = r' := Int.emod_eq_of_lt hr'.1 hr'.2

/-- In rank two, the HNF matrix of a fixed submodule relative to a fixed ambient basis is
unique. -/
theorem matrix_eq (h h' : HermiteNormalForm bM N) : h.matrix = h'.matrix := by
  let U : Matrix (Fin 2) (Fin 2) ℤ := h.bN.toMatrix h'.bN
  let V : Matrix (Fin 2) (Fin 2) ℤ := h'.bN.toMatrix h.bN
  have hmul : h.matrix * U = h'.matrix := matrix_mul_toMatrix_eq h h'
  have hmul' : h'.matrix * V = h.matrix := matrix_mul_toMatrix_eq h' h
  have hz := h.isColumnHermiteNormalForm.belowDiagonal_eq_zero 1 0 (by omega)
  have hz' := h'.isColumnHermiteNormalForm.belowDiagonal_eq_zero 1 0 (by omega)
  have hd := h.isColumnHermiteNormalForm.diagonal_pos 0
  have hd' := h'.isColumnHermiteNormalForm.diagonal_pos 0
  have ha := h.isColumnHermiteNormalForm.diagonal_pos 1
  have ha' := h'.isColumnHermiteNormalForm.diagonal_pos 1
  have hr := h.isColumnHermiteNormalForm.reduced 0 1 (by omega)
  have hr' := h'.isColumnHermiteNormalForm.reduced 0 1 (by omega)
  have hu10 : U 1 0 = 0 := by
    have e : h.matrix 1 1 * U 1 0 = 0 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hz, hz', zero_mul, zero_add] using
        congrFun (congrFun hmul 1) 0
    exact (mul_eq_zero.mp e).resolve_left (ne_of_gt ha)
  have hv10 : V 1 0 = 0 := by
    have e : h'.matrix 1 1 * V 1 0 = 0 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hz, hz', zero_mul, zero_add] using
        congrFun (congrFun hmul' 1) 0
    exact (mul_eq_zero.mp e).resolve_left (ne_of_gt ha')
  have haa' : h.matrix 1 1 = h'.matrix 1 1 := by
    have e : h.matrix 1 1 * U 1 1 = h'.matrix 1 1 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hz, zero_mul, zero_add] using
        congrFun (congrFun hmul 1) 1
    have e' : h'.matrix 1 1 * V 1 1 = h.matrix 1 1 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hz', zero_mul, zero_add] using
        congrFun (congrFun hmul' 1) 1
    exact le_antisymm (Int.le_of_dvd ha' ⟨U 1 1, e.symm⟩)
      (Int.le_of_dvd ha ⟨V 1 1, e'.symm⟩)
  have hu11 : U 1 1 = 1 := by
    have e : h.matrix 1 1 * U 1 1 = h'.matrix 1 1 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hz, zero_mul, zero_add] using
        congrFun (congrFun hmul 1) 1
    apply mul_left_cancel₀ (ne_of_gt ha')
    simpa only [haa', mul_one] using e
  have hdd' : h.matrix 0 0 = h'.matrix 0 0 := by
    have e : h.matrix 0 0 * U 0 0 = h'.matrix 0 0 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hu10, mul_zero, add_zero] using
        congrFun (congrFun hmul 0) 0
    have e' : h'.matrix 0 0 * V 0 0 = h.matrix 0 0 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hv10, mul_zero, add_zero] using
        congrFun (congrFun hmul' 0) 0
    exact le_antisymm (Int.le_of_dvd hd' ⟨U 0 0, e.symm⟩)
      (Int.le_of_dvd hd ⟨V 0 0, e'.symm⟩)
  have hrr' : h.matrix 0 1 = h'.matrix 0 1 := by
    have e : h.matrix 0 0 * U 0 1 + h.matrix 0 1 = h'.matrix 0 1 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hu11, mul_one] using
        congrFun (congrFun hmul 0) 1
    exact reduced_eq_of_eq_add_mul hr (hdd' ▸ hr') e
  ext i j
  fin_cases i <;> fin_cases j
  · exact hdd'
  · exact hrr'
  · exact hz.trans hz'.symm
  · exact haa'

/-- In rank two, the submodule basis occurring in HNF is unique as well. -/
theorem bN_eq (h h' : HermiteNormalForm bM N) : h.bN = h'.bN := by
  apply DFunLike.ext _ _
  intro j
  apply Subtype.ext
  apply bM.repr.injective
  ext i
  change bM.repr (N.subtype (h.bN j)) i = bM.repr (N.subtype (h'.bN j)) i
  rw [h.repr_apply, h'.repr_apply, h.matrix_eq h']

variable {n : ℕ} {bM : Basis (Fin n) ℤ M} {N : Submodule ℤ M}

/-- The index of a full-rank HNF submodule is the absolute determinant of its inclusion
matrix (Cox, Exercise 7.15 in the rank-two case). -/
theorem index_eq_natAbs_det (h : HermiteNormalForm bM N) :
    N.toAddSubgroup.index = h.matrix.det.natAbs := by
  rw [AddSubgroup.index_eq_natAbs_det bM N.toAddSubgroup h.bN, Basis.det_apply]
  have hmatrix : bM.toMatrix (fun i ↦ (h.bN i : M)) = h.matrix := by
    rw [← h.toMatrix_eq]
    ext i j
    rw [Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    rfl
  exact congrArg Int.natAbs (congrArg Matrix.det hmatrix)

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
    by_cases hij : i = j
    · subst i
      simp [bNS, bS, c, D, Submodule.smithNormalFormBotBasis_def]
    · simp [bNS, bS, c, D, Submodule.smithNormalFormBotBasis_def, hij]
  have hDA : bS.toMatrix bM * A * bN.toMatrix bNS = D := by
    rw [show A = LinearMap.toMatrix bN bM N.subtype from rfl, ← hD]
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bNS bN bS bM
      N.subtype
  have hAD : bM.toMatrix bS * D * bNS.toMatrix bN = A := by
    rw [show A = LinearMap.toMatrix bN bM N.subtype from rfl, ← hD]
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bN bNS bM bS
      N.subtype
  have hcontent : A.rankTwoContent = Nat.gcd (c 0).natAbs (c 1).natAbs := by
    have hADvd : A.rankTwoContent ∣ D.rankTwoContent := by
      rw [← hDA]
      exact (Matrix.rankTwoContent_dvd_mul_left (bS.toMatrix bM) A).trans
        (Matrix.rankTwoContent_dvd_mul_right (bS.toMatrix bM * A)
          (bN.toMatrix bNS))
    have hDvdA : D.rankTwoContent ∣ A.rankTwoContent := by
      rw [← hAD]
      exact (Matrix.rankTwoContent_dvd_mul_left (bM.toMatrix bS) D).trans
        (Matrix.rankTwoContent_dvd_mul_right (bM.toMatrix bS * D) (bNS.toMatrix bN))
    have hcontentD : D.rankTwoContent = Nat.gcd (c 0).natAbs (c 1).natAbs := by
      simp [D, Matrix.rankTwoContent]
    rw [hcontentD] at hADvd hDvdA
    exact Nat.dvd_antisymm hADvd hDvdA
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
  let e : M ≃ₗ[ℤ] N := bM.equiv bN₀ (Equiv.refl (Fin 2))
  let f : M →ₗ[ℤ] M := N.subtype.comp e.toLinearMap
  have hf : Function.Injective f := N.subtype_injective.comp e.injective
  have hfdet : LinearMap.det f ≠ 0 := by
    intro hdet
    have hker : f.ker ≠ ⊥ := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet
    exact hker (LinearMap.ker_eq_bot.mpr hf)
  have hmatrix : LinearMap.toMatrix bM bM f = A := by
    rw [show f = N.subtype.comp e.toLinearMap from rfl,
      LinearMap.toMatrix_comp bM bN₀ bM]
    rw [show LinearMap.toMatrix bM bN₀ e.toLinearMap = 1 by
      exact LinearMap.toMatrix_basis_equiv bN₀ bM]
    simp [A]
  have hAdet : A.det ≠ 0 := by
    rw [← hmatrix, LinearMap.det_toMatrix]
    exact hfdet
  obtain ⟨B, hBunit, hAB⟩ :=
    Matrix.exists_right_mul_isColumnHermiteNormalForm A hAdet
  let eB : N ≃ₗ[ℤ] N := Matrix.toLinearEquiv bN₀ B hBunit
  let bN : Basis (Fin 2) ℤ N := bN₀.map eB
  have hrelation : LinearMap.toMatrix bN bM N.subtype = A * B := by
    rw [show bN = bN₀.map eB from rfl, LinearMap.toMatrix_map_left,
      LinearMap.toMatrix_comp bN₀ bN₀ bM]
    rw [show LinearMap.toMatrix bN₀ bM N.subtype = A from rfl]
    congr 1
    exact LinearMap.toMatrix_toLin bN₀ bN₀ B
  exact ⟨⟨bN, A * B, hrelation, hAB⟩⟩

/-- The canonical HNF chosen from `exists_hermiteNormalForm`. -/
noncomputable def hermiteNormalForm (bM : Basis (Fin 2) ℤ M)
    (N : Submodule ℤ M) (hN : Module.finrank ℤ N = 2) :
    Module.Basis.HermiteNormalForm bM N :=
  Classical.choice (N.exists_hermiteNormalForm bM hN)

end Submodule
