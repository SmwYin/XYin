/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.HermiteNormalForm
import XYin.PhD.Cox.ModularFunction

/-!
# Cox matrices and right cosets

This file defines Cox's primitive upper-triangular representatives and identifies them with
right cosets of `Γ₀(m)` in `SL₂(ℤ)`. It also develops the induced coset action on modular
functions.
-/

open Complex Function MatrixGroups UpperHalfPlane

noncomputable section

namespace Cox

/-- Cox's finite set `C(m)` of primitive upper-triangular determinant-`m` matrices. -/
structure CoxMatrix (m : ℕ+) where
  a : ℕ
  b : ℕ
  d : ℕ
  a_pos : 0 < a
  determinant : a * d = (m : ℕ)
  b_lt : b < d
  primitive : Nat.gcd (Nat.gcd a b) d = 1

namespace CoxMatrix

variable {m : ℕ+}

theorem d_pos (σ : CoxMatrix m) : 0 < σ.d := by
  have hm : 0 < σ.a * σ.d := by
    rw [σ.determinant]
    exact PNat.pos m
  exact pos_of_mul_pos_right hm (Nat.zero_le σ.a)

theorem a_le (σ : CoxMatrix m) : σ.a ≤ (m : ℕ) := by
  rw [← σ.determinant]
  exact Nat.le_mul_of_pos_right σ.a σ.d_pos

theorem d_le (σ : CoxMatrix m) : σ.d ≤ (m : ℕ) := by
  rw [← σ.determinant]
  exact Nat.le_mul_of_pos_left σ.d σ.a_pos

/-- Cox's matrix acting on the upper half-plane. -/
def mobiusMatrix (σ : CoxMatrix m) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(σ.a : ℤ), (σ.b : ℤ); 0, (σ.d : ℤ)]

/-- The column-HNF inclusion matrix for the associated sublattice `[d,aτ+b]`. -/
def inclusionMatrix (σ : CoxMatrix m) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(σ.d : ℤ), (σ.b : ℤ); 0, (σ.a : ℤ)]

theorem inclusionMatrix_isColumnHermiteNormalForm (σ : CoxMatrix m) :
    σ.inclusionMatrix.IsColumnHermiteNormalForm := by
  apply Matrix.isColumnHermiteNormalForm_fin_two
  · exact_mod_cast σ.d_pos
  · exact_mod_cast σ.a_pos
  · exact_mod_cast Nat.zero_le σ.b
  · exact_mod_cast σ.b_lt

theorem inclusionMatrix_det (σ : CoxMatrix m) :
    σ.inclusionMatrix.det = (m : ℕ) := by
  rw [inclusionMatrix, Matrix.det_fin_two_of]
  simp only [mul_zero, sub_zero]
  norm_cast
  rw [Nat.mul_comm, σ.determinant]

theorem inclusionMatrix_content_eq_one (σ : CoxMatrix m) :
    Matrix.rankTwoContent σ.inclusionMatrix = 1 := by
  simpa [inclusionMatrix, Matrix.rankTwoContent, Nat.gcd_comm, Nat.gcd_left_comm,
    Nat.gcd_assoc] using σ.primitive

/-- The Möbius action `(aτ+b)/d`. -/
def act (σ : CoxMatrix m) (τ : ℍ) : ℍ :=
  ⟨((σ.a : ℂ) * (τ : ℂ) + (σ.b : ℂ)) / (σ.d : ℂ), by
    have hd : ((σ.d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr σ.d_pos.ne'
    have hd_pos : (0 : ℝ) < (σ.d : ℝ) := by exact_mod_cast σ.d_pos
    have ha : (0 : ℝ) < (σ.a : ℝ) := by exact_mod_cast σ.a_pos
    have him : (((σ.a : ℂ) * (τ : ℂ) + (σ.b : ℂ)) / (σ.d : ℂ)).im =
        (σ.a : ℝ) * (τ : ℂ).im / (σ.d : ℝ) := by
      rw [Complex.div_im, Complex.normSq_natCast]
      simp [Complex.add_im, Complex.mul_im, Complex.add_re, Complex.mul_re,
        Complex.natCast_im, Complex.natCast_re]
      field_simp
    rw [him]
    exact div_pos (mul_pos ha τ.im_pos) hd_pos⟩

@[simp] theorem coe_act (σ : CoxMatrix m) (τ : ℍ) :
    ((σ.act τ : ℍ) : ℂ) =
      ((σ.a : ℂ) * (τ : ℂ) + (σ.b : ℂ)) / (σ.d : ℂ) := rfl

/-- A bounded encoding used to obtain the finite type structure on `C(m)`. -/
def toFin (σ : CoxMatrix m) :
    Fin ((m : ℕ) + 1) × Fin ((m : ℕ) + 1) × Fin ((m : ℕ) + 1) :=
  (⟨σ.a, by have := σ.a_le; omega⟩,
   ⟨σ.b, by have := σ.b_lt; have := σ.d_le; omega⟩,
   ⟨σ.d, by have := σ.d_le; omega⟩)

theorem toFin_injective : Function.Injective (toFin (m := m)) := by
  intro σ τ h
  have ha : σ.a = τ.a := congrArg (fun x ↦ x.1.val) h
  have hb : σ.b = τ.b := congrArg (fun x ↦ x.2.1.val) h
  have hd : σ.d = τ.d := congrArg (fun x ↦ x.2.2.val) h
  cases σ
  cases τ
  simp_all

instance : DecidableEq (CoxMatrix m) := fun x y ↦
  decidable_of_iff (x.toFin = y.toFin) toFin_injective.eq_iff

instance : Fintype (CoxMatrix m) := Fintype.ofInjective toFin toFin_injective

end CoxMatrix

/-- Cox's distinguished matrix `σ₀ = diag(m,1)`. -/
def sigmaZero (m : ℕ+) : CoxMatrix m where
  a := m
  b := 0
  d := 1
  a_pos := PNat.pos m
  determinant := Nat.mul_one m
  b_lt := Nat.zero_lt_one
  primitive := by simp

/-- For a nontrivial level, the two diagonal Cox representatives are distinct. -/
theorem one_lt_card_coxMatrix (m : ℕ+) (hm : 1 < (m : ℕ)) :
    1 < Fintype.card (CoxMatrix m) := by
  let σ : CoxMatrix m :=
    { a := 1
      b := 0
      d := m
      a_pos := Nat.zero_lt_one
      determinant := Nat.one_mul m
      b_lt := PNat.pos m
      primitive := by simp }
  apply Fintype.one_lt_card_iff.mpr
  refine ⟨σ, sigmaZero m, ?_⟩
  intro h
  have ha := congrArg CoxMatrix.a h
  change 1 = (m : ℕ) at ha
  omega

/-- Right cosets of `Γ₀(m)` in `SL₂(ℤ)`. -/
abbrev Gamma0RightCosets (m : ℕ+) :=
  Quotient (QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (m : ℕ)))

noncomputable instance gamma0RightCosetsFintype (m : ℕ+) :
    Fintype (Gamma0RightCosets m) := by
  letI : NeZero (m : ℕ) := ⟨PNat.ne_zero m⟩
  haveI : (CongruenceSubgroup.Gamma0 (m : ℕ)).FiniteIndex := by infer_instance
  letI : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (m : ℕ)) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  exact Fintype.ofEquiv (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (m : ℕ))
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel
      (s := CongruenceSubgroup.Gamma0 (m : ℕ))).symm

private def matrixStar (A : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  !![A 1 1, A 0 1; A 1 0, A 0 0]

private theorem matrixStar_involutive (A : Matrix (Fin 2) (Fin 2) ℤ) :
    matrixStar (matrixStar A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem matrixStar_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    matrixStar (A * B) = matrixStar B * matrixStar A := by
  rw [matrixStar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixStar, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem matrixStar_det (A : Matrix (Fin 2) (Fin 2) ℤ) :
    (matrixStar A).det = A.det := by
  simp [matrixStar, Matrix.det_fin_two]
  ring

private theorem matrixStar_mobiusMatrix {m : ℕ+} (σ : CoxMatrix m) :
    matrixStar σ.mobiusMatrix = σ.inclusionMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private def determinantScale (m : ℕ+) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(m : ℤ), 0; 0, 1]

private def determinantScaleDual (m : ℕ+) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 0, (m : ℤ)]

private theorem matrixStar_determinantScale (m : ℕ+) :
    matrixStar (determinantScale m) = determinantScaleDual m := by
  rfl

private theorem determinantScale_det (m : ℕ+) :
    (determinantScale m).det = (m : ℤ) := by
  simp [determinantScale, Matrix.det_fin_two_of]

private def coxInput (m : ℕ+) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  matrixStar (determinantScale m * γ.1)

private theorem coxInput_eq (m : ℕ+) (γ : SL(2, ℤ)) :
    coxInput m γ =
      !![γ 1 1, (m : ℤ) * γ 0 1; γ 1 0, (m : ℤ) * γ 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coxInput, matrixStar, determinantScale, Matrix.mul_apply, Fin.sum_univ_two]

private theorem coxInput_det (m : ℕ+) (γ : SL(2, ℤ)) :
    (coxInput m γ).det = (m : ℤ) := by
  rw [coxInput, matrixStar_det, Matrix.det_mul, determinantScale_det,
    Matrix.SpecialLinearGroup.det_coe, mul_one]

private theorem coxInput_content_eq_one (m : ℕ+) (γ : SL(2, ℤ)) :
    Matrix.rankTwoContent (coxInput m γ) = 1 := by
  have hcop := ModularGroup.bottom_row_coprime γ
  rw [Int.isCoprime_iff_gcd_eq_one] at hcop
  change Nat.gcd (γ 1 0).natAbs (γ 1 1).natAbs = 1 at hcop
  rw [coxInput_eq]
  simp only [Matrix.rankTwoContent, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [show Nat.gcd
      (Nat.gcd (Nat.gcd (γ 1 1).natAbs ((m : ℤ) * γ 0 1).natAbs)
        (γ 1 0).natAbs) (((m : ℤ) * γ 0 0).natAbs) =
      Nat.gcd (Nat.gcd (γ 1 0).natAbs (γ 1 1).natAbs)
        (Nat.gcd (((m : ℤ) * γ 0 1).natAbs) (((m : ℤ) * γ 0 0).natAbs)) by
    ac_rfl]
  simp [hcop]

private theorem rankTwoContent_dvd_entry_aux (A : Matrix (Fin 2) (Fin 2) ℤ)
    (i j : Fin 2) : A.rankTwoContent ∣ (A i j).natAbs := by
  fin_cases i <;> fin_cases j
  · exact (Nat.gcd_dvd_left _ _).trans
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
  · exact (Nat.gcd_dvd_left _ _).trans
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  · exact Nat.gcd_dvd_right _ _

private theorem dvd_rankTwoContent_aux {A : Matrix (Fin 2) (Fin 2) ℤ} {k : ℕ}
    (h : ∀ i j, k ∣ (A i j).natAbs) : k ∣ A.rankTwoContent :=
  Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (h 0 0) (h 0 1)) (h 1 0)) (h 1 1)

private theorem rankTwoContent_dvd_mul_right_aux
    (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    A.rankTwoContent ∣ (A * B).rankTwoContent := by
  apply dvd_rankTwoContent_aux
  intro i j
  rw [← Int.natCast_dvd, Matrix.mul_apply, Fin.sum_univ_two]
  exact dvd_add
    (dvd_mul_of_dvd_left
      (Int.natCast_dvd.mpr (rankTwoContent_dvd_entry_aux A i 0)) _)
    (dvd_mul_of_dvd_left
      (Int.natCast_dvd.mpr (rankTwoContent_dvd_entry_aux A i 1)) _)

private theorem rankTwoContent_mul_sl (A : Matrix (Fin 2) (Fin 2) ℤ)
    (U : SL(2, ℤ)) : (A * U.1).rankTwoContent = A.rankTwoContent := by
  apply Nat.dvd_antisymm
  · have h := rankTwoContent_dvd_mul_right_aux (A * U.1) U⁻¹.1
    have hcancel : (A * U.1) * U⁻¹.1 = A := by
      rw [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul]
      simp
    rw [hcancel] at h
    exact h
  · exact rankTwoContent_dvd_mul_right_aux A U.1

private def slStar (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨matrixStar γ.1, by rw [matrixStar_det, γ.prop]⟩

@[simp] private theorem coe_slStar (γ : SL(2, ℤ)) :
    (slStar γ).1 = matrixStar γ.1 := rfl

private theorem reduced_eq_of_eq_add_mul_aux {d r r' q : ℤ}
    (hr : r ∈ Set.Ico 0 d) (hr' : r' ∈ Set.Ico 0 d)
    (e : d * q + r = r') : r = r' := by
  calc
    r = r % d := (Int.emod_eq_of_lt hr.1 hr.2).symm
    _ = r' % d := by rw [← e]; simp [Int.add_emod]
    _ = r' := Int.emod_eq_of_lt hr'.1 hr'.2

private theorem columnHNF_eq_of_mul {A B U : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : A.IsColumnHermiteNormalForm) (hB : B.IsColumnHermiteNormalForm)
    (hU : IsUnit U.det) (hmul : A * U = B) : A = B := by
  let V : Matrix (Fin 2) (Fin 2) ℤ := U⁻¹
  have hmul' : B * V = A := by
    rw [← hmul, Matrix.mul_assoc, Matrix.mul_nonsing_inv U hU, Matrix.mul_one]
  have hz := hA.belowDiagonal_eq_zero 1 0 (by omega)
  have hz' := hB.belowDiagonal_eq_zero 1 0 (by omega)
  have hd := hA.diagonal_pos 0
  have hd' := hB.diagonal_pos 0
  have ha := hA.diagonal_pos 1
  have ha' := hB.diagonal_pos 1
  have hr := hA.reduced 0 1 (by omega)
  have hr' := hB.reduced 0 1 (by omega)
  have hu10 : U 1 0 = 0 := by
    have e : A 1 1 * U 1 0 = 0 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hz, hz', zero_mul,
        zero_add] using congrFun (congrFun hmul 1) 0
    exact (mul_eq_zero.mp e).resolve_left (ne_of_gt ha)
  have hv10 : V 1 0 = 0 := by
    have e : B 1 1 * V 1 0 = 0 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hz, hz', zero_mul,
        zero_add] using congrFun (congrFun hmul' 1) 0
    exact (mul_eq_zero.mp e).resolve_left (ne_of_gt ha')
  have haa' : A 1 1 = B 1 1 := by
    have e : A 1 1 * U 1 1 = B 1 1 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hz, zero_mul,
        zero_add] using congrFun (congrFun hmul 1) 1
    have e' : B 1 1 * V 1 1 = A 1 1 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hz', zero_mul,
        zero_add] using congrFun (congrFun hmul' 1) 1
    apply le_antisymm
    · exact Int.le_of_dvd ha' ⟨U 1 1, e.symm⟩
    · exact Int.le_of_dvd ha ⟨V 1 1, e'.symm⟩
  have hu11 : U 1 1 = 1 := by
    have e : A 1 1 * U 1 1 = B 1 1 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hz, zero_mul,
        zero_add] using congrFun (congrFun hmul 1) 1
    apply mul_left_cancel₀ (ne_of_gt ha')
    simpa only [haa', mul_one] using e
  have hdd' : A 0 0 = B 0 0 := by
    have e : A 0 0 * U 0 0 = B 0 0 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hu10, mul_zero,
        add_zero] using congrFun (congrFun hmul 0) 0
    have e' : B 0 0 * V 0 0 = A 0 0 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hv10, mul_zero,
        add_zero] using congrFun (congrFun hmul' 0) 0
    apply le_antisymm
    · exact Int.le_of_dvd hd' ⟨U 0 0, e.symm⟩
    · exact Int.le_of_dvd hd ⟨V 0 0, e'.symm⟩
  have hrr' : A 0 1 = B 0 1 := by
    have e : A 0 0 * U 0 1 + A 0 1 = B 0 1 := by
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, hu11, mul_one] using
        congrFun (congrFun hmul 0) 1
    exact reduced_eq_of_eq_add_mul_aux hr (hdd' ▸ hr') e
  ext i j
  fin_cases i <;> fin_cases j
  · exact hdd'
  · exact hrr'
  · exact hz.trans hz'.symm
  · exact haa'

/-- A Cox representative is determined by its sublattice inclusion matrix. -/
theorem CoxMatrix.inclusionMatrix_injective {m : ℕ+} :
    Function.Injective (CoxMatrix.inclusionMatrix (m := m)) := by
  intro σ τ h
  have hd := congrFun (congrFun h 0) 0
  have hb := congrFun (congrFun h 0) 1
  have ha := congrFun (congrFun h 1) 1
  simp only [CoxMatrix.inclusionMatrix, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Int.ofNat_inj] at hd hb ha
  cases σ
  cases τ
  simp_all

private theorem rightRel_of_coxInput_eq_mul (m : ℕ+) (γ δ U : SL(2, ℤ))
    (h : coxInput m δ = coxInput m γ * U.1) :
    QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (m : ℕ)) γ δ := by
  rw [QuotientGroup.rightRel_apply, CongruenceSubgroup.Gamma0_mem]
  have h10 := congrFun (congrFun h 1) 0
  have h00 := congrFun (congrFun h 0) 0
  rw [coxInput_eq, coxInput_eq] at h10 h00
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h10 h00
  have hentry : (δ * γ⁻¹) 1 0 = (m : ℤ) * U 1 0 := by
    change (δ.1 * (γ⁻¹).1) 1 0 = (m : ℤ) * U 1 0
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp only [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hdet := γ.prop
    rw [Matrix.det_fin_two] at hdet
    linear_combination γ 1 1 * h10 - γ 1 0 * h00 +
      ((m : ℤ) * U 1 0) * hdet
  rw [hentry]
  simp

private theorem exists_coxInput_eq_mul_of_rightRel (m : ℕ+) (γ δ : SL(2, ℤ))
    (hrel : QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (m : ℕ)) γ δ) :
    ∃ U : SL(2, ℤ), coxInput m δ = coxInput m γ * U.1 := by
  let h : SL(2, ℤ) := δ * γ⁻¹
  have hhmem : h ∈ CongruenceSubgroup.Gamma0 (m : ℕ) :=
    QuotientGroup.rightRel_apply.mp hrel
  have hcast : ((h 1 0 : ℤ) : ZMod (m : ℕ)) = 0 :=
    CongruenceSubgroup.Gamma0_mem.mp hhmem
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  let U : SL(2, ℤ) :=
    ⟨!![h 1 1, (m : ℤ) * h 0 1; k, h 0 0], by
      rw [Matrix.det_fin_two_of]
      have hdet := h.prop
      rw [Matrix.det_fin_two] at hdet
      linear_combination hdet + h 0 1 * hk⟩
  refine ⟨U, ?_⟩
  have hhγ : h * γ = δ := by simp [h]
  rw [← hhγ, coxInput_eq, coxInput_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U, Matrix.mul_apply, Fin.sum_univ_two, hk] <;> ring

private theorem exists_coxMatrix_reduction (m : ℕ+) (γ : SL(2, ℤ)) :
    ∃ (σ : CoxMatrix m) (U : SL(2, ℤ)),
      coxInput m γ * U.1 = σ.inclusionMatrix := by
  obtain ⟨B, hBunit, hH⟩ :=
    Matrix.exists_right_mul_isColumnHermiteNormalForm (coxInput m γ)
      (by rw [coxInput_det]; exact_mod_cast PNat.ne_zero m)
  let H : Matrix (Fin 2) (Fin 2) ℤ := coxInput m γ * B
  have hHhnf : H.IsColumnHermiteNormalForm := hH
  have hz : H 1 0 = 0 := hHhnf.belowDiagonal_eq_zero 1 0 (by omega)
  have hd : 0 < H 0 0 := hHhnf.diagonal_pos 0
  have ha : 0 < H 1 1 := hHhnf.diagonal_pos 1
  have hb := hHhnf.reduced 0 1 (by omega)
  have hHdet : H.det = (m : ℤ) * B.det := by
    change (coxInput m γ * B).det = (m : ℤ) * B.det
    rw [Matrix.det_mul, coxInput_det]
  have hHdetpos : 0 < H.det := by
    rw [Matrix.det_fin_two, hz, mul_zero, sub_zero]
    exact mul_pos hd ha
  have hBdet : B.det = 1 := by
    rcases Int.isUnit_iff.mp hBunit with hB | hB
    · exact hB
    · rw [hHdet, hB, mul_neg_one] at hHdetpos
      have hmpos : (0 : ℤ) < m := by exact_mod_cast PNat.pos m
      omega
  let U : SL(2, ℤ) := ⟨B, hBdet⟩
  have hHdet' : H.det = (m : ℤ) := by rw [hHdet, hBdet, mul_one]
  have hdiag : H 0 0 * H 1 1 = (m : ℤ) := by
    simpa [Matrix.det_fin_two, hz] using hHdet'
  have hcontent : H.rankTwoContent = 1 := by
    change (coxInput m γ * U.1).rankTwoContent = 1
    rw [rankTwoContent_mul_sl, coxInput_content_eq_one]
  let σ : CoxMatrix m :=
    { a := (H 1 1).natAbs
      b := (H 0 1).natAbs
      d := (H 0 0).natAbs
      a_pos := Int.natAbs_pos.mpr (ne_of_gt ha)
      determinant := by
        have hdiag' : ((H 1 1).natAbs : ℤ) * (H 0 0).natAbs = (m : ℤ) := by
          rw [Int.ofNat_natAbs_of_nonneg ha.le,
            Int.ofNat_natAbs_of_nonneg hd.le]
          exact (mul_comm _ _).trans hdiag
        exact_mod_cast hdiag'
      b_lt := by
        have hbc : ((H 0 1).natAbs : ℤ) < (H 0 0).natAbs := by
          rw [Int.ofNat_natAbs_of_nonneg hb.1,
            Int.ofNat_natAbs_of_nonneg hd.le]
          exact hb.2
        exact_mod_cast hbc
      primitive := by
        simpa [Matrix.rankTwoContent, hz, Nat.gcd_comm, Nat.gcd_left_comm,
          Nat.gcd_assoc] using hcontent }
  refine ⟨σ, U, ?_⟩
  change H = σ.inclusionMatrix
  ext i j
  fin_cases i <;> fin_cases j
  · simp [σ, CoxMatrix.inclusionMatrix, Int.ofNat_natAbs_of_nonneg hd.le]
  · simp [σ, CoxMatrix.inclusionMatrix, Int.ofNat_natAbs_of_nonneg hb.1]
  · simp [σ, CoxMatrix.inclusionMatrix, hz]
  · simp [σ, CoxMatrix.inclusionMatrix, Int.ofNat_natAbs_of_nonneg ha.le]

private theorem coxMatrix_reduction_unique (m : ℕ+) (γ : SL(2, ℤ))
    {σ τ : CoxMatrix m} {U V : SL(2, ℤ)}
    (hσ : coxInput m γ * U.1 = σ.inclusionMatrix)
    (hτ : coxInput m γ * V.1 = τ.inclusionMatrix) : σ = τ := by
  let W : SL(2, ℤ) := U⁻¹ * V
  have hmul : σ.inclusionMatrix * W.1 = τ.inclusionMatrix := by
    calc
      σ.inclusionMatrix * W.1 =
          (coxInput m γ * U.1) * (U⁻¹.1 * V.1) := by rw [hσ]; rfl
      _ = coxInput m γ * V.1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc U.1,
          ← Matrix.SpecialLinearGroup.coe_mul]
        simp
      _ = τ.inclusionMatrix := hτ
  apply CoxMatrix.inclusionMatrix_injective
  exact columnHNF_eq_of_mul σ.inclusionMatrix_isColumnHermiteNormalForm
    τ.inclusionMatrix_isColumnHermiteNormalForm (by rw [Matrix.SpecialLinearGroup.det_coe]; simp)
    hmul

private noncomputable def coxRepresentative (m : ℕ+) (γ : SL(2, ℤ)) : CoxMatrix m :=
  (exists_coxMatrix_reduction m γ).choose

private noncomputable def coxReductionMatrix (m : ℕ+) (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  (exists_coxMatrix_reduction m γ).choose_spec.choose

private theorem coxReduction_spec (m : ℕ+) (γ : SL(2, ℤ)) :
    coxInput m γ * (coxReductionMatrix m γ).1 =
      (coxRepresentative m γ).inclusionMatrix :=
  (exists_coxMatrix_reduction m γ).choose_spec.choose_spec

private theorem rightRel_iff_coxRepresentative_eq (m : ℕ+) (γ δ : SL(2, ℤ)) :
    QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (m : ℕ)) γ δ ↔
      coxRepresentative m γ = coxRepresentative m δ := by
  constructor
  · intro hrel
    obtain ⟨W, hW⟩ := exists_coxInput_eq_mul_of_rightRel m γ δ hrel
    let V : SL(2, ℤ) := W * coxReductionMatrix m δ
    apply coxMatrix_reduction_unique m γ (coxReduction_spec m γ)
    calc
      coxInput m γ * V.1 =
          (coxInput m γ * W.1) * (coxReductionMatrix m δ).1 := by
        rw [show V = W * coxReductionMatrix m δ from rfl,
          Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
      _ = coxInput m δ * (coxReductionMatrix m δ).1 := by rw [hW]
      _ = (coxRepresentative m δ).inclusionMatrix := coxReduction_spec m δ
  · intro hrep
    let W : SL(2, ℤ) := coxReductionMatrix m γ * (coxReductionMatrix m δ)⁻¹
    apply rightRel_of_coxInput_eq_mul m γ δ W
    have hγ := coxReduction_spec m γ
    have hδ := coxReduction_spec m δ
    rw [hrep] at hγ
    have heq : coxInput m δ * (coxReductionMatrix m δ).1 =
        coxInput m γ * (coxReductionMatrix m γ).1 := hδ.trans hγ.symm
    calc
      coxInput m δ =
          (coxInput m δ * (coxReductionMatrix m δ).1) *
            (coxReductionMatrix m δ)⁻¹.1 := by
        rw [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul]
        simp
      _ = (coxInput m γ * (coxReductionMatrix m γ).1) *
          (coxReductionMatrix m δ)⁻¹.1 := by rw [heq]
      _ = coxInput m γ * W.1 := by
        rw [show W = coxReductionMatrix m γ * (coxReductionMatrix m δ)⁻¹ from rfl,
          Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

private theorem matrixStar_inclusionMatrix {m : ℕ+} (σ : CoxMatrix m) :
    matrixStar σ.inclusionMatrix = σ.mobiusMatrix := by
  rw [← matrixStar_mobiusMatrix σ, matrixStar_involutive]

private theorem coxRepresentative_normalization (m : ℕ+) (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ),
      (δ⁻¹ : SL(2, ℤ)).1 *
          !![(m : ℤ) * γ 0 0, (m : ℤ) * γ 0 1; γ 1 0, γ 1 1] =
        (coxRepresentative m γ).mobiusMatrix := by
  let U := coxReductionMatrix m γ
  refine ⟨(slStar U)⁻¹, ?_⟩
  have h := congrArg matrixStar (coxReduction_spec m γ)
  rw [matrixStar_mul, matrixStar_inclusionMatrix] at h
  have hD : determinantScale m * γ.1 =
      !![(m : ℤ) * γ 0 0, (m : ℤ) * γ 0 1; γ 1 0, γ 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [determinantScale, Matrix.mul_apply, Fin.sum_univ_two]
  change matrixStar U.1 * matrixStar (coxInput m γ) =
    (coxRepresentative m γ).mobiusMatrix at h
  rw [coxInput, matrixStar_involutive, hD] at h
  simpa [U, coe_slStar] using h

private theorem coxInput_one (m : ℕ+) :
    coxInput m (1 : SL(2, ℤ)) = (sigmaZero m).inclusionMatrix := by
  rw [coxInput_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaZero, CoxMatrix.inclusionMatrix]

private theorem coxRepresentative_one (m : ℕ+) :
    coxRepresentative m (1 : SL(2, ℤ)) = sigmaZero m := by
  apply coxMatrix_reduction_unique m 1 (coxReduction_spec m 1)
      (V := (1 : SL(2, ℤ)))
  rw [coxInput_one]
  simp

private theorem exists_coprime_add_mul_of_gcd_gcd_eq_one
    (a b d : ℕ) (ha : a ≠ 0) (h : Nat.gcd (Nat.gcd a b) d = 1) :
    ∃ x : ℕ, Nat.Coprime a (b + x * d) := by
  let ps : Finset ℕ := {p ∈ a.primeFactors | ¬p ∣ b}
  use ps.prod id
  apply Nat.coprime_of_dvd
  intro p pp hpa hpSum
  by_cases hpb : p ∣ b
  · have hpProd : p ∣ ps.prod id * d := by
      exact (Nat.dvd_add_iff_right (n := ps.prod id * d) hpb).mpr hpSum
    rcases pp.dvd_mul.mp hpProd with hpPs | hpd
    · have ⟨q, hq, hpq⟩ := (pp.prime.dvd_finsetProd_iff id).mp hpPs
      rw [Finset.mem_filter, Nat.mem_primeFactors,
        ← (Nat.prime_dvd_prime_iff_eq pp hq.1.1).mp hpq] at hq
      exact hq.2 hpb
    · have hpGcd : p ∣ Nat.gcd (Nat.gcd a b) d :=
        Nat.dvd_gcd (Nat.dvd_gcd hpa hpb) hpd
      rw [h] at hpGcd
      exact pp.not_dvd_one hpGcd
  · have hps : p ∈ ps := Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨pp, hpa, ha⟩, hpb⟩
    have hpProd : p ∣ ps.prod id * d :=
      (Finset.dvd_prod_of_mem id hps).mul_right d
    exact hpb ((Nat.dvd_add_iff_left (m := b) hpProd).mpr hpSum)

private theorem coxMatrix_smith_normalization {m : ℕ+} (σ : CoxMatrix m) :
    ∃ L R : SL(2, ℤ),
      (L⁻¹).1 * σ.inclusionMatrix * R.1 = determinantScaleDual m := by
  obtain ⟨x, hx⟩ :=
    exists_coprime_add_mul_of_gcd_gcd_eq_one σ.a σ.b σ.d σ.a_pos.ne' σ.primitive
  let R₁ : SL(2, ℤ) :=
    ⟨!![(x : ℤ), -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩
  let M : Matrix (Fin 2) (Fin 2) ℤ := σ.inclusionMatrix * R₁.1
  have hM00 : M 0 0 = (σ.b + x * σ.d : ℕ) := by
    simp [M, R₁, CoxMatrix.inclusionMatrix]
    ring
  have hM10 : M 1 0 = σ.a := by
    simp [M, R₁, CoxMatrix.inclusionMatrix]
  have hcop : IsCoprime ((σ.b + x * σ.d : ℕ) : ℤ) (σ.a : ℤ) :=
    hx.symm.isCoprime
  obtain ⟨L, hL00, hL10⟩ := hcop.exists_SL2_col 0
  let N : Matrix (Fin 2) (Fin 2) ℤ := (L⁻¹).1 * M
  have hN00 : N 0 0 = 1 := by
    change ((L⁻¹).1 * M) 0 0 = 1
    rw [Matrix.mul_apply, Matrix.SpecialLinearGroup.SL2_inv_expl,
      Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hM00, hM10, ← hL00, ← hL10]
    have hdet := L.prop
    rw [Matrix.det_fin_two] at hdet
    linear_combination hdet
  have hN10 : N 1 0 = 0 := by
    change ((L⁻¹).1 * M) 1 0 = 0
    rw [Matrix.mul_apply, Matrix.SpecialLinearGroup.SL2_inv_expl,
      Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hM00, hM10, ← hL00, ← hL10]
    ring
  have hMdet : M.det = (m : ℤ) := by
    change (σ.inclusionMatrix * R₁.1).det = (m : ℤ)
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one,
      CoxMatrix.inclusionMatrix_det]
  have hNdet : N.det = (m : ℤ) := by
    change ((L⁻¹).1 * M).det = (m : ℤ)
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul, hMdet]
  have hN11 : N 1 1 = (m : ℤ) := by
    simpa [Matrix.det_fin_two, hN00, hN10] using hNdet
  let R₂ : SL(2, ℤ) :=
    ⟨!![1, -N 0 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let R : SL(2, ℤ) := R₁ * R₂
  refine ⟨L, R, ?_⟩
  change (L⁻¹).1 * σ.inclusionMatrix * (R₁ * R₂).1 = determinantScaleDual m
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc,
    Matrix.mul_assoc (L⁻¹).1 σ.inclusionMatrix R₁.1]
  change N * R₂.1 = determinantScaleDual m
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R₂, determinantScaleDual, Matrix.mul_apply, Fin.sum_univ_two,
      hN00, hN10, hN11]

private theorem coxRepresentative_surjective (m : ℕ+) :
    Function.Surjective (coxRepresentative m) := by
  intro σ
  obtain ⟨L, R, hnorm⟩ := coxMatrix_smith_normalization σ
  refine ⟨slStar L, ?_⟩
  apply coxMatrix_reduction_unique m (slStar L) (coxReduction_spec m (slStar L))
  calc
    coxInput m (slStar L) * (R⁻¹).1 =
        L.1 * determinantScaleDual m * (R⁻¹).1 := by
          rw [coxInput, coe_slStar, matrixStar_mul,
            matrixStar_involutive, matrixStar_determinantScale]
    _ = σ.inclusionMatrix := by
      calc
        L.1 * determinantScaleDual m * (R⁻¹).1 =
            L.1 * ((L⁻¹).1 * σ.inclusionMatrix * R.1) * (R⁻¹).1 := by rw [hnorm]
        _ = σ.inclusionMatrix := by
          rw [Matrix.mul_assoc L.1, Matrix.mul_assoc ((L⁻¹).1 * σ.inclusionMatrix),
            ← Matrix.SpecialLinearGroup.coe_mul]
          simp only [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
          rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul]
          simp

private noncomputable def rightCosetToCoxMatrix (m : ℕ+) :
    Gamma0RightCosets m → CoxMatrix m :=
  Quotient.lift (coxRepresentative m) fun γ δ h ↦
    (rightRel_iff_coxRepresentative_eq m γ δ).mp h

private theorem rightCosetToCoxMatrix_bijective (m : ℕ+) :
    Function.Bijective (rightCosetToCoxMatrix m) := by
  constructor
  · intro c d hcd
    obtain ⟨γ, rfl⟩ := Quotient.exists_rep c
    obtain ⟨δ, rfl⟩ := Quotient.exists_rep d
    apply Quotient.sound
    exact (rightRel_iff_coxRepresentative_eq m γ δ).mpr hcd
  · intro σ
    obtain ⟨γ, hγ⟩ := coxRepresentative_surjective m σ
    exact ⟨Quotient.mk'' γ, hγ⟩

/-- Cox Lemma 11.11.  The proof is the rank-two HNF classification of the relevant
determinant-`m` primitive matrices. -/
noncomputable def coxMatrixEquivRightCosets (m : ℕ+) :
    CoxMatrix m ≃ Gamma0RightCosets m :=
  (Equiv.ofBijective (rightCosetToCoxMatrix m)
    (rightCosetToCoxMatrix_bijective m)).symm

@[simp]
private theorem coxMatrixEquivRightCosets_coxRepresentative
    (m : ℕ+) (γ : SL(2, ℤ)) :
    coxMatrixEquivRightCosets m (coxRepresentative m γ) = Quotient.mk'' γ := by
  apply (Equiv.ofBijective (rightCosetToCoxMatrix m)
    (rightCosetToCoxMatrix_bijective m)).symm_apply_eq.mpr
  rfl

/-- Translate a `Γ₀(m)`-modular function by a right coset; invariance makes this independent
of the representative. -/
noncomputable def rightCosetTranslate (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (c : Gamma0RightCosets m) (τ : ℍ) : ℂ :=
  Quotient.liftOn c (fun γ : SL(2, ℤ) ↦ f (γ • τ)) fun γ δ hγδ ↦ by
    have hmem : δ * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 (m : ℕ) :=
      QuotientGroup.rightRel_apply.mp hγδ
    let g₀ : CongruenceSubgroup.Gamma0 (m : ℕ) := ⟨δ * γ⁻¹, hmem⟩
    have hinv := congrFun (hf.2.1 g₀) (γ • τ)
    have hg₀ : (g₀ : SL(2, ℤ)) * γ = δ := by
      simp [g₀]
    rw [ModularForm.SL_slash_apply] at hinv
    simp only [neg_zero, zpow_zero, mul_one] at hinv
    calc
      f (γ • τ) = f ((g₀ : SL(2, ℤ)) • (γ • τ)) := hinv.symm
      _ = f (((g₀ : SL(2, ℤ)) * γ) • τ) :=
        congrArg f (mul_smul (g₀ : SL(2, ℤ)) γ τ).symm
      _ = f (δ • τ) := by rw [hg₀]

@[simp]
theorem rightCosetTranslate_mk (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (γ : SL(2, ℤ)) (τ : ℍ) :
    rightCosetTranslate m hf (Quotient.mk'' γ) τ = f (γ • τ) :=
  rfl

/-- The conjugate `j(m γ τ)` attached to a right coset. -/
noncomputable def rightCosetEval (m : ℕ+) (c : Gamma0RightCosets m) (τ : ℍ) : ℂ :=
  rightCosetTranslate m (levelJ_isGamma0ModularFunction m) c τ

@[simp]
theorem rightCosetEval_mk (m : ℕ+) (γ : SL(2, ℤ)) (τ : ℍ) :
    rightCosetEval m (Quotient.mk'' γ) τ = levelJ m (γ • τ) :=
  rfl

/-- Right multiplication by an element of `SL₂(ℤ)` permutes the right cosets of `Γ₀(m)`. -/
def rightCosetMul (m : ℕ+) (δ : SL(2, ℤ)) :
    Gamma0RightCosets m ≃ Gamma0RightCosets m where
  toFun :=
    Quotient.map' (fun γ : SL(2, ℤ) ↦ γ * δ) fun γ γ' h ↦ by
      rw [QuotientGroup.rightRel_apply] at h ⊢
      simpa [mul_assoc] using h
  invFun :=
    Quotient.map' (fun γ : SL(2, ℤ) ↦ γ * δ⁻¹) fun γ γ' h ↦ by
      rw [QuotientGroup.rightRel_apply] at h ⊢
      simpa [mul_assoc] using h
  left_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro γ
    apply Quotient.sound
    change QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (m : ℕ))
      ((γ * δ) * δ⁻¹) γ
    rw [QuotientGroup.rightRel_apply]
    simp [mul_assoc]
  right_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro γ
    apply Quotient.sound
    change QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (m : ℕ))
      ((γ * δ⁻¹) * δ) γ
    rw [QuotientGroup.rightRel_apply]
    simp [mul_assoc]

/-- Right multiplication on the quotient sends the class of `γ` to the class of `γ * δ`. -/
@[simp]
theorem rightCosetMul_mk (m : ℕ+) (δ γ : SL(2, ℤ)) :
    rightCosetMul m δ (Quotient.mk'' γ) = Quotient.mk'' (γ * δ) :=
  rfl

/-- The right coset of the identity matrix. -/
def baseRightCoset (m : ℕ+) : Gamma0RightCosets m :=
  Quotient.mk'' (1 : SL(2, ℤ))

/-- Every right coset is obtained from the identity coset by right multiplication. -/
theorem exists_rightCosetMul_baseRightCoset_eq (m : ℕ+) (c : Gamma0RightCosets m) :
    ∃ δ : SL(2, ℤ), rightCosetMul m δ (baseRightCoset m) = c := by
  obtain ⟨δ, rfl⟩ := Quotient.exists_rep c
  exact ⟨δ, by simp [baseRightCoset]⟩

/-- Translating the argument of a right-coset translate corresponds to right multiplication
of its coset. -/
theorem rightCosetTranslate_smul (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (δ : SL(2, ℤ))
    (c : Gamma0RightCosets m) (τ : ℍ) :
    rightCosetTranslate m hf c (δ • τ) =
      rightCosetTranslate m hf (rightCosetMul m δ c) τ := by
  refine Quotient.inductionOn c ?_
  intro γ
  change f (γ • (δ • τ)) = f ((γ * δ) • τ)
  rw [mul_smul]

/-- Translating the argument of a right-coset conjugate corresponds to right multiplication
of its coset. -/
theorem rightCosetEval_smul (m : ℕ+) (δ : SL(2, ℤ))
    (c : Gamma0RightCosets m) (τ : ℍ) :
    rightCosetEval m c (δ • τ) = rightCosetEval m (rightCosetMul m δ c) τ := by
  exact rightCosetTranslate_smul m (levelJ_isGamma0ModularFunction m) δ c τ

private lemma complex_mobius_scale_eq_affine
    {n p q u v a b c d g r s z : ℂ}
    (hD : c * z + d ≠ 0) (hs : s ≠ 0)
    (h00 : p * (n * a) + q * c = g) (h01 : p * (n * b) + q * d = r)
    (h10 : u * (n * a) + v * c = 0) (h11 : u * (n * b) + v * d = s) :
    (p * (n * ((a * z + b) / (c * z + d))) + q) /
        (u * (n * ((a * z + b) / (c * z + d))) + v) =
      r / s + g / s * z := by
  let D := c * z + d
  have hD' : D ≠ 0 := by simpa [D] using hD
  have hnum : p * (n * ((a * z + b) / D)) + q = (g * z + r) / D := by
    field_simp [hD']
    linear_combination z * h00 + h01
  have hden : u * (n * ((a * z + b) / D)) + v = s / D := by
    field_simp [hD']
    linear_combination z * h10 + h11
  rw [show c * z + d = D from rfl, hnum, hden]
  field_simp [hD', hs]
  ring

private theorem levelJ_smul_eq_j_act_of_normalization
    (m : ℕ+) (σ : CoxMatrix m) (γ δ : SL(2, ℤ))
    (hmat : (δ⁻¹ : SL(2, ℤ)).1 *
        !![(m : ℤ) * γ 0 0, (m : ℤ) * γ 0 1; γ 1 0, γ 1 1] =
      σ.mobiusMatrix) (τ : ℍ) :
    levelJ m (γ • τ) = j (σ.act τ) := by
  let zN : ℍ := ⟨(m : ℂ) * ((γ • τ : ℍ) : ℂ), by
    rw [Complex.mul_im]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (Nat.cast_pos.mpr (PNat.pos m)) (γ • τ).im_pos⟩
  change j zN = j (σ.act τ)
  rw [← j_modularGroup_smul (δ⁻¹) zN]
  congr 1
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hγcoe : (((γ • τ : ℍ) : ℂ)) =
      ((((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) + (γ 0 1 : ℤ)) /
        (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (γ 1 1 : ℤ))) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    norm_cast
  change
    ((((δ⁻¹ : SL(2, ℤ)) 0 0 : ℤ) : ℂ) *
          ((m : ℂ) * (((γ • τ : ℍ) : ℂ))) +
        (((δ⁻¹ : SL(2, ℤ)) 0 1 : ℤ) : ℂ)) /
      ((((δ⁻¹ : SL(2, ℤ)) 1 0 : ℤ) : ℂ) *
          ((m : ℂ) * (((γ • τ : ℍ) : ℂ))) +
        (((δ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ℂ)) = _
  rw [hγcoe]
  have h00 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hmat 0) 0)
  have h01 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hmat 0) 1)
  have h10 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hmat 1) 0)
  have h11 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hmat 1) 1)
  simp only [CoxMatrix.mobiusMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h01 h10 h11
  push_cast at h00 h01 h10 h11
  have hD : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (γ 1 1 : ℤ)) ≠ 0 := by
    simpa [ModularGroup.denom_apply, algebraMap_int_eq] using
      UpperHalfPlane.denom_ne_zero γ τ
  have hmob := complex_mobius_scale_eq_affine hD
    (show (σ.d : ℂ) ≠ 0 by exact_mod_cast σ.d_pos.ne') h00 h01 h10 h11
  rw [hmob, CoxMatrix.coe_act]
  field_simp [show (σ.d : ℂ) ≠ 0 by exact_mod_cast σ.d_pos.ne']
  ring

private theorem coxMatrixEquivRightCosets_sigmaZero (m : ℕ+) :
    coxMatrixEquivRightCosets m (sigmaZero m) = Quotient.mk'' (1 : SL(2, ℤ)) := by
  rw [← coxRepresentative_one m]
  exact coxMatrixEquivRightCosets_coxRepresentative m 1

/-- Cox equation (11.12), expressed through the HNF/right-coset equivalence. -/
theorem rightCosetEval_equiv (m : ℕ+) (σ : CoxMatrix m) (τ : ℍ) :
    rightCosetEval m (coxMatrixEquivRightCosets m σ) τ = j (σ.act τ) := by
  obtain ⟨γ, rfl⟩ := coxRepresentative_surjective m σ
  rw [coxMatrixEquivRightCosets_coxRepresentative, rightCosetEval_mk]
  obtain ⟨δ, hδ⟩ := coxRepresentative_normalization m γ
  exact levelJ_smul_eq_j_act_of_normalization m (coxRepresentative m γ) γ δ hδ τ

/-- The distinguished Cox matrix corresponds to the identity right coset, so translating by
it leaves a modular function unchanged. -/
theorem rightCosetTranslate_sigmaZero (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (τ : ℍ) :
    rightCosetTranslate m hf (coxMatrixEquivRightCosets m (sigmaZero m)) τ = f τ := by
  rw [coxMatrixEquivRightCosets_sigmaZero, rightCosetTranslate_mk]
  simp

theorem j_act_sigmaZero (m : ℕ+) :
    (fun τ ↦ j ((sigmaZero m).act τ)) = levelJ m := by
  funext τ
  congr 1
  apply UpperHalfPlane.ext
  simp [sigmaZero, CoxMatrix.act]

private theorem exists_sl_right_mul_isColumnHermiteNormalForm_aux
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : 0 < A.det) :
    ∃ U : SL(2, ℤ), (A * U.1).IsColumnHermiteNormalForm := by
  obtain ⟨B, hBunit, hH⟩ :=
    Matrix.exists_right_mul_isColumnHermiteNormalForm A hdet.ne'
  have hABdet : 0 < (A * B).det := by
    rw [Matrix.det_fin_two, hH.belowDiagonal_eq_zero 1 0 (by omega), mul_zero, sub_zero]
    exact mul_pos (hH.diagonal_pos 0) (hH.diagonal_pos 1)
  have hBdet : B.det = 1 := by
    rcases Int.isUnit_iff.mp hBunit with hB | hB
    · exact hB
    · rw [Matrix.det_mul, hB, mul_neg_one] at hABdet
      omega
  exact ⟨⟨B, hBdet⟩, hH⟩

private theorem exists_coxMatrix_of_isColumnHermiteNormalForm_aux {m : ℕ+}
    (H : Matrix (Fin 2) (Fin 2) ℤ) (hH : H.IsColumnHermiteNormalForm)
    (hdet : H.det = (m : ℤ)) (hcontent : H.rankTwoContent = 1) :
    ∃ σ : CoxMatrix m, H = σ.inclusionMatrix := by
  have hz : H 1 0 = 0 := hH.belowDiagonal_eq_zero 1 0 (by omega)
  have hd : 0 < H 0 0 := hH.diagonal_pos 0
  have ha : 0 < H 1 1 := hH.diagonal_pos 1
  have hb := hH.reduced 0 1 (by omega)
  have hdiag : H 0 0 * H 1 1 = (m : ℤ) := by
    simpa [Matrix.det_fin_two, hz] using hdet
  let σ : CoxMatrix m :=
    { a := (H 1 1).natAbs
      b := (H 0 1).natAbs
      d := (H 0 0).natAbs
      a_pos := Int.natAbs_pos.mpr (ne_of_gt ha)
      determinant := by
        have hdiag' : ((H 1 1).natAbs : ℤ) * (H 0 0).natAbs = (m : ℤ) := by
          rw [Int.ofNat_natAbs_of_nonneg ha.le, Int.ofNat_natAbs_of_nonneg hd.le]
          exact (mul_comm _ _).trans hdiag
        exact_mod_cast hdiag'
      b_lt := by
        have hbc : ((H 0 1).natAbs : ℤ) < (H 0 0).natAbs := by
          rw [Int.ofNat_natAbs_of_nonneg hb.1, Int.ofNat_natAbs_of_nonneg hd.le]
          exact hb.2
        exact_mod_cast hbc
      primitive := by
        simpa [Matrix.rankTwoContent, hz, Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc]
          using hcontent }
  refine ⟨σ, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp [σ, CoxMatrix.inclusionMatrix, Int.ofNat_natAbs_of_nonneg hd.le]
  · simp [σ, CoxMatrix.inclusionMatrix, Int.ofNat_natAbs_of_nonneg hb.1]
  · simp [σ, CoxMatrix.inclusionMatrix, hz]
  · simp [σ, CoxMatrix.inclusionMatrix, Int.ofNat_natAbs_of_nonneg ha.le]

/-- A primitive integer matrix of positive determinant has a Cox upper-triangular representative
after left multiplication by an element of `SL₂(ℤ)` (Report Lemma 5.8). -/
theorem exists_sl2_mul_eq_coxMatrix {m : ℕ+}
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = (m : ℤ))
    (hprimitive : Matrix.rankTwoContent M = 1) :
    ∃ γ : SL(2, ℤ), ∃ σ : CoxMatrix m, γ.1 * M = σ.mobiusMatrix := by
  obtain ⟨U, hH⟩ := exists_sl_right_mul_isColumnHermiteNormalForm_aux (matrixStar M) (by
    rw [matrixStar_det, hdet]
    exact_mod_cast PNat.pos m)
  let H : Matrix (Fin 2) (Fin 2) ℤ := matrixStar M * U.1
  have hHhnf : H.IsColumnHermiteNormalForm := hH
  have hHdet : H.det = (m : ℤ) := by
    change (matrixStar M * U.1).det = (m : ℤ)
    rw [Matrix.det_mul, matrixStar_det, hdet, Matrix.SpecialLinearGroup.det_coe, mul_one]
  have hstarcontent : (matrixStar M).rankTwoContent = M.rankTwoContent := by
    simp only [Matrix.rankTwoContent, matrixStar, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ac_rfl
  have hcontent : H.rankTwoContent = 1 := by
    change (matrixStar M * U.1).rankTwoContent = 1
    rw [rankTwoContent_mul_sl, hstarcontent, hprimitive]
  obtain ⟨σ, hHσ⟩ :=
    exists_coxMatrix_of_isColumnHermiteNormalForm_aux H hHhnf hHdet hcontent
  refine ⟨slStar U, σ, ?_⟩
  change matrixStar U.1 * M = σ.mobiusMatrix
  have hstar := congrArg matrixStar hHσ
  rw [matrixStar_inclusionMatrix] at hstar
  change matrixStar (matrixStar M * U.1) = σ.mobiusMatrix at hstar
  rw [matrixStar_mul, matrixStar_involutive] at hstar
  exact hstar

end Cox
