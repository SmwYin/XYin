/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.HermiteNormalForm
import XYin.PhD.Cox.ModularFunction.LevelJ

/-!
# Cox matrices and right cosets

This file defines Cox's primitive upper-triangular representatives and identifies them with
right cosets of `Γ₀(m)` in `SL₂(ℤ)`. It also develops the induced coset action on modular
functions.
-/

open Complex Function MatrixGroups UpperHalfPlane

noncomputable section

namespace Cox

/-- Cox's finite set `C(m)` of primitive upper-triangular determinant-`m` matrices
`!![a, b; 0, d]` with `ad = m`, `0 ≤ b < d` and `gcd(a, b, d) = 1`. -/
@[ext]
structure CoxMatrix (m : ℕ+) where
  /-- The upper-left entry. -/
  a : ℕ
  /-- The upper-right entry. -/
  b : ℕ
  /-- The lower-right entry. -/
  d : ℕ
  a_pos : 0 < a
  determinant : a * d = (m : ℕ)
  b_lt : b < d
  primitive : Nat.gcd (Nat.gcd a b) d = 1

namespace CoxMatrix

variable {m : ℕ+}

theorem d_pos (σ : CoxMatrix m) : 0 < σ.d :=
  pos_of_mul_pos_right (σ.determinant ▸ m.pos) (Nat.zero_le σ.a)

theorem a_dvd (σ : CoxMatrix m) : σ.a ∣ (m : ℕ) :=
  ⟨σ.d, σ.determinant.symm⟩

theorem d_dvd (σ : CoxMatrix m) : σ.d ∣ (m : ℕ) :=
  Dvd.intro_left σ.a σ.determinant

theorem div_d (σ : CoxMatrix m) : (m : ℕ) / σ.d = σ.a := by
  rw [← σ.determinant, Nat.mul_div_cancel _ σ.d_pos]

theorem div_a (σ : CoxMatrix m) : (m : ℕ) / σ.a = σ.d := by
  rw [← σ.determinant, Nat.mul_div_cancel_left _ σ.a_pos]

theorem a_le (σ : CoxMatrix m) : σ.a ≤ (m : ℕ) :=
  Nat.le_of_dvd m.pos σ.a_dvd

theorem d_le (σ : CoxMatrix m) : σ.d ≤ (m : ℕ) :=
  Nat.le_of_dvd m.pos σ.d_dvd

/-- Primitivity in the form used for counting: `gcd(a, d)` is coprime to `b`. -/
theorem coprime_gcd_b (σ : CoxMatrix m) : (Nat.gcd σ.a σ.d).Coprime σ.b := by
  simpa only [Nat.Coprime, Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc] using σ.primitive

/-- Cox's matrix acting on the upper half-plane. -/
def mobiusMatrix (σ : CoxMatrix m) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(σ.a : ℤ), (σ.b : ℤ); 0, (σ.d : ℤ)]

/-- The column-HNF inclusion matrix for the associated sublattice `[d,aτ+b]`. -/
def inclusionMatrix (σ : CoxMatrix m) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(σ.d : ℤ), (σ.b : ℤ); 0, (σ.a : ℤ)]

@[simp] theorem inclusionMatrix_zero_zero (σ : CoxMatrix m) : σ.inclusionMatrix 0 0 = σ.d :=
  rfl

@[simp] theorem inclusionMatrix_zero_one (σ : CoxMatrix m) : σ.inclusionMatrix 0 1 = σ.b :=
  rfl

@[simp] theorem inclusionMatrix_one_zero (σ : CoxMatrix m) : σ.inclusionMatrix 1 0 = 0 :=
  rfl

@[simp] theorem inclusionMatrix_one_one (σ : CoxMatrix m) : σ.inclusionMatrix 1 1 = σ.a :=
  rfl

/-- The Möbius matrix is the anti-transpose of the inclusion matrix. -/
theorem antiTranspose_inclusionMatrix (σ : CoxMatrix m) :
    σ.inclusionMatrix.antiTranspose = σ.mobiusMatrix :=
  rfl

/-- The inclusion matrix is the anti-transpose of the Möbius matrix. -/
theorem antiTranspose_mobiusMatrix (σ : CoxMatrix m) :
    σ.mobiusMatrix.antiTranspose = σ.inclusionMatrix :=
  rfl

theorem inclusionMatrix_isColumnHermiteNormalForm (σ : CoxMatrix m) :
    σ.inclusionMatrix.IsColumnHermiteNormalForm :=
  Matrix.isColumnHermiteNormalForm_fin_two (by exact_mod_cast σ.d_pos)
    (by exact_mod_cast σ.a_pos) (Int.natCast_nonneg σ.b) (by exact_mod_cast σ.b_lt)

theorem inclusionMatrix_det (σ : CoxMatrix m) :
    σ.inclusionMatrix.det = (m : ℕ) := by
  rw [σ.inclusionMatrix_isColumnHermiteNormalForm.det_eq, ← σ.determinant]
  simp [mul_comm]

theorem inclusionMatrix_content_eq_one (σ : CoxMatrix m) :
    Matrix.rankTwoContent σ.inclusionMatrix = 1 := by
  simpa [σ.inclusionMatrix_isColumnHermiteNormalForm.rankTwoContent_eq] using σ.primitive

/-- A Cox representative is determined by its sublattice inclusion matrix. -/
theorem inclusionMatrix_injective :
    Function.Injective (inclusionMatrix (m := m)) := fun σ τ h ↦
  CoxMatrix.ext (by simpa using congrFun (congrFun h 1) 1)
    (by simpa using congrFun (congrFun h 0) 1) (by simpa using congrFun (congrFun h 0) 0)

/-- The Cox matrix whose inclusion matrix is a given column Hermite normal form of
determinant `m` and content `1`. -/
def ofColumnHNF (H : Matrix (Fin 2) (Fin 2) ℤ) (hH : H.IsColumnHermiteNormalForm)
    (hdet : H.det = (m : ℤ)) (hcontent : H.rankTwoContent = 1) : CoxMatrix m where
  a := (H 1 1).natAbs
  b := (H 0 1).natAbs
  d := (H 0 0).natAbs
  a_pos := Int.natAbs_pos.mpr hH.one_one_pos.ne'
  determinant := by
    rw [← Int.natAbs_mul, mul_comm, ← hH.det_eq, hdet, Int.natAbs_natCast]
  b_lt := Int.natAbs_lt_natAbs_of_nonneg_of_lt hH.zero_one_mem.1 hH.zero_one_mem.2
  primitive := hH.rankTwoContent_eq.symm.trans hcontent

section ofColumnHNF

variable (H : Matrix (Fin 2) (Fin 2) ℤ) (hH : H.IsColumnHermiteNormalForm)
  (hdet : H.det = (m : ℤ)) (hcontent : H.rankTwoContent = 1)

@[simp] theorem ofColumnHNF_a : (ofColumnHNF H hH hdet hcontent).a = (H 1 1).natAbs := rfl

@[simp] theorem ofColumnHNF_b : (ofColumnHNF H hH hdet hcontent).b = (H 0 1).natAbs := rfl

@[simp] theorem ofColumnHNF_d : (ofColumnHNF H hH hdet hcontent).d = (H 0 0).natAbs := rfl

@[simp]
theorem inclusionMatrix_ofColumnHNF : (ofColumnHNF H hH hdet hcontent).inclusionMatrix = H := by
  conv_rhs => rw [hH.eq_fin_two]
  simp [inclusionMatrix, abs_of_pos hH.zero_zero_pos, abs_of_nonneg hH.zero_one_mem.1,
    abs_of_pos hH.one_one_pos]

theorem mobiusMatrix_ofColumnHNF :
    (ofColumnHNF H hH hdet hcontent).mobiusMatrix = H.antiTranspose := by
  rw [← antiTranspose_inclusionMatrix, inclusionMatrix_ofColumnHNF]

end ofColumnHNF

/-- The Möbius action `(aτ+b)/d`. -/
def act (σ : CoxMatrix m) (τ : ℍ) : ℍ :=
  ⟨((σ.a : ℂ) * (τ : ℂ) + (σ.b : ℂ)) / (σ.d : ℂ), by
    simpa using div_pos (mul_pos (Nat.cast_pos.mpr σ.a_pos) τ.im_pos)
      (Nat.cast_pos.mpr σ.d_pos)⟩

@[simp] theorem coe_act (σ : CoxMatrix m) (τ : ℍ) :
    ((σ.act τ : ℍ) : ℂ) =
      ((σ.a : ℂ) * (τ : ℂ) + (σ.b : ℂ)) / (σ.d : ℂ) := rfl

/-- The Cox action is the affine transform `τ ↦ (b + aτ) / d`. -/
theorem affineUpperHalfPlane_eq_act (σ : CoxMatrix m) (τ : ℍ) :
    affineUpperHalfPlane σ.a σ.d σ.a_pos σ.d_pos σ.b τ = σ.act τ := by
  have hd : (σ.d : ℂ) ≠ 0 := by exact_mod_cast σ.d_pos.ne'
  ext
  simp only [coe_affineUpperHalfPlane, coe_act, Complex.ofReal_natCast, Int.cast_natCast]
  field_simp
  ring

/-- If `γ · M` is the Möbius matrix of `σ` for some `γ ∈ SL₂(ℤ)`, then `σ` acts on `τ` as `γ`
acts on the Möbius transform `w = (M₀₀ τ + M₀₁) / (M₁₀ τ + M₁₁)`. -/
theorem act_eq_smul_of_mul_eq (σ : CoxMatrix m) {γ : SL(2, ℤ)}
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : γ.1 * M = σ.mobiusMatrix) (τ w : ℍ)
    (hw : (w : ℂ) = ((M 0 0 : ℂ) * τ + M 0 1) / ((M 1 0 : ℂ) * τ + M 1 1)) :
    σ.act τ = γ • w := by
  have hD : (M 1 0 : ℂ) * τ + M 1 1 ≠ 0 := fun h0 ↦ by
    have him := w.im_pos
    rw [UpperHalfPlane.im, hw, h0, div_zero, Complex.zero_im] at him
    exact lt_irrefl 0 him
  have hD' : (τ : ℂ) * M 1 0 + M 1 1 ≠ 0 := by rwa [mul_comm]
  have h00 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hM 0) 0)
  have h01 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hM 0) 1)
  have h10 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hM 1) 0)
  have h11 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hM 1) 1)
  simp only [mobiusMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h01 h10 h11
  push_cast at h00 h01 h10 h11
  apply UpperHalfPlane.ext
  rw [coe_act, UpperHalfPlane.coe_specialLinearGroup_apply]
  change _ = (((γ 0 0 : ℤ) : ℂ) * (w : ℂ) + (γ 0 1 : ℤ)) /
    (((γ 1 0 : ℤ) : ℂ) * (w : ℂ) + (γ 1 1 : ℤ))
  have hnum : ((γ 0 0 : ℤ) : ℂ) * (w : ℂ) + (γ 0 1 : ℤ) =
      ((σ.a : ℂ) * τ + σ.b) / ((M 1 0 : ℂ) * τ + M 1 1) := by
    rw [hw]
    field_simp
    linear_combination (τ : ℂ) * h00 + h01
  have hden : ((γ 1 0 : ℤ) : ℂ) * (w : ℂ) + (γ 1 1 : ℤ) =
      (σ.d : ℂ) / ((M 1 0 : ℂ) * τ + M 1 1) := by
    rw [hw]
    field_simp
    linear_combination (τ : ℂ) * h10 + h11
  rw [hnum, hden, div_div_div_cancel_right₀ hD]

/-- A bounded encoding used to obtain the finite type structure on `C(m)`. -/
def toFin (σ : CoxMatrix m) :
    Fin ((m : ℕ) + 1) × Fin ((m : ℕ) + 1) × Fin ((m : ℕ) + 1) :=
  (⟨σ.a, by have := σ.a_le; omega⟩,
   ⟨σ.b, by have := σ.b_lt; have := σ.d_le; omega⟩,
   ⟨σ.d, by have := σ.d_le; omega⟩)

theorem toFin_injective : Function.Injective (toFin (m := m)) := fun _ _ h ↦
  CoxMatrix.ext (congrArg (·.1.val) h) (congrArg (·.2.1.val) h) (congrArg (·.2.2.val) h)

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
  refine Fintype.one_lt_card_iff.mpr ⟨σ, sigmaZero m, fun h ↦ ?_⟩
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

private def determinantScale (m : ℕ+) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(m : ℤ), 0; 0, 1]

private def determinantScaleDual (m : ℕ+) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 0, (m : ℤ)]

private theorem antiTranspose_determinantScale (m : ℕ+) :
    (determinantScale m).antiTranspose = determinantScaleDual m :=
  rfl

private theorem determinantScale_mul_eq (m : ℕ+) (γ : SL(2, ℤ)) :
    determinantScale m * γ.1 = !![(m : ℤ) * γ 0 0, (m : ℤ) * γ 0 1; γ 1 0, γ 1 1] := by
  conv_lhs => rw [Matrix.eta_fin_two γ.1]
  simp [determinantScale]

private def coxInput (m : ℕ+) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  (determinantScale m * γ.1).antiTranspose

private theorem coxInput_eq (m : ℕ+) (γ : SL(2, ℤ)) :
    coxInput m γ =
      !![γ 1 1, (m : ℤ) * γ 0 1; γ 1 0, (m : ℤ) * γ 0 0] := by
  rw [coxInput, determinantScale_mul_eq]
  rfl

private theorem coxInput_det (m : ℕ+) (γ : SL(2, ℤ)) :
    (coxInput m γ).det = (m : ℤ) := by
  rw [coxInput, Matrix.det_antiTranspose, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe,
    mul_one, determinantScale, Matrix.det_fin_two_of]
  ring

private theorem coxInput_content_eq_one (m : ℕ+) (γ : SL(2, ℤ)) :
    Matrix.rankTwoContent (coxInput m γ) = 1 := by
  have hcop := ModularGroup.bottom_row_coprime γ
  rw [Int.isCoprime_iff_gcd_eq_one] at hcop
  change Nat.gcd (γ 1 0).natAbs (γ 1 1).natAbs = 1 at hcop
  rw [coxInput_eq]
  exact Nat.eq_one_of_dvd_one <| (Nat.dvd_gcd (Matrix.rankTwoContent_dvd_entry _ 1 0)
    (Matrix.rankTwoContent_dvd_entry _ 0 0)).trans hcop.dvd

private def slStar (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨γ.1.antiTranspose, by simp⟩

private theorem coe_slStar (γ : SL(2, ℤ)) : (slStar γ).1 = γ.1.antiTranspose :=
  rfl

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
  obtain ⟨U, hU⟩ := (coxInput m γ).exists_right_mul_SL2_isColumnHermiteNormalForm (by
    rw [coxInput_det]
    exact_mod_cast PNat.pos m)
  refine ⟨.ofColumnHNF _ hU ?_ ?_, U, (CoxMatrix.inclusionMatrix_ofColumnHNF ..).symm⟩
  · rw [Matrix.det_mul, coxInput_det, Matrix.SpecialLinearGroup.det_coe, mul_one]
  · rw [Matrix.rankTwoContent_mul_of_isUnit_det _ (by simp), coxInput_content_eq_one]

private theorem coxMatrix_reduction_unique (m : ℕ+) (γ : SL(2, ℤ))
    {σ τ : CoxMatrix m} {U V : SL(2, ℤ)}
    (hσ : coxInput m γ * U.1 = σ.inclusionMatrix)
    (hτ : coxInput m γ * V.1 = τ.inclusionMatrix) : σ = τ := by
  refine CoxMatrix.inclusionMatrix_injective <|
    σ.inclusionMatrix_isColumnHermiteNormalForm.eq_of_mul_isUnit_det
      τ.inclusionMatrix_isColumnHermiteNormalForm (U := (U⁻¹ * V).1)
      (by rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one) ?_
  rw [← hσ, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc,
    Matrix.SpecialLinearGroup.mul_coe_mul_coe_inv, hτ]

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
    apply coxMatrix_reduction_unique m γ (coxReduction_spec m γ)
      (V := W * coxReductionMatrix m δ)
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, ← hW]
    exact coxReduction_spec m δ
  · intro hrep
    apply rightRel_of_coxInput_eq_mul m γ δ
      (coxReductionMatrix m γ * (coxReductionMatrix m δ)⁻¹)
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, coxReduction_spec, hrep,
      ← coxReduction_spec, Matrix.SpecialLinearGroup.mul_coe_mul_coe_inv]

private theorem coxRepresentative_normalization (m : ℕ+) (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ),
      δ.1 * !![(m : ℤ) * γ 0 0, (m : ℤ) * γ 0 1; γ 1 0, γ 1 1] =
        (coxRepresentative m γ).mobiusMatrix := by
  refine ⟨slStar (coxReductionMatrix m γ), ?_⟩
  have h := congrArg Matrix.antiTranspose (coxReduction_spec m γ)
  rwa [Matrix.antiTranspose_mul, coxInput, Matrix.antiTranspose_antiTranspose,
    determinantScale_mul_eq, CoxMatrix.antiTranspose_inclusionMatrix] at h

private theorem coxRepresentative_one (m : ℕ+) :
    coxRepresentative m (1 : SL(2, ℤ)) = sigmaZero m := by
  apply coxMatrix_reduction_unique m 1 (coxReduction_spec m 1) (V := (1 : SL(2, ℤ)))
  simp [coxInput_eq, sigmaZero, CoxMatrix.inclusionMatrix]

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
  have hdet := L.prop
  rw [Matrix.det_fin_two] at hdet
  have hN00 : N 0 0 = 1 := by
    simp only [N, Matrix.mul_apply, Matrix.SpecialLinearGroup.SL2_inv_expl, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hM00, hM10, ← hL00, ← hL10]
    linear_combination hdet
  have hN10 : N 1 0 = 0 := by
    simp only [N, Matrix.mul_apply, Matrix.SpecialLinearGroup.SL2_inv_expl, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hM00, hM10, ← hL00, ← hL10]
    ring
  have hN11 : N 1 1 = (m : ℤ) := by
    have hNdet : N.det = (m : ℤ) := by
      simp [N, M, Matrix.det_mul, σ.inclusionMatrix_det, -Matrix.SpecialLinearGroup.coe_inv]
    simpa [Matrix.det_fin_two, hN00, hN10] using hNdet
  let R₂ : SL(2, ℤ) :=
    ⟨!![1, -N 0 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  refine ⟨L, R₁ * R₂, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc,
    Matrix.mul_assoc (L⁻¹).1 σ.inclusionMatrix R₁.1]
  change N * R₂.1 = determinantScaleDual m
  rw [Matrix.eta_fin_two N, hN00, hN10, hN11]
  simp [R₂, determinantScaleDual]

private theorem coxRepresentative_surjective (m : ℕ+) :
    Function.Surjective (coxRepresentative m) := by
  intro σ
  obtain ⟨L, R, hnorm⟩ := coxMatrix_smith_normalization σ
  refine ⟨slStar L, ?_⟩
  apply coxMatrix_reduction_unique m (slStar L) (coxReduction_spec m (slStar L)) (V := R⁻¹)
  rw [coxInput, coe_slStar, Matrix.antiTranspose_mul, Matrix.antiTranspose_antiTranspose,
    antiTranspose_determinantScale, ← hnorm, ← Matrix.mul_assoc L.1,
    Matrix.SpecialLinearGroup.mul_coe_mul_coe_inv,
    Matrix.SpecialLinearGroup.coe_mul_coe_inv_mul]

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

private theorem coxMatrixEquivRightCosets_coxRepresentative
    (m : ℕ+) (γ : SL(2, ℤ)) :
    coxMatrixEquivRightCosets m (coxRepresentative m γ) = Quotient.mk'' γ := by
  apply (Equiv.ofBijective (rightCosetToCoxMatrix m)
    (rightCosetToCoxMatrix_bijective m)).symm_apply_eq.mpr
  rfl

/-- Translate a `Γ₀(m)`-modular function by a right coset; invariance makes this independent
of the representative. -/
noncomputable def rightCosetTranslate (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) (c : Gamma0RightCosets m) (τ : ℍ) : ℂ :=
  Quotient.liftOn c (fun γ : SL(2, ℤ) ↦ f (γ • τ)) fun γ δ hγδ ↦ by
    simpa [mul_smul] using
      (hf.apply_smul ⟨δ * γ⁻¹, QuotientGroup.rightRel_apply.mp hγδ⟩ (γ • τ)).symm

@[simp]
theorem rightCosetTranslate_mk (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) (γ : SL(2, ℤ)) (τ : ℍ) :
    rightCosetTranslate m hf (Quotient.mk'' γ) τ = f (γ • τ) :=
  rfl

/-- The conjugate `j(m γ τ)` attached to a right coset. -/
noncomputable def rightCosetEval (m : ℕ+) (c : Gamma0RightCosets m) (τ : ℍ) : ℂ :=
  rightCosetTranslate m (levelJ_cuspData m) c τ

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
    change Quotient.mk'' ((γ * δ) * δ⁻¹) = Quotient.mk'' γ
    simp [mul_assoc]
  right_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro γ
    change Quotient.mk'' ((γ * δ⁻¹) * δ) = Quotient.mk'' γ
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
    (hf : CuspData m f) (δ : SL(2, ℤ))
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
  exact rightCosetTranslate_smul m (levelJ_cuspData m) δ c τ

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
  set σ := coxRepresentative m γ
  rw [levelJ_smul_eq_j_affine m γ δ σ.a σ.d σ.a_pos σ.d_pos σ.b hδ,
    σ.affineUpperHalfPlane_eq_act]

/-- The distinguished Cox matrix corresponds to the identity right coset, so translating by
it leaves a modular function unchanged. -/
theorem rightCosetTranslate_sigmaZero (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) (τ : ℍ) :
    rightCosetTranslate m hf (coxMatrixEquivRightCosets m (sigmaZero m)) τ = f τ := by
  rw [coxMatrixEquivRightCosets_sigmaZero, rightCosetTranslate_mk]
  simp

/-- The distinguished Cox matrix acts as `τ ↦ mτ`, so it recovers the level transform. -/
theorem j_act_sigmaZero (m : ℕ+) :
    (fun τ ↦ j ((sigmaZero m).act τ)) = levelJ m := by
  funext τ
  congr 1
  apply UpperHalfPlane.ext
  simp [sigmaZero, CoxMatrix.act]

/-- A primitive integer matrix of positive determinant has a Cox upper-triangular representative
after left multiplication by an element of `SL₂(ℤ)` (Report Lemma 5.8). -/
theorem exists_sl2_mul_eq_coxMatrix {m : ℕ+}
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = (m : ℤ))
    (hprimitive : Matrix.rankTwoContent M = 1) :
    ∃ γ : SL(2, ℤ), ∃ σ : CoxMatrix m, γ.1 * M = σ.mobiusMatrix := by
  obtain ⟨γ, a, b, d, ha, hd, hb, -, hγ⟩ :=
    M.exists_SL2_mul_eq_upperTriangular (by rw [hdet]; positivity)
  have hH : (γ.1 * M).antiTranspose.IsColumnHermiteNormalForm := by
    rw [hγ]
    exact Matrix.isColumnHermiteNormalForm_fin_two hd ha hb.1 hb.2
  refine ⟨γ, .ofColumnHNF _ hH (by simp [hdet]) ?_, ?_⟩
  · rw [Matrix.rankTwoContent_antiTranspose, Matrix.rankTwoContent_isUnit_det_mul (by simp),
      hprimitive]
  · rw [CoxMatrix.mobiusMatrix_ofColumnHNF, Matrix.antiTranspose_antiTranspose]

end Cox
