import Mathlib
import XYin.Modularforms.Delta
import XYin.Test.jfunctionLaurent

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups
  PowerSeries SlashInvariantFormClass Real Function IntegralPowerSeries
open scoped Manifold

local notation "𝕢" => Periodic.qParam
local notation "ℍₒ" => upperHalfPlaneSet

noncomputable section

section modularEquation

noncomputable def jN (N : ℕ+) : ℍ → ℂ :=
  fun z => j (N • z)

lemma j_invariant (γ : SL(2, ℤ)) (z : ℍ) : j (γ • z) = j z := by
  have := congrFun (j_slashInvariant γ) z
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one] at this
  exact this

private def gamma0Conjugate (N : ℕ+) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N : ℕ)) : SL(2, ℤ) :=
  let a := γ 0 0; let b := γ 0 1; let c := γ 1 0; let d := γ 1 1
  ⟨!![a, ↑N * b; c / ↑N, d], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have hdvd : (↑N : ℤ) ∣ c :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
    have hdet : a * d - b * c = 1 := by
      have := γ.prop; rwa [Matrix.det_fin_two] at this
    rw [show ↑N * b * (c / ↑N) = b * (↑N * (c / ↑N)) from by ring]
    rw [Int.mul_ediv_cancel' hdvd]
    linarith⟩

private lemma natPosSMul_gamma0_comm (N : ℕ+) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N : ℕ)) (z : ℍ) :
    (N • (γ • z) : ℍ) = gamma0Conjugate N γ hγ • (N • z : ℍ) := by
  ext
  simp only [coe_specialLinearGroup_apply, gamma0Conjugate, Matrix.of_apply, natPosSMul_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  have hdvd : (↑N : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have hcN : (↑N : ℤ) * (γ 1 0 / ↑N) = γ 1 0 := Int.mul_ediv_cancel' hdvd
  have hR :
      (algebraMap ℤ ℝ) (γ 1 0 / ↑N) * (↑N : ℝ) = (algebraMap ℤ ℝ) (γ 1 0) := by
    rw [show (↑N : ℝ) = (algebraMap ℤ ℝ) (↑N : ℤ) from by simp [algebraMap_int_eq]]
    rw [← map_mul, mul_comm, hcN]
  have hC : (↑((algebraMap ℤ ℝ) (γ 1 0 / ↑N)) : ℂ) * ((↑N : ℂ) * ↑z) =
      (↑((algebraMap ℤ ℝ) (γ 1 0)) : ℂ) * ↑z := by
    rw [← mul_assoc, show (↑((algebraMap ℤ ℝ) (γ 1 0 / ↑N)) : ℂ) * ↑N =
      ↑((algebraMap ℤ ℝ) (γ 1 0)) from by exact_mod_cast hR]
  rw [hC, map_mul,
    show (algebraMap ℤ ℝ) (↑N : ℤ) = (↑N : ℝ) from by simp [algebraMap_int_eq]]
  push_cast
  rw [← mul_div_assoc]
  congr 1; ring

lemma jN_slashInvariant (N : ℕ+) (γ : CongruenceSubgroup.Gamma0 (N : ℕ)) :
    jN N ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = jN N := by
  ext z
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one, jN]
  rw [natPosSMul_gamma0_comm N γ γ.prop z]
  exact j_invariant _ _

/-- Right cosets of `Γ₀(N)` in `SL₂(ℤ)`, in the orientation used by Cox's
modular-equation product. -/
abbrev Gamma0RightCosets (N : ℕ+) :=
  Quotient (QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (N : ℕ)))

noncomputable instance gamma0RightCosetsFintype (N : ℕ+) :
    Fintype (Gamma0RightCosets N) := by
  letI : NeZero (N : ℕ) := ⟨PNat.ne_zero N⟩
  haveI : (CongruenceSubgroup.Gamma0 (N : ℕ)).FiniteIndex := by infer_instance
  letI : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (N : ℕ)) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  exact Fintype.ofEquiv (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (N : ℕ))
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel
      (s := CongruenceSubgroup.Gamma0 (N : ℕ))).symm

/-- The Cox root attached to a right coset: for representative `γ`, this is
`jN N (γ • z)`. -/
noncomputable def gamma0RightCosetEval (N : ℕ+) (c : Gamma0RightCosets N)
    (z : ℍ) : ℂ :=
  Quotient.liftOn c (fun γ : SL(2, ℤ) => jN N (γ • z)) fun x y hxy => by
    have hmem : y * x⁻¹ ∈ CongruenceSubgroup.Gamma0 (N : ℕ) :=
      QuotientGroup.rightRel_apply.mp hxy
    let δ : CongruenceSubgroup.Gamma0 (N : ℕ) := ⟨y * x⁻¹, hmem⟩
    have hy : y = (δ : SL(2, ℤ)) * x := by
      change y = (y * x⁻¹) * x
      group
    have hact : y • z = (δ : SL(2, ℤ)) • (x • z) := by
      rw [hy, mul_smul]
    have hinv := congrFun (jN_slashInvariant N δ) (x • z)
    simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one] at hinv
    calc
      jN N (x • z) = jN N ((δ : SL(2, ℤ)) • (x • z)) := hinv.symm
      _ = jN N (y • z) := by rw [← hact]

/-- Cox's right-coset product specialized at the second variable `j z`. -/
noncomputable def coxPhiAtJ (N : ℕ+) (z : ℍ) : Polynomial ℂ :=
  ∏ c : Gamma0RightCosets N,
    (Polynomial.X - Polynomial.C (gamma0RightCosetEval N c z))

theorem coxPhiAtJ_eval_jN (N : ℕ+) (z : ℍ) :
    Polynomial.eval (jN N z) (coxPhiAtJ N z) = 0 := by
  classical
  rw [coxPhiAtJ, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ
    (Quotient.mk _ (1 : SL(2, ℤ)) : Gamma0RightCosets N)) ?_
  simp [gamma0RightCosetEval]
  have hcoe : (↑(1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = 1 := by
    ext i j
    simp
  rw [hcoe, one_smul, sub_self]

theorem coxPhiAtJ_isRoot_jN (N : ℕ+) (z : ℍ) :
    (coxPhiAtJ N z).IsRoot (jN N z) := by
  simpa [Polynomial.IsRoot] using coxPhiAtJ_eval_jN N z

theorem coxPhiAtJ_monic (N : ℕ+) (z : ℍ) : (coxPhiAtJ N z).Monic := by
  classical
  simpa [coxPhiAtJ] using
    Polynomial.monic_prod_of_monic (Finset.univ : Finset (Gamma0RightCosets N))
      (fun c => Polynomial.X - Polynomial.C (gamma0RightCosetEval N c z))
      (fun c _ => Polynomial.monic_X_sub_C (gamma0RightCosetEval N c z))

theorem coxPhiAtJ_ne_zero (N : ℕ+) (z : ℍ) : coxPhiAtJ N z ≠ 0 :=
  (coxPhiAtJ_monic N z).ne_zero

noncomputable def gamma0RightCosetsMulEquiv (N : ℕ+) (δ : SL(2, ℤ)) :
    Gamma0RightCosets N ≃ Gamma0RightCosets N where
  toFun :=
    Quotient.map' (fun γ : SL(2, ℤ) => γ * δ) fun x y hxy => by
      rw [QuotientGroup.rightRel_apply] at hxy ⊢
      simpa [mul_assoc] using hxy
  invFun :=
    Quotient.map' (fun γ : SL(2, ℤ) => γ * δ⁻¹) fun x y hxy => by
      rw [QuotientGroup.rightRel_apply] at hxy ⊢
      simpa [mul_assoc] using hxy
  left_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro γ
    apply Quotient.sound
    change QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (N : ℕ))
      ((γ * δ) * δ⁻¹) γ
    rw [QuotientGroup.rightRel_apply]
    simp [mul_assoc]
  right_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro γ
    apply Quotient.sound
    change QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (N : ℕ))
      ((γ * δ⁻¹) * δ) γ
    rw [QuotientGroup.rightRel_apply]
    simp [mul_assoc]

theorem gamma0RightCosetEval_smul (N : ℕ+) (δ : SL(2, ℤ))
    (c : Gamma0RightCosets N) (z : ℍ) :
    gamma0RightCosetEval N c (δ • z) =
      gamma0RightCosetEval N (gamma0RightCosetsMulEquiv N δ c) z := by
  refine Quotient.inductionOn c ?_
  intro γ
  change
    jN N ((↑γ : GL (Fin 2) ℝ) • ((↑δ : GL (Fin 2) ℝ) • z)) =
      jN N ((↑(γ * δ) : GL (Fin 2) ℝ) • z)
  have hcoe : (↑(γ * δ) : GL (Fin 2) ℝ) =
      (↑γ : GL (Fin 2) ℝ) * (↑δ : GL (Fin 2) ℝ) := by
    ext i j
    simp
  rw [hcoe, mul_smul]

theorem coxPhiAtJ_sl2_smul (N : ℕ+) (δ : SL(2, ℤ)) (z : ℍ) :
    coxPhiAtJ N (δ • z) = coxPhiAtJ N z := by
  classical
  let e := gamma0RightCosetsMulEquiv N δ
  calc
    coxPhiAtJ N (δ • z) =
        ∏ c : Gamma0RightCosets N,
          (Polynomial.X - Polynomial.C (gamma0RightCosetEval N (e c) z)) := by
      simp only [coxPhiAtJ]
      refine Finset.prod_congr rfl ?_
      intro c _
      rw [gamma0RightCosetEval_smul]
    _ = coxPhiAtJ N z := by
      simpa [coxPhiAtJ, e] using
        (Equiv.prod_comp e
          (fun c : Gamma0RightCosets N =>
            Polynomial.X - Polynomial.C (gamma0RightCosetEval N c z)))

theorem coxPhiAtJ_coeff_sl2_smul (N : ℕ+) (δ : SL(2, ℤ)) (z : ℍ) (n : ℕ) :
    (coxPhiAtJ N (δ • z)).coeff n = (coxPhiAtJ N z).coeff n :=
  congrArg (fun P : Polynomial ℂ => P.coeff n) (coxPhiAtJ_sl2_smul N δ z)

/-- The three standard right-coset representatives for `Γ₀(2)` in `SL₂(ℤ)`. -/
def gamma0TwoRightCosetReps : Fin 3 → SL(2, ℤ) :=
  ![1, ModularGroup.S, ModularGroup.S * ModularGroup.T]

/-- The quotient classes of the three standard `Γ₀(2)` right-coset representatives. -/
noncomputable def gamma0TwoRightCosetRepQuotient (i : Fin 3) :
    Gamma0RightCosets (2 : ℕ+) :=
  Quotient.mk _ (gamma0TwoRightCosetReps i)

private lemma zmodTwo_eq_one_of_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exfalso
    exact hx rfl
  · rfl

theorem gamma0TwoRightCosetReps_surjective :
    Function.Surjective gamma0TwoRightCosetRepQuotient := by
  intro c
  refine Quotient.inductionOn c ?_
  intro γ
  by_cases hc : (γ 1 0 : ZMod 2) = 0
  · refine ⟨0, ?_⟩
    apply Quotient.sound
    change QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (2 : ℕ))
      (gamma0TwoRightCosetReps 0) γ
    rw [QuotientGroup.rightRel_apply]
    rw [CongruenceSubgroup.Gamma0_mem]
    simpa [gamma0TwoRightCosetReps] using hc
  · by_cases hd : (γ 1 1 : ZMod 2) = 0
    · refine ⟨1, ?_⟩
      apply Quotient.sound
      change QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (2 : ℕ))
        (gamma0TwoRightCosetReps 1) γ
      rw [QuotientGroup.rightRel_apply]
      rw [CongruenceSubgroup.Gamma0_mem]
      simpa [gamma0TwoRightCosetReps, ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]
        using hd
    · refine ⟨2, ?_⟩
      have hc1 : (γ 1 0 : ZMod 2) = 1 := zmodTwo_eq_one_of_ne_zero _ hc
      have hd1 : (γ 1 1 : ZMod 2) = 1 := zmodTwo_eq_one_of_ne_zero _ hd
      have hsum : (γ 1 0 : ZMod 2) + (γ 1 1 : ZMod 2) = 0 := by
        rw [hc1, hd1]
        decide
      apply Quotient.sound
      change QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (2 : ℕ))
        (gamma0TwoRightCosetReps 2) γ
      rw [QuotientGroup.rightRel_apply]
      rw [CongruenceSubgroup.Gamma0_mem]
      simpa [gamma0TwoRightCosetReps, ModularGroup.S, ModularGroup.T, Matrix.mul_apply,
        Fin.sum_univ_two] using hsum

theorem gamma0TwoRightCosetReps_injective :
    Function.Injective gamma0TwoRightCosetRepQuotient := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · have hrel := Quotient.exact hij
    change QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (2 : ℕ))
      (gamma0TwoRightCosetReps 0) (gamma0TwoRightCosetReps 1) at hrel
    rw [QuotientGroup.rightRel_apply] at hrel
    have hz := CongruenceSubgroup.Gamma0_mem.mp hrel
    simp [gamma0TwoRightCosetReps, ModularGroup.S, ModularGroup.T] at hz
  · have hrel := Quotient.exact hij
    change QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (2 : ℕ))
      (gamma0TwoRightCosetReps 0) (gamma0TwoRightCosetReps 2) at hrel
    rw [QuotientGroup.rightRel_apply] at hrel
    have hz := CongruenceSubgroup.Gamma0_mem.mp hrel
    simp [gamma0TwoRightCosetReps, ModularGroup.S, ModularGroup.T, Matrix.mul_apply,
      Fin.sum_univ_two] at hz
  · have hrel := Quotient.exact hij
    change QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (2 : ℕ))
      (gamma0TwoRightCosetReps 1) (gamma0TwoRightCosetReps 0) at hrel
    rw [QuotientGroup.rightRel_apply] at hrel
    have hz := CongruenceSubgroup.Gamma0_mem.mp hrel
    simp [gamma0TwoRightCosetReps, ModularGroup.S, ModularGroup.T] at hz
  · rfl
  · have hrel := Quotient.exact hij
    change QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (2 : ℕ))
      (gamma0TwoRightCosetReps 1) (gamma0TwoRightCosetReps 2) at hrel
    rw [QuotientGroup.rightRel_apply] at hrel
    have hz := CongruenceSubgroup.Gamma0_mem.mp hrel
    simp [gamma0TwoRightCosetReps, ModularGroup.S, ModularGroup.T, Matrix.mul_apply,
      Fin.sum_univ_two] at hz
  · have hrel := Quotient.exact hij
    change QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (2 : ℕ))
      (gamma0TwoRightCosetReps 2) (gamma0TwoRightCosetReps 0) at hrel
    rw [QuotientGroup.rightRel_apply] at hrel
    have hz := CongruenceSubgroup.Gamma0_mem.mp hrel
    simp [gamma0TwoRightCosetReps, ModularGroup.S, ModularGroup.T, Matrix.mul_apply,
      Fin.sum_univ_two] at hz
  · have hrel := Quotient.exact hij
    change QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (2 : ℕ))
      (gamma0TwoRightCosetReps 2) (gamma0TwoRightCosetReps 1) at hrel
    rw [QuotientGroup.rightRel_apply] at hrel
    have hz := CongruenceSubgroup.Gamma0_mem.mp hrel
    simp [gamma0TwoRightCosetReps, ModularGroup.S, ModularGroup.T, Matrix.mul_apply,
      Fin.sum_univ_two] at hz
  · rfl

/-- The three standard representatives enumerate the right cosets of `Γ₀(2)`. -/
noncomputable def gamma0TwoRightCosetsEquiv : Fin 3 ≃ Gamma0RightCosets (2 : ℕ+) :=
  Equiv.ofBijective gamma0TwoRightCosetRepQuotient
    ⟨gamma0TwoRightCosetReps_injective, gamma0TwoRightCosetReps_surjective⟩

theorem coxPhiAtJ_two_eq_fin3_product (z : ℍ) :
    coxPhiAtJ (2 : ℕ+) z =
      ∏ i : Fin 3,
        (Polynomial.X - Polynomial.C
          (gamma0RightCosetEval (2 : ℕ+) (gamma0TwoRightCosetsEquiv i) z)) := by
  classical
  simpa [coxPhiAtJ] using
    (Equiv.prod_comp gamma0TwoRightCosetsEquiv
      (fun c : Gamma0RightCosets (2 : ℕ+) =>
        Polynomial.X - Polynomial.C (gamma0RightCosetEval (2 : ℕ+) c z))).symm

theorem coxPhiAtJ_two_fin3_product_eval_jN (z : ℍ) :
    Polynomial.eval (jN (2 : ℕ+) z)
      (∏ i : Fin 3,
        (Polynomial.X - Polynomial.C
          (gamma0RightCosetEval (2 : ℕ+) (gamma0TwoRightCosetsEquiv i) z))) = 0 := by
  rw [← coxPhiAtJ_two_eq_fin3_product z]
  exact coxPhiAtJ_eval_jN (2 : ℕ+) z

/-- The upper-half-plane point with complex coordinate `z / 2`. -/
def halfUpper (z : ℍ) : ℍ :=
  ⟨(z : ℂ) / 2, by
    have hz : 0 < (z : ℂ).im := z.2
    simpa using div_pos hz (by norm_num : (0 : ℝ) < 2)⟩

theorem coe_halfUpper (z : ℍ) :
    ((halfUpper z : ℍ) : ℂ) = (z : ℂ) / 2 := rfl

/-- The upper-half-plane point with complex coordinate `(z + 1) / 2`. -/
def halfTranslateUpper (z : ℍ) : ℍ :=
  ⟨((z : ℂ) + 1) / 2, by
    have hz : 0 < ((z : ℂ) + 1).im := by simpa using z.2
    simpa using div_pos hz (by norm_num : (0 : ℝ) < 2)⟩

theorem coe_halfTranslateUpper (z : ℍ) :
    ((halfTranslateUpper z : ℍ) : ℂ) = ((z : ℂ) + 1) / 2 := rfl

theorem two_nsmul_halfUpper (z : ℍ) :
    (2 : ℕ+) • halfUpper z = z := by
  ext
  rw [natPosSMul_apply, coe_halfUpper]
  norm_num
  field_simp

theorem two_nsmul_halfTranslateUpper (z : ℍ) :
    (2 : ℕ+) • halfTranslateUpper z = ModularGroup.T • z := by
  ext
  calc
    (((2 : ℕ+) • halfTranslateUpper z : ℍ) : ℂ) = (z : ℂ) + 1 := by
      rw [natPosSMul_apply, coe_halfTranslateUpper]
      norm_num
      ring
    _ = ((ModularGroup.T • z : ℍ) : ℂ) := by
      change (z : ℂ) + 1 = ((ModularGroup.T ^ (1 : ℤ) • z : ℍ) : ℂ)
      rw [ModularGroup.coe_T_zpow_smul_eq]
      norm_num

theorem two_nsmul_modular_S_smul_halfUpper (z : ℍ) :
    (2 : ℕ+) • (ModularGroup.S • z) = ModularGroup.S • halfUpper z := by
  ext
  rw [natPosSMul_apply, UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_S_smul]
  change (2 : ℂ) * (-(z : ℂ))⁻¹ = (-((halfUpper z : ℍ) : ℂ))⁻¹
  rw [coe_halfUpper]
  have hz0 : (z : ℂ) ≠ 0 := by
    intro hz
    have him : (z : ℂ).im = 0 := by simp [hz]
    exact ne_of_gt z.2 him
  field_simp [hz0]

theorem two_nsmul_modular_ST_smul_halfTranslateUpper (z : ℍ) :
    (2 : ℕ+) • ((ModularGroup.S * ModularGroup.T) • z) =
      ModularGroup.S • halfTranslateUpper z := by
  ext
  rw [natPosSMul_apply, mul_smul, UpperHalfPlane.modular_S_smul,
    UpperHalfPlane.modular_S_smul]
  change (2 : ℂ) * (-((ModularGroup.T • z : ℍ) : ℂ))⁻¹ =
    (-((halfTranslateUpper z : ℍ) : ℂ))⁻¹
  rw [UpperHalfPlane.modular_T_smul, coe_halfTranslateUpper]
  simp [UpperHalfPlane.coe_vadd]
  have hz0 : (z : ℂ) + 1 ≠ 0 := by
    intro hz
    have him : ((z : ℂ) + 1).im = 0 := by simp [hz]
    have him_pos : 0 < ((z : ℂ) + 1).im := by simpa using z.2
    exact ne_of_gt him_pos him
  rw [show -(z : ℂ) + -1 = -((z : ℂ) + 1) by ring]
  field_simp [hz0]

theorem gamma0RightCosetEval_two_one (z : ℍ) :
    gamma0RightCosetEval (2 : ℕ+) (gamma0TwoRightCosetsEquiv 0) z =
      jN (2 : ℕ+) z := by
  simp [gamma0TwoRightCosetsEquiv, gamma0TwoRightCosetRepQuotient, gamma0TwoRightCosetReps,
    gamma0RightCosetEval]
  have hcoe : (↑(1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = 1 := by
    ext i j
    simp
  rw [hcoe, one_smul]

theorem gamma0RightCosetEval_two_S (z : ℍ) :
    gamma0RightCosetEval (2 : ℕ+) (gamma0TwoRightCosetsEquiv 1) z =
      j (halfUpper z) := by
  simp [gamma0TwoRightCosetsEquiv, gamma0TwoRightCosetRepQuotient, gamma0TwoRightCosetReps,
    gamma0RightCosetEval, jN]
  change j ((2 : ℕ+) • (ModularGroup.S • z)) = j (halfUpper z)
  rw [two_nsmul_modular_S_smul_halfUpper]
  exact j_invariant ModularGroup.S (halfUpper z)

theorem gamma0RightCosetEval_two_ST (z : ℍ) :
    gamma0RightCosetEval (2 : ℕ+) (gamma0TwoRightCosetsEquiv 2) z =
      j (halfTranslateUpper z) := by
  simp [gamma0TwoRightCosetsEquiv, gamma0TwoRightCosetRepQuotient, gamma0TwoRightCosetReps,
    gamma0RightCosetEval, jN]
  change j ((2 : ℕ+) • ((ModularGroup.S * ModularGroup.T) • z)) =
    j (halfTranslateUpper z)
  rw [two_nsmul_modular_ST_smul_halfTranslateUpper]
  exact j_invariant ModularGroup.S (halfTranslateUpper z)

noncomputable def coxPhiTwoExplicit (z : ℍ) : Polynomial ℂ :=
  (Polynomial.X - Polynomial.C (jN (2 : ℕ+) z)) *
  (Polynomial.X - Polynomial.C (j (halfUpper z))) *
  (Polynomial.X - Polynomial.C (j (halfTranslateUpper z)))

theorem coxPhiAtJ_two_eq_explicit (z : ℍ) :
    coxPhiAtJ (2 : ℕ+) z = coxPhiTwoExplicit z := by
  rw [coxPhiAtJ_two_eq_fin3_product]
  rw [Fin.prod_univ_three]
  norm_num [coxPhiTwoExplicit, gamma0RightCosetEval_two_one, gamma0RightCosetEval_two_S,
    gamma0RightCosetEval_two_ST]

theorem coxPhiTwoExplicit_eval_jN (z : ℍ) :
    Polynomial.eval (jN (2 : ℕ+) z) (coxPhiTwoExplicit z) = 0 := by
  rw [← coxPhiAtJ_two_eq_explicit z]
  exact coxPhiAtJ_eval_jN (2 : ℕ+) z

theorem coxPhiTwoExplicit_isRoot_jN (z : ℍ) :
    (coxPhiTwoExplicit z).IsRoot (jN (2 : ℕ+) z) := by
  simpa [Polynomial.IsRoot] using coxPhiTwoExplicit_eval_jN z

/-- Evaluation of function coefficients at a point of the upper half-plane. -/
def evalAtUpper (z : ℍ) : (ℍ → ℂ) →+* ℂ :=
  Pi.evalRingHom (fun _ : ℍ => ℂ) z

/-- Cox's right-coset product as a polynomial whose coefficients are functions on `ℍ`. -/
noncomputable def coxPhiFunction (N : ℕ+) : Polynomial (ℍ → ℂ) :=
  ∏ c : Gamma0RightCosets N,
    (Polynomial.X - Polynomial.C (fun z => gamma0RightCosetEval N c z))

theorem coxPhiFunction_map_eval (N : ℕ+) (z : ℍ) :
    (coxPhiFunction N).map (evalAtUpper z) = coxPhiAtJ N z := by
  classical
  simp [coxPhiFunction, coxPhiAtJ, evalAtUpper, Polynomial.map_prod]

theorem coxPhiFunction_coeff_apply (N : ℕ+) (n : ℕ) (z : ℍ) :
    (coxPhiFunction N).coeff n z = (coxPhiAtJ N z).coeff n := by
  rw [← coxPhiFunction_map_eval N z, Polynomial.coeff_map]
  rfl

theorem coxPhiFunction_eval_jN (N : ℕ+) :
    Polynomial.eval (jN N) (coxPhiFunction N) = 0 := by
  ext z
  have h := coxPhiAtJ_eval_jN N z
  rw [← coxPhiFunction_map_eval N z] at h
  have happly : evalAtUpper z (Polynomial.eval (jN N) (coxPhiFunction N)) = 0 := by
    rw [← Polynomial.eval₂_at_apply (p := coxPhiFunction N) (evalAtUpper z) (jN N)]
    simpa [evalAtUpper, Polynomial.eval_map] using h
  simpa [evalAtUpper] using happly

theorem coxPhiFunction_coeff_sl2_smul
    (N : ℕ+) (δ : SL(2, ℤ)) (n : ℕ) (z : ℍ) :
    (coxPhiFunction N).coeff n (δ • z) =
      (coxPhiFunction N).coeff n z := by
  rw [coxPhiFunction_coeff_apply, coxPhiFunction_coeff_apply]
  exact coxPhiAtJ_coeff_sl2_smul N δ z n

theorem coxPhiFunction_monic (N : ℕ+) : (coxPhiFunction N).Monic := by
  classical
  simpa [coxPhiFunction] using
    Polynomial.monic_prod_of_monic (Finset.univ : Finset (Gamma0RightCosets N))
      (fun c => Polynomial.X - Polynomial.C (fun z => gamma0RightCosetEval N c z))
      (fun c _ => Polynomial.monic_X_sub_C (fun z => gamma0RightCosetEval N c z))

noncomputable def qjN (N : ℕ+) : ℍ → ℂ :=
  fun z => qj (N • z)

lemma natPosSMul_ofComplex_coe (N : ℕ+) {w : ℂ} (hw : 0 < w.im) :
    (N • UpperHalfPlane.ofComplex w : ℍ) = UpperHalfPlane.ofComplex ((↑N : ℂ) * w) := by
  have hNw : 0 < ((↑N : ℂ) * w).im := by
    rw [Complex.mul_im]
    simp only [natCast_re, natCast_im, zero_mul, add_zero]
    exact mul_pos (Nat.cast_pos.mpr N.pos) hw
  apply UpperHalfPlane.ext
  rw [natPosSMul_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
    UpperHalfPlane.ofComplex_apply_of_im_pos hNw]

lemma qjN_periodic (N : ℕ+) : Periodic (qjN N ∘ UpperHalfPlane.ofComplex) (N : ℕ) := by
  have hqNN : Periodic (qj ∘ UpperHalfPlane.ofComplex) ((↑N : ℂ) * ↑N) := by
    have := qj_periodic.nat_mul ((N : ℕ) * (N : ℕ))
    simpa [Nat.cast_mul] using this
  intro w
  simp only [Function.comp, qjN]
  by_cases hw : 0 < Complex.im w
  · have hwN : 0 < Complex.im (w + ↑N) := by simp [Complex.add_im]; linarith
    have hkey := hqNN ((↑N : ℂ) * w)
    have hring : (↑N : ℂ) * w + (↑N : ℂ) * ↑N = (↑N : ℂ) * (w + ↑N) := by ring
    rw [hring] at hkey
    simp only [Function.comp] at hkey
    rw [natPosSMul_ofComplex_coe N hwN, natPosSMul_ofComplex_coe N hw]
    exact hkey
  · have hw0 := le_of_not_gt hw
    have hwN : Complex.im (w + ↑N) ≤ 0 := by simp [Complex.add_im]; linarith
    simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos hw0,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hwN]

lemma qjN_holomorphic (N : ℕ+) :
    ∀ z : ℂ, 0 < Complex.im z →
      DifferentiableAt ℂ (qjN N ∘ UpperHalfPlane.ofComplex) z := by
  intro z hz
  have hNz : 0 < Complex.im ((↑N : ℂ) * z) := by
    rw [Complex.mul_im]
    simp only [natCast_re, natCast_im, zero_mul, add_zero]
    exact mul_pos (Nat.cast_pos.mpr N.pos) hz
  have hqj := qj_holomorphic _ hNz
  have hN : DifferentiableAt ℂ (fun w => (↑N : ℂ) * w) z :=
    (differentiableAt_const _).mul differentiableAt_id
  refine (hqj.comp z hN).congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im) hz] with w hw
  simp only [Function.comp, qjN]
  rw [natPosSMul_ofComplex_coe N hw]

lemma qjN_MDifferentiable (N : ℕ+) : MDiff (qjN N) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  exact (qjN_holomorphic N z hz).differentiableWithinAt

lemma qjN_IsBoundedAtImInfty (N : ℕ+) :
    IsBoundedAtImInfty (qjN N) := by
  apply qj_IsBoundedAtImInfty.comp_tendsto
  rw [show atImInfty = Filter.comap UpperHalfPlane.im
    Filter.atTop from rfl, Filter.tendsto_comap_iff]
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr N.pos
  have him_eq :
      UpperHalfPlane.im ∘
          (fun x : ℍ => (N • x : ℍ)) =
        (fun x : ℝ => (↑N : ℝ) * x) ∘ UpperHalfPlane.im := by
    ext τ
    simp only [Function.comp, natPosSMul_apply, UpperHalfPlane.im, Complex.mul_im,
      Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  rw [him_eq]
  exact (Filter.Tendsto.const_mul_atTop hN_pos Filter.tendsto_id).comp Filter.tendsto_comap

lemma qjN_cuspFunction_analyticAt (N : ℕ+) :
    AnalyticAt ℂ (cuspFunction (N : ℕ) (qjN N)) 0 :=
  DifferentiableOn.analyticAt (fun q hq => (UpperHalfPlane.differentiableOn_cuspFunction_ball
    (Nat.cast_pos.mpr N.pos) (qjN_periodic N)
    (qjN_MDifferentiable N) (qjN_IsBoundedAtImInfty N)) q hq)
      (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

lemma jN_cuspFunction_eq (N : ℕ+) {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    cuspFunction (N : ℕ) (jN N) q =
      q⁻¹ ^ ((N : ℕ) * (N : ℕ)) * cuspFunction (N : ℕ) (qjN N) q := by
  have hN : (0 : ℝ) < (N : ℕ) := Nat.cast_pos.mpr N.pos
  have him := Periodic.im_invQParam_pos_of_norm_lt_one hN hq hq0
  let τ : ℍ := ⟨Periodic.invQParam (N : ℕ) q, him⟩
  have hjN_eq : cuspFunction (N : ℕ) (jN N) q = jN N τ := by
    change Periodic.cuspFunction (N : ℕ) _ q = _
    rw [Periodic.cuspFunction_eq_of_nonzero (N : ℕ) _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hqjN_eq : cuspFunction (N : ℕ) (qjN N) q = qjN N τ := by
    change Periodic.cuspFunction (N : ℕ) _ q = _
    rw [Periodic.cuspFunction_eq_of_nonzero (N : ℕ) _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hcexp :
      cexp (2 * ↑π * Complex.I *
        (↑(N • τ : ℍ) : ℂ)) = q ^ ((N : ℕ) * (N : ℕ)) := by
    rw [natPosSMul_apply]
    have hNnzC : (↑N : ℂ) ≠ 0 := by
      exact_mod_cast (PNat.ne_zero N)
    rw [show 2 * ↑π * Complex.I * ((↑N : ℂ) * (τ : ℂ)) = ↑((N : ℕ) * (N : ℕ)) *
      (2 * ↑π * Complex.I * (τ : ℂ) / ↑N) from by field_simp [hNnzC]; push_cast; ring,
      Complex.exp_nat_mul]
    congr 1
    simpa [τ, Periodic.qParam] using
      Periodic.qParam_right_inv (show ((N : ℕ) : ℝ) ≠ 0 by
        exact_mod_cast (PNat.ne_zero N)) hq0
  rw [hjN_eq, hqjN_eq]
  simp only [jN, qjN, qj, Pi.mul_apply]
  rw [hcexp, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq0), one_mul]

lemma jN_cuspFunction_Meromorphic (N : ℕ+) :
    MeromorphicAt (cuspFunction (N : ℕ) (jN N)) (0 : ℂ) := by
  have hqjN_mer : MeromorphicAt (cuspFunction (N : ℕ) (qjN N)) (0 : ℂ) := by
    change MeromorphicAt
      (Function.Periodic.cuspFunction (N : ℕ) (qjN N ∘ UpperHalfPlane.ofComplex)) 0
    exact (qjN_cuspFunction_analyticAt N).meromorphicAt
  have hpow : MeromorphicAt (fun q : ℂ => q⁻¹ ^ ((N : ℕ) * (N : ℕ))) (0 : ℂ) :=
    ((MeromorphicAt.id (0 : ℂ)).inv).pow _
  refine (hpow.mul hqjN_mer).congr ?_
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds (by simpa [Metric.ball, dist_eq_norm]
      using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  filter_upwards [hnorm, self_mem_nhdsWithin] with q hq hq'
  simp only [Pi.mul_apply]
  exact (jN_cuspFunction_eq N (by simpa using hq') hq).symm

/-- Packaged modular-function data available for `jN`: slash invariance on `Γ₀(N)` and
meromorphicity of the `q`-cusp function at `0`. -/
theorem jN_modular_data (N : ℕ+) :
    (∀ γ : CongruenceSubgroup.Gamma0 (N : ℕ),
      jN N ∣[(0 : ℤ)] (γ : SL(2, ℤ)) = jN N) ∧
    MeromorphicAt (cuspFunction (N : ℕ) (jN N)) (0 : ℂ) :=
  ⟨jN_slashInvariant N, jN_cuspFunction_Meromorphic N⟩

/-- `cuspFunction (N) (jN N)` is `q^(-(N^2))` times an analytic remainder on `‖q‖ < 1`. -/
theorem jN_exists_analytic_remainder (N : ℕ+) :
    ∃ F : ℂ → ℂ,
      AnalyticAt ℂ F 0 ∧
      ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 →
        cuspFunction (N : ℕ) (jN N) q =
          q⁻¹ ^ ((N : ℕ) * (N : ℕ)) * F q := by
  refine ⟨cuspFunction (N : ℕ) (qjN N), qjN_cuspFunction_analyticAt N, ?_⟩
  intro q hq0 hq
  simpa using jN_cuspFunction_eq N hq0 hq

/-- Level-`2` specialization of `jN_cuspFunction_eq`. -/
theorem jN_cuspFunction_eq_two {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    cuspFunction (2 : ℕ) (jN (2 : ℕ+)) q =
      q⁻¹ ^ (4 : ℕ) * cuspFunction (2 : ℕ) (qjN (2 : ℕ+)) q := by
  simpa using jN_cuspFunction_eq (N := (2 : ℕ+)) hq0 hq

lemma jN_Meromorphic (N : ℕ+) {z : ℍₒ} :
    DifferentiableAt ℂ (jN N ∘ UpperHalfPlane.ofComplex) z := by
  obtain ⟨z, hz⟩ := z
  have hz' := Set.mem_setOf.mp hz
  have hNz : 0 < Complex.im ((↑N : ℂ) * z) := by
    rw [Complex.mul_im]
    simp only [natCast_re, natCast_im, zero_mul, add_zero, Nat.cast_pos, N.pos,
        mul_pos_iff_of_pos_left]
    exact hz'
  have hE4 := UpperHalfPlane.mdifferentiableAt_iff.mp
    (ModularFormClass.holo E4 ⟨↑N * z, hNz⟩)
  have hΔ := UpperHalfPlane.mdifferentiableAt_iff.mp
    (ModularFormClass.holo Delta ⟨↑N * z, hNz⟩)
  have hΔ0 : (Delta ∘ UpperHalfPlane.ofComplex) (↑N * z) ≠ 0 := by
    simp only [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hNz, Delta_apply]
    exact Δ_ne_zero _
  have hj : DifferentiableAt ℂ (j ∘ UpperHalfPlane.ofComplex) (↑N * z) := by
    simpa [j, Function.comp] using (hE4.pow 3).div hΔ hΔ0
  have hcomp := hj.comp z (by
    change DifferentiableAt ℂ (fun w => (↑N : ℂ) * w) z
    exact differentiableAt_const _ |>.mul differentiableAt_id)
  have hEq : (jN N ∘ UpperHalfPlane.ofComplex)
      =ᶠ[nhds z] ((j ∘ UpperHalfPlane.ofComplex) ∘ fun w => (↑N : ℂ) * w) := by
    filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im) hz']
      with w hw
    have hNw : 0 < (↑N * w).im := by
      rw [Complex.mul_im]
      simp only [natCast_re, natCast_im, zero_mul, add_zero, Nat.cast_pos, N.pos,
        mul_pos_iff_of_pos_left]
      exact hw
    have hsmul :
        (N • UpperHalfPlane.ofComplex w : ℍ) = UpperHalfPlane.ofComplex ((↑N : ℂ) * w) :=
      natPosSMul_ofComplex_coe N hw
    simpa [Function.comp, jN, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos hNw] using congrArg j hsmul
  change DifferentiableAt ℂ (jN N ∘ UpperHalfPlane.ofComplex) z
  have hcomp' :
      DifferentiableAt ℂ ((j ∘ UpperHalfPlane.ofComplex) ∘ fun w => (↑N : ℂ) * w) z := by
    convert hcomp using 2
  exact hcomp'.congr_of_eventuallyEq hEq

end modularEquation
