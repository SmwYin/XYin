import Mathlib
import XYin.Test.JLevelN.JN

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups
  PowerSeries SlashInvariantFormClass Real Function IntegralPowerSeries
open scoped Manifold

/-!
# Cox right cosets and the right-coset product

This file contains the quotient/right-coset API used as the Lean counterpart of
Cox Lemma 11.11.  It also defines the Cox product from equation (11.14), both
pointwise as `coxPhiAtJ` and as the function-valued polynomial `coxPhiFunction`.
-/

local notation "𝕢" => Periodic.qParam
local notation "ℍₒ" => upperHalfPlaneSet

noncomputable section

section modularEquation

/-! ## Cox right-coset product

This is the right-coset version of Cox Lemma 11.11 and equation (11.14).  We
work directly with finite quotients rather than first enumerating Cox's `C(m)`.
-/

section CoxRightCosets

/-- Right cosets of `Γ₀(N)` in `SL₂(ℤ)`, the quotient side of Cox
Lemma 11.11 used in the modular-equation product. -/
abbrev Gamma0RightCosets (N : ℕ+) :=
  Quotient (QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 (N : ℕ)))

/-- Finiteness of the Cox right-coset quotient, using finite index of `Γ₀(N)`. -/
noncomputable instance gamma0RightCosetsFintype (N : ℕ+) :
    Fintype (Gamma0RightCosets N) := by
  letI : NeZero (N : ℕ) := ⟨PNat.ne_zero N⟩
  haveI : (CongruenceSubgroup.Gamma0 (N : ℕ)).FiniteIndex := by infer_instance
  letI : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (N : ℕ)) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  exact Fintype.ofEquiv (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (N : ℕ))
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel
      (s := CongruenceSubgroup.Gamma0 (N : ℕ))).symm

/-- The Cox root attached to a right coset.  For representative `γ`, this is
`jN N (γ • z)`, matching the factors in Cox equation (11.14). -/
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

/-- Cox equation (11.14), specialised at the second variable `j z`, as a
pointwise product over right cosets. -/
noncomputable def coxPhiAtJ (N : ℕ+) (z : ℍ) : Polynomial ℂ :=
  ∏ c : Gamma0RightCosets N,
    (Polynomial.X - Polynomial.C (gamma0RightCosetEval N c z))

/-- The root relation from Cox equation (11.14): the product vanishes at
`X = jN N z`. -/
theorem coxPhiAtJ_eval_jN (N : ℕ+) (z : ℍ) :
    Polynomial.eval (jN N z) (coxPhiAtJ N z) = 0 := by
  classical
  rw [coxPhiAtJ, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ
    (Quotient.mk _ (1 : SL(2, ℤ)) : Gamma0RightCosets N)) ?_
  simp [gamma0RightCosetEval]

/-- The Cox pointwise product has `jN N z` as a root. -/
theorem coxPhiAtJ_isRoot_jN (N : ℕ+) (z : ℍ) :
    (coxPhiAtJ N z).IsRoot (jN N z) := by
  simpa [Polynomial.IsRoot] using coxPhiAtJ_eval_jN N z

/-- Cox's pointwise right-coset product is monic. -/
theorem coxPhiAtJ_monic (N : ℕ+) (z : ℍ) : (coxPhiAtJ N z).Monic := by
  classical
  simpa [coxPhiAtJ] using
    Polynomial.monic_prod_of_monic (Finset.univ : Finset (Gamma0RightCosets N))
      (fun c => Polynomial.X - Polynomial.C (gamma0RightCosetEval N c z))
      (fun c _ => Polynomial.monic_X_sub_C (gamma0RightCosetEval N c z))

/-- Cox's pointwise right-coset product is nonzero because it is monic. -/
theorem coxPhiAtJ_ne_zero (N : ℕ+) (z : ℍ) : coxPhiAtJ N z ≠ 0 :=
  (coxPhiAtJ_monic N z).ne_zero

/-- Right multiplication by an `SL₂(ℤ)` element permutes the Cox right cosets
from Lemma 11.11. -/
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

/-- Compatibility of Cox roots with the right-coset reindexing behind
equation (11.14). -/
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

/-- Cox equation (11.14) is invariant under the `SL₂(ℤ)` action on `τ`, by
reindexing the right-coset product. -/
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

/-- Coefficients of the pointwise Cox product are invariant under `SL₂(ℤ)`. -/
theorem coxPhiAtJ_coeff_sl2_smul (N : ℕ+) (δ : SL(2, ℤ)) (z : ℍ) (n : ℕ) :
    (coxPhiAtJ N (δ • z)).coeff n = (coxPhiAtJ N z).coeff n :=
  congrArg (fun P : Polynomial ℂ => P.coeff n) (coxPhiAtJ_sl2_smul N δ z)

end CoxRightCosets

/-! ## Function-valued Cox product

This packages Cox equation (11.14) with coefficients as functions on `ℍ`, so
coefficient modularity can be proved before replacing those functions by `P(j)`.
-/

section FunctionValuedProduct

/-- Evaluation of function coefficients at a point of the upper half-plane. -/
def evalAtUpper (z : ℍ) : (ℍ → ℂ) →+* ℂ :=
  Pi.evalRingHom (fun _ : ℍ => ℂ) z

/-- Cox equation (11.14) as a polynomial whose coefficients are functions on
`ℍ`, before proving those coefficients are polynomials in `j`. -/
noncomputable def coxPhiFunction (N : ℕ+) : Polynomial (ℍ → ℂ) :=
  ∏ c : Gamma0RightCosets N,
    (Polynomial.X - Polynomial.C (fun z => gamma0RightCosetEval N c z))

/-- Point evaluation of the function-valued Cox product recovers the
specialised product in Cox equation (11.14). -/
theorem coxPhiFunction_map_eval (N : ℕ+) (z : ℍ) :
    (coxPhiFunction N).map (evalAtUpper z) = coxPhiAtJ N z := by
  classical
  simp [coxPhiFunction, coxPhiAtJ, evalAtUpper, Polynomial.map_prod]

/-- Coefficients of the function-valued Cox product evaluate to pointwise coefficients. -/
theorem coxPhiFunction_coeff_apply (N : ℕ+) (n : ℕ) (z : ℍ) :
    (coxPhiFunction N).coeff n z = (coxPhiAtJ N z).coeff n := by
  rw [← coxPhiFunction_map_eval N z, Polynomial.coeff_map]
  rfl

/-- Function-valued form of the root relation in Cox equation (11.14). -/
theorem coxPhiFunction_eval_jN (N : ℕ+) :
    Polynomial.eval (jN N) (coxPhiFunction N) = 0 := by
  ext z
  have h := coxPhiAtJ_eval_jN N z
  rw [← coxPhiFunction_map_eval N z] at h
  have happly : evalAtUpper z (Polynomial.eval (jN N) (coxPhiFunction N)) = 0 := by
    rw [← Polynomial.eval₂_at_apply (p := coxPhiFunction N) (evalAtUpper z) (jN N)]
    simpa [evalAtUpper, Polynomial.eval_map] using h
  simpa [evalAtUpper] using happly

/-- Coefficients of the function-valued Cox product are invariant under `SL₂(ℤ)`. -/
theorem coxPhiFunction_coeff_sl2_smul
    (N : ℕ+) (δ : SL(2, ℤ)) (n : ℕ) (z : ℍ) :
    (coxPhiFunction N).coeff n (δ • z) =
      (coxPhiFunction N).coeff n z := by
  rw [coxPhiFunction_coeff_apply, coxPhiFunction_coeff_apply]
  exact coxPhiAtJ_coeff_sl2_smul N δ z n

/-- Each coefficient of the Cox product is level-one invariant, the modularity
input for Cox Lemma 11.10(ii). -/
theorem coxPhiFunction_coeff_slashInvariant
    (N : ℕ+) (n : ℕ) (γ : SL(2, ℤ)) :
    ((coxPhiFunction N).coeff n) ∣[(0 : ℤ)] γ =
      (coxPhiFunction N).coeff n := by
  ext z
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one]
  exact coxPhiFunction_coeff_sl2_smul N γ n z

/-- The function-valued Cox product is monic. -/
theorem coxPhiFunction_monic (N : ℕ+) : (coxPhiFunction N).Monic := by
  classical
  simpa [coxPhiFunction] using
    Polynomial.monic_prod_of_monic (Finset.univ : Finset (Gamma0RightCosets N))
      (fun c => Polynomial.X - Polynomial.C (fun z => gamma0RightCosetEval N c z))
      (fun c _ => Polynomial.monic_X_sub_C (fun z => gamma0RightCosetEval N c z))

end FunctionValuedProduct

end modularEquation
