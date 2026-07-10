import XYin.PhD.Test.JLevelN.Existence

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups
  PowerSeries SlashInvariantFormClass Real Function IntegralPowerSeries
open scoped Manifold

/-!
# The explicit level-`2` modular equation

This file contains the explicit `N = 2` modular equation for the classical
`j`-function.  It builds the three right-coset roots, proves the coefficient
identities needed to identify the displayed polynomial with the Cox product,
and records the `m = 2` instances of Cox Theorem 11.18: integer coefficients,
irreducibility, symmetry, the diagonal leading coefficient, and Kronecker's
congruence modulo `2`.
-/

local notation "𝕢" => Periodic.qParam
local notation "ℍₒ" => upperHalfPlaneSet

noncomputable section

section modularEquation

/-! ## Explicit level-two Cox product

For `m = 2`, Cox equation (11.15) becomes a product over three representatives.
This section identifies those three roots without expanding the classical `Φ₂`.
-/

section LevelTwoExplicit

/-- The three standard right-coset representatives for `Γ₀(2)` in `SL₂(ℤ)`. -/
def gamma0TwoRightCosetReps : Fin 3 → SL(2, ℤ) :=
  ![1, ModularGroup.S, ModularGroup.S * ModularGroup.T]

/-- The quotient classes of the three standard `Γ₀(2)` right-coset representatives. -/
noncomputable def gamma0TwoRightCosetRepQuotient (i : Fin 3) :
    Gamma0RightCosets (2 : ℕ+) :=
  Quotient.mk _ (gamma0TwoRightCosetReps i)

/-- In `ZMod 2`, every nonzero element is `1`. -/
private lemma zmodTwo_eq_one_of_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exfalso
    exact hx rfl
  · rfl

/-- Every `Γ₀(2)` right coset has one of the three standard representatives. -/
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

/-- The three standard `Γ₀(2)` right-coset representatives are distinct. -/
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

/-- The three standard representatives enumerate the right cosets of `Γ₀(2)`,
the `m = 2` case of Cox Lemma 11.11. -/
noncomputable def gamma0TwoRightCosetsEquiv : Fin 3 ≃ Gamma0RightCosets (2 : ℕ+) :=
  Equiv.ofBijective gamma0TwoRightCosetRepQuotient
    ⟨gamma0TwoRightCosetReps_injective, gamma0TwoRightCosetReps_surjective⟩

/-- Reindex the level-`2` Cox product by the three explicit right cosets. -/
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

/-- The reindexed level-`2` Cox product still has `jN 2 z` as a root. -/
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

/-- The complex coordinate of `halfUpper z` is `z / 2`. -/
theorem coe_halfUpper (z : ℍ) :
    ((halfUpper z : ℍ) : ℂ) = (z : ℂ) / 2 := rfl

/-- The upper-half-plane point with complex coordinate `(z + 1) / 2`. -/
def halfTranslateUpper (z : ℍ) : ℍ :=
  ⟨((z : ℂ) + 1) / 2, by
    have hz : 0 < ((z : ℂ) + 1).im := by simpa using z.2
    simpa using div_pos hz (by norm_num : (0 : ℝ) < 2)⟩

/-- The complex coordinate of `halfTranslateUpper z` is `(z + 1) / 2`. -/
theorem coe_halfTranslateUpper (z : ℍ) :
    ((halfTranslateUpper z : ℍ) : ℂ) = ((z : ℂ) + 1) / 2 := rfl

/-- Doubling `halfUpper z` recovers `z`. -/
theorem two_nsmul_halfUpper (z : ℍ) :
    (2 : ℕ+) • halfUpper z = z := by
  ext
  rw [natPosSMul_apply, coe_halfUpper]
  norm_num
  field_simp

/-- Doubling `halfTranslateUpper z` gives the `T`-translate of `z`. -/
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

/-- The `S`-root for the level-`2` product is represented by `halfUpper`. -/
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

/-- The `S*T`-root for the level-`2` product is represented by `halfTranslateUpper`. -/
theorem two_nsmul_modular_ST_smul_halfTranslateUpper (z : ℍ) :
    (2 : ℕ+) • ((ModularGroup.S * ModularGroup.T) • z) =
      ModularGroup.S • halfTranslateUpper z := by
  ext
  rw [natPosSMul_apply, mul_smul, UpperHalfPlane.modular_S_smul,
    UpperHalfPlane.modular_S_smul]
  change (2 : ℂ) * (-((ModularGroup.T • z : ℍ) : ℂ))⁻¹ =
    (-((halfTranslateUpper z : ℍ) : ℂ))⁻¹
  rw [UpperHalfPlane.modular_T_smul, coe_halfTranslateUpper]
  simp only [coe_vadd, ofReal_one, neg_add_rev, inv_neg, inv_div]
  have hz0 : (z : ℂ) + 1 ≠ 0 := by
    intro hz
    have him : ((z : ℂ) + 1).im = 0 := by simp [hz]
    have him_pos : 0 < ((z : ℂ) + 1).im := by simpa using z.2
    exact ne_of_gt him_pos him
  rw [show -(z : ℂ) + -1 = -((z : ℂ) + 1) by ring]
  field_simp [hz0]

/-- The identity coset root is `jN 2`. -/
theorem gamma0RightCosetEval_two_one (z : ℍ) :
    gamma0RightCosetEval (2 : ℕ+) (gamma0TwoRightCosetsEquiv 0) z =
      jN (2 : ℕ+) z := by
  simp [gamma0TwoRightCosetsEquiv, gamma0TwoRightCosetRepQuotient, gamma0TwoRightCosetReps,
    gamma0RightCosetEval]

/-- The `S` coset root is `j(z / 2)`. -/
theorem gamma0RightCosetEval_two_S (z : ℍ) :
    gamma0RightCosetEval (2 : ℕ+) (gamma0TwoRightCosetsEquiv 1) z =
      j (halfUpper z) := by
  simp only [gamma0RightCosetEval, PNat.val_ofNat, gamma0TwoRightCosetsEquiv, Fin.isValue,
    Equiv.ofBijective_apply, gamma0TwoRightCosetRepQuotient, gamma0TwoRightCosetReps,
    Matrix.cons_val_one, Matrix.cons_val_zero, jN, ModularGroup.sl_moeb, Quotient.lift_mk]
  change j ((2 : ℕ+) • (ModularGroup.S • z)) = j (halfUpper z)
  rw [two_nsmul_modular_S_smul_halfUpper]
  exact j_invariant ModularGroup.S (halfUpper z)

/-- The `S*T` coset root is `j((z + 1) / 2)`. -/
theorem gamma0RightCosetEval_two_ST (z : ℍ) :
    gamma0RightCosetEval (2 : ℕ+) (gamma0TwoRightCosetsEquiv 2) z =
      j (halfTranslateUpper z) := by
  simp only [gamma0RightCosetEval, PNat.val_ofNat, gamma0TwoRightCosetsEquiv, Fin.isValue,
    Equiv.ofBijective_apply, gamma0TwoRightCosetRepQuotient, gamma0TwoRightCosetReps,
    jN, ModularGroup.sl_moeb, Quotient.lift_mk]
  have h :
      j ((2 : ℕ+) • ((ModularGroup.S * ModularGroup.T) • z)) =
        j (ModularGroup.S • halfTranslateUpper z) := by
    exact congrArg j (two_nsmul_modular_ST_smul_halfTranslateUpper z)
  simpa using h.trans (j_invariant ModularGroup.S (halfTranslateUpper z))

/-- The `m = 2` product from Cox equation (11.15), written with the three
explicit roots. -/
noncomputable def coxPhiTwoExplicit (z : ℍ) : Polynomial ℂ :=
  (Polynomial.X - Polynomial.C (jN (2 : ℕ+) z)) *
  (Polynomial.X - Polynomial.C (j (halfUpper z))) *
  (Polynomial.X - Polynomial.C (j (halfTranslateUpper z)))

/-- The right-coset Cox product agrees with the explicit `m = 2` product from
Cox equation (11.15). -/
theorem coxPhiAtJ_two_eq_explicit (z : ℍ) :
    coxPhiAtJ (2 : ℕ+) z = coxPhiTwoExplicit z := by
  rw [coxPhiAtJ_two_eq_fin3_product]
  rw [Fin.prod_univ_three]
  norm_num [coxPhiTwoExplicit, gamma0RightCosetEval_two_one, gamma0RightCosetEval_two_S,
    gamma0RightCosetEval_two_ST]

/-- The explicit `m = 2` Cox product has `jN 2 z` as a root, as in equation
(11.15). -/
theorem coxPhiTwoExplicit_eval_jN (z : ℍ) :
    Polynomial.eval (jN (2 : ℕ+) z) (coxPhiTwoExplicit z) = 0 := by
  rw [← coxPhiAtJ_two_eq_explicit z]
  exact coxPhiAtJ_eval_jN (2 : ℕ+) z

/-- Root formulation of `coxPhiTwoExplicit_eval_jN`. -/
theorem coxPhiTwoExplicit_isRoot_jN (z : ℍ) :
    (coxPhiTwoExplicit z).IsRoot (jN (2 : ℕ+) z) := by
  simpa [Polynomial.IsRoot] using coxPhiTwoExplicit_eval_jN z

end LevelTwoExplicit

/-! ## Level-two cusp changes

This section keeps the cusp-change lemmas used for the explicit level-`2`
coefficient identities.  The general finite q-order estimates live in
`XYin.PhD.Test.JLevelN.Existence`.
-/

section LevelTwoCuspChanges

/-- Level-one periodicity of `j` after extending to all complex inputs by `ofComplex`. -/
private theorem j_comp_ofComplex_periodic_one :
    Periodic (j ∘ UpperHalfPlane.ofComplex) (1 : ℝ) :=
  periodic_comp_of_slashInvariant_one j_slashInvariant

/-- At the width-`2` cusp, the half-root `j(τ / 2)` has the level-one `j`
cusp function. -/
private theorem cuspFunction_two_j_halfUpper_eventuallyEq :
    cuspFunction (2 : ℝ) (fun τ : ℍ => j (halfUpper τ))
      =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
        cuspFunction (1 : ℝ) j := by
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds (by simpa [Metric.ball, dist_eq_norm]
      using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hqmem
  have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hqmem
  have him2 : 0 < Complex.im (Periodic.invQParam (2 : ℝ) q) :=
    Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hqnorm hq0
  let τ : ℍ := ⟨Periodic.invQParam (2 : ℝ) q, him2⟩
  have hleft :
      cuspFunction (2 : ℝ) (fun τ : ℍ => j (halfUpper τ)) q =
        j (halfUpper τ) := by
    change Periodic.cuspFunction (2 : ℝ) _ q = _
    rw [Periodic.cuspFunction_eq_of_nonzero (2 : ℝ) _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him2]
  have hqparam : 𝕢 (1 : ℝ) ((halfUpper τ : ℍ) : ℂ) = q := by
    rw [coe_halfUpper]
    change 𝕢 (1 : ℝ) (Periodic.invQParam (2 : ℝ) q / 2) = q
    have h := Periodic.qParam_right_inv (h := (2 : ℝ)) (by norm_num) hq0
    rw [Periodic.qParam]
    have harg :
        2 * ↑Real.pi * Complex.I * (Periodic.invQParam (2 : ℝ) q / 2) /
            ↑(1 : ℝ) =
          2 * ↑Real.pi * Complex.I * Periodic.invQParam (2 : ℝ) q / ↑(2 : ℝ) := by
      norm_num
      ring
    rw [harg]
    simpa [Periodic.qParam] using h
  have hcusp :=
    Periodic.eq_cuspFunction (h := (1 : ℝ)) (f := j ∘ UpperHalfPlane.ofComplex)
      (by norm_num) j_comp_ofComplex_periodic_one ((halfUpper τ : ℍ) : ℂ)
  rw [hleft]
  change j (halfUpper τ) = Periodic.cuspFunction (1 : ℝ)
    (j ∘ UpperHalfPlane.ofComplex) q
  rw [← hqparam]
  simpa [UpperHalfPlane.ofComplex_apply_of_im_pos (halfUpper τ).2] using hcusp.symm

/-- At the width-`2` cusp, the translated half-root corresponds to evaluating
the level-one cusp function at `-q`. -/
private theorem cuspFunction_two_j_halfTranslateUpper_eventuallyEq :
    cuspFunction (2 : ℝ) (fun τ : ℍ => j (halfTranslateUpper τ))
      =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
        fun q : ℂ => cuspFunction (1 : ℝ) j (-q) := by
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds (by simpa [Metric.ball, dist_eq_norm]
      using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hqmem
  have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hqmem
  have him2 : 0 < Complex.im (Periodic.invQParam (2 : ℝ) q) :=
    Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hqnorm hq0
  let τ : ℍ := ⟨Periodic.invQParam (2 : ℝ) q, him2⟩
  have hleft :
      cuspFunction (2 : ℝ) (fun τ : ℍ => j (halfTranslateUpper τ)) q =
        j (halfTranslateUpper τ) := by
    change Periodic.cuspFunction (2 : ℝ) _ q = _
    rw [Periodic.cuspFunction_eq_of_nonzero (2 : ℝ) _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him2]
  have hqparam : 𝕢 (1 : ℝ) ((halfTranslateUpper τ : ℍ) : ℂ) = -q := by
    rw [coe_halfTranslateUpper]
    change 𝕢 (1 : ℝ) ((Periodic.invQParam (2 : ℝ) q + 1) / 2) = -q
    have h := Periodic.qParam_right_inv (h := (2 : ℝ)) (by norm_num) hq0
    rw [Periodic.qParam]
    have harg :
        2 * ↑Real.pi * Complex.I * ((Periodic.invQParam (2 : ℝ) q + 1) / 2) /
            ↑(1 : ℝ) =
          2 * ↑Real.pi * Complex.I * Periodic.invQParam (2 : ℝ) q / ↑(2 : ℝ) +
            ↑Real.pi * Complex.I := by
      norm_num
      ring
    rw [harg, Complex.exp_add_pi_mul_I]
    simpa [Periodic.qParam] using congrArg Neg.neg h
  have hcusp :=
    Periodic.eq_cuspFunction (h := (1 : ℝ)) (f := j ∘ UpperHalfPlane.ofComplex)
      (by norm_num) j_comp_ofComplex_periodic_one ((halfTranslateUpper τ : ℍ) : ℂ)
  rw [hleft]
  change j (halfTranslateUpper τ) = Periodic.cuspFunction (1 : ℝ)
    (j ∘ UpperHalfPlane.ofComplex) (-q)
  rw [← hqparam]
  simpa [UpperHalfPlane.ofComplex_apply_of_im_pos (halfTranslateUpper τ).2] using hcusp.symm

/-- At the width-`2` cusp, `j(2τ)` corresponds to the level-one cusp function
evaluated at `q^4`. -/
private theorem cuspFunction_two_jN_two_eventuallyEq :
    cuspFunction (2 : ℝ) (jN (2 : ℕ+))
      =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
        fun q : ℂ => cuspFunction (1 : ℝ) j (q ^ 4) := by
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds (by simpa [Metric.ball, dist_eq_norm]
      using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hqmem
  have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hqmem
  have him2 : 0 < Complex.im (Periodic.invQParam (2 : ℝ) q) :=
    Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hqnorm hq0
  let τ : ℍ := ⟨Periodic.invQParam (2 : ℝ) q, him2⟩
  have hleft : cuspFunction (2 : ℝ) (jN (2 : ℕ+)) q = jN (2 : ℕ+) τ := by
    change Periodic.cuspFunction (2 : ℝ) _ q = _
    rw [Periodic.cuspFunction_eq_of_nonzero (2 : ℝ) _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him2]
  have hqparam : 𝕢 (1 : ℝ) (((2 : ℕ+) • τ : ℍ) : ℂ) = q ^ 4 := by
    rw [natPosSMul_apply]
    change 𝕢 (1 : ℝ) ((2 : ℂ) * Periodic.invQParam (2 : ℝ) q) = q ^ 4
    have h := Periodic.qParam_right_inv (h := (2 : ℝ)) (by norm_num) hq0
    rw [Periodic.qParam]
    have harg :
        2 * ↑Real.pi * Complex.I * ((2 : ℂ) * Periodic.invQParam (2 : ℝ) q) /
            ↑(1 : ℝ) =
          (4 : ℕ) *
            (2 * ↑Real.pi * Complex.I * Periodic.invQParam (2 : ℝ) q / ↑(2 : ℝ)) := by
      norm_num
      ring
    rw [harg, Complex.exp_nat_mul]
    simpa [Periodic.qParam] using congrArg (fun x : ℂ => x ^ 4) h
  have hcusp :=
    Periodic.eq_cuspFunction (h := (1 : ℝ)) (f := j ∘ UpperHalfPlane.ofComplex)
      (by norm_num) j_comp_ofComplex_periodic_one (((2 : ℕ+) • τ : ℍ) : ℂ)
  rw [hleft]
  change j ((2 : ℕ+) • τ) = Periodic.cuspFunction (1 : ℝ)
    (j ∘ UpperHalfPlane.ofComplex) (q ^ 4)
  rw [← hqparam]
  simpa [UpperHalfPlane.ofComplex_apply_of_im_pos ((2 : ℕ+) • τ).2] using hcusp.symm

end LevelTwoCuspChanges

/-! ## Level-two equation

This section contains the explicit level-`2` modular equation, its coefficient
identities, and the `m = 2` instances of Cox Theorem 11.18: integer
coefficients, irreducibility in the Cox/root variable, symmetry, the diagonal
leading term, and Kronecker's congruence modulo `2`.
-/

section LevelTwoEquation

/-! ### Function-valued level-two product

This section rewrites the general Cox product at level `2` as the explicit
three-root product and records its coefficients.
-/

section LevelTwoFunctionValuedProduct

/-- The function-valued `N = 2` Cox product written with the three explicit roots. -/
noncomputable def coxPhiTwoFunctionExplicit : Polynomial (ℍ → ℂ) :=
  (Polynomial.X - Polynomial.C (jN (2 : ℕ+))) *
  (Polynomial.X - Polynomial.C (fun z : ℍ => j (halfUpper z))) *
  (Polynomial.X - Polynomial.C (fun z : ℍ => j (halfTranslateUpper z)))

/-- Evaluating the function-valued explicit product gives the pointwise product. -/
private theorem coxPhiTwoFunctionExplicit_map_eval (z : ℍ) :
    coxPhiTwoFunctionExplicit.map (evalAtUpper z) = coxPhiTwoExplicit z := by
  simp [coxPhiTwoFunctionExplicit, coxPhiTwoExplicit, evalAtUpper, Polynomial.map_mul]

/-- The function-valued Cox product at level `2` is the three-root product. -/
theorem coxPhiFunction_two_eq_explicit :
    coxPhiFunction (2 : ℕ+) = coxPhiTwoFunctionExplicit := by
  apply Polynomial.ext
  intro n
  ext z
  rw [coxPhiFunction_coeff_apply, coxPhiAtJ_two_eq_explicit]
  rw [← coxPhiTwoFunctionExplicit_map_eval z, Polynomial.coeff_map]
  rfl

/-- The leading coefficient of the level-`2` Cox product. -/
theorem coxPhiFunction_two_coeff_three :
    (coxPhiFunction (2 : ℕ+)).coeff 3 = 1 := by
  rw [coxPhiFunction_two_eq_explicit]
  ext z
  change evalAtUpper z (coxPhiTwoFunctionExplicit.coeff 3) = 1
  rw [← Polynomial.coeff_map, coxPhiTwoFunctionExplicit_map_eval]
  rw [coxPhiTwoExplicit, Cubic.prod_X_sub_C_eq]
  simp only [Cubic.toPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  simp

/-- The `Y^2` coefficient of the level-`2` Cox product as a symmetric sum. -/
theorem coxPhiFunction_two_coeff_two :
    (coxPhiFunction (2 : ℕ+)).coeff 2 =
      -((jN (2 : ℕ+)) +
        (fun z : ℍ => j (halfUpper z)) +
        (fun z : ℍ => j (halfTranslateUpper z))) := by
  rw [coxPhiFunction_two_eq_explicit]
  ext z
  change evalAtUpper z (coxPhiTwoFunctionExplicit.coeff 2) =
    -(jN (2 : ℕ+) z + j (halfUpper z) + j (halfTranslateUpper z))
  rw [← Polynomial.coeff_map, coxPhiTwoFunctionExplicit_map_eval]
  rw [coxPhiTwoExplicit, Cubic.prod_X_sub_C_eq]
  simp only [Cubic.toPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  simp

/-- The `Y` coefficient of the level-`2` Cox product as a symmetric sum. -/
theorem coxPhiFunction_two_coeff_one :
    (coxPhiFunction (2 : ℕ+)).coeff 1 =
      (jN (2 : ℕ+)) * (fun z : ℍ => j (halfUpper z)) +
      (jN (2 : ℕ+)) * (fun z : ℍ => j (halfTranslateUpper z)) +
      (fun z : ℍ => j (halfUpper z)) *
        (fun z : ℍ => j (halfTranslateUpper z)) := by
  rw [coxPhiFunction_two_eq_explicit]
  ext z
  change evalAtUpper z (coxPhiTwoFunctionExplicit.coeff 1) =
    jN (2 : ℕ+) z * j (halfUpper z) +
      jN (2 : ℕ+) z * j (halfTranslateUpper z) +
        j (halfUpper z) * j (halfTranslateUpper z)
  rw [← Polynomial.coeff_map, coxPhiTwoFunctionExplicit_map_eval]
  rw [coxPhiTwoExplicit, Cubic.prod_X_sub_C_eq]
  simp only [Cubic.toPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  simp

/-- The constant coefficient of the level-`2` Cox product as a symmetric product. -/
theorem coxPhiFunction_two_coeff_zero :
    (coxPhiFunction (2 : ℕ+)).coeff 0 =
      -((jN (2 : ℕ+)) *
        (fun z : ℍ => j (halfUpper z)) *
        (fun z : ℍ => j (halfTranslateUpper z))) := by
  rw [coxPhiFunction_two_eq_explicit]
  ext z
  change evalAtUpper z (coxPhiTwoFunctionExplicit.coeff 0) =
    -(jN (2 : ℕ+) z * j (halfUpper z) * j (halfTranslateUpper z))
  rw [← Polynomial.coeff_map, coxPhiTwoFunctionExplicit_map_eval]
  rw [coxPhiTwoExplicit, Cubic.prod_X_sub_C_eq]
  simp only [Cubic.toPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  simp

end LevelTwoFunctionValuedProduct

/-! ### Explicit polynomial and arithmetic facts

This section defines the displayed integral and complex level-`2` polynomial and
records the `m = 2` arithmetic facts from Cox Theorem 11.18.
-/

section LevelTwoExplicitPolynomial

/-- The `Y^2` coefficient polynomial in the `N = 2` example. -/
noncomputable def modularEquationTwoCoeffY2 : Polynomial ℂ :=
  -Polynomial.X ^ 2 + Polynomial.C (1488 : ℂ) * Polynomial.X -
    Polynomial.C (162000 : ℂ)

/-- The `Y` coefficient polynomial in the `N = 2` example. -/
noncomputable def modularEquationTwoCoeffY1 : Polynomial ℂ :=
  Polynomial.C (1488 : ℂ) * Polynomial.X ^ 2 +
    Polynomial.C (40773375 : ℂ) * Polynomial.X +
      Polynomial.C (8748000000 : ℂ)

/-- The constant coefficient polynomial in the `N = 2` example. -/
noncomputable def modularEquationTwoCoeffY0 : Polynomial ℂ :=
  Polynomial.X ^ 3 - Polynomial.C (162000 : ℂ) * Polynomial.X ^ 2 +
    Polynomial.C (8748000000 : ℂ) * Polynomial.X -
      Polynomial.C (157464000000000 : ℂ)

/-- The integral `Y^2` coefficient polynomial in the `N = 2` example. -/
def modularEquationTwoIntCoeffY2 : Polynomial ℤ :=
  -Polynomial.X ^ 2 + Polynomial.C (1488 : ℤ) * Polynomial.X -
    Polynomial.C (162000 : ℤ)

/-- The integral `Y` coefficient polynomial in the `N = 2` example. -/
def modularEquationTwoIntCoeffY1 : Polynomial ℤ :=
  Polynomial.C (1488 : ℤ) * Polynomial.X ^ 2 +
    Polynomial.C (40773375 : ℤ) * Polynomial.X +
      Polynomial.C (8748000000 : ℤ)

/-- The integral constant coefficient polynomial in the `N = 2` example. -/
def modularEquationTwoIntCoeffY0 : Polynomial ℤ :=
  Polynomial.X ^ 3 - Polynomial.C (162000 : ℤ) * Polynomial.X ^ 2 +
    Polynomial.C (8748000000 : ℤ) * Polynomial.X -
      Polynomial.C (157464000000000 : ℤ)

/-- The classical explicit modular polynomial `Φ₂` from the `N = 2` example.

The inner polynomial variable is `X` and the outer polynomial variable is `Y`.
The coefficient comparison with the Cox product is proved below in
`modularEquationTwo_map_eq_coxPhiFunction_two`. -/
noncomputable def modularEquationTwo : Polynomial (Polynomial ℂ) :=
  let Y : Polynomial (Polynomial ℂ) := Polynomial.X
  Y ^ 3 + Polynomial.C modularEquationTwoCoeffY2 * Y ^ 2 +
    Polynomial.C modularEquationTwoCoeffY1 * Y +
      Polynomial.C modularEquationTwoCoeffY0

/-- Cox Theorem 11.18(i) for `m = 2`: the explicit `Φ₂` for the `N = 2`
example as a polynomial with integer coefficients.

The inner polynomial variable is `X` and the outer polynomial variable is `Y`,
matching `modularEquationTwo`. -/
def modularEquationTwoInt : Polynomial (Polynomial ℤ) :=
  let Y : Polynomial (Polynomial ℤ) := Polynomial.X
  Y ^ 3 + Polynomial.C modularEquationTwoIntCoeffY2 * Y ^ 2 +
    Polynomial.C modularEquationTwoIntCoeffY1 * Y +
      Polynomial.C modularEquationTwoIntCoeffY0

/-- A natural numeral in a polynomial ring is the corresponding constant polynomial. -/
private theorem polynomial_C_ofNat {R : Type*} [Semiring R] (n : ℕ) [n.AtLeastTwo] :
    Polynomial.C (OfNat.ofNat n : R) = (OfNat.ofNat n : Polynomial R) :=
  Polynomial.C_eq_natCast n

/-- Over `ZMod 2`, a polynomial numeral is the corresponding constant polynomial. -/
private theorem polynomial_ofNat_zmod_two (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Polynomial (ZMod 2)) = Polynomial.C (OfNat.ofNat n : ZMod 2) :=
  (Polynomial.C_eq_natCast n).symm

/-- The integral `Y^2` coefficient maps to the complex coefficient. -/
theorem modularEquationTwoIntCoeffY2_map_complex :
    modularEquationTwoIntCoeffY2.map (Int.castRingHom ℂ) = modularEquationTwoCoeffY2 := by
  simp only [modularEquationTwoIntCoeffY2, eq_intCast, Int.cast_ofNat, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_neg, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_mul, Polynomial.map_ofNat, modularEquationTwoCoeffY2]
  rw [polynomial_C_ofNat 1488, polynomial_C_ofNat 162000]

/-- The integral `Y` coefficient maps to the complex coefficient. -/
theorem modularEquationTwoIntCoeffY1_map_complex :
    modularEquationTwoIntCoeffY1.map (Int.castRingHom ℂ) = modularEquationTwoCoeffY1 := by
  simp only [modularEquationTwoIntCoeffY1, eq_intCast, Int.cast_ofNat, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_pow, Polynomial.map_X,
    modularEquationTwoCoeffY1]
  rw [polynomial_C_ofNat 1488, polynomial_C_ofNat 40773375,
    polynomial_C_ofNat 8748000000]

/-- The integral constant coefficient maps to the complex coefficient. -/
theorem modularEquationTwoIntCoeffY0_map_complex :
    modularEquationTwoIntCoeffY0.map (Int.castRingHom ℂ) = modularEquationTwoCoeffY0 := by
  simp only [modularEquationTwoIntCoeffY0, eq_intCast, Int.cast_ofNat, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul,
    Polynomial.map_ofNat, modularEquationTwoCoeffY0]
  rw [polynomial_C_ofNat 162000, polynomial_C_ofNat 8748000000,
    polynomial_C_ofNat 157464000000000]

/-- Mapping the integral `N = 2` example polynomial to `ℂ` recovers the
existing complex-coefficient polynomial. -/
theorem modularEquationTwoInt_map_complex :
    modularEquationTwoInt.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) =
      modularEquationTwo := by
  simp [modularEquationTwoInt, modularEquationTwo, modularEquationTwoIntCoeffY2_map_complex,
    modularEquationTwoIntCoeffY1_map_complex, modularEquationTwoIntCoeffY0_map_complex]

/-- The explicit integral `Φ₂` is monic in the Cox/root variable. -/
theorem modularEquationTwoInt_monic : modularEquationTwoInt.Monic := by
  rw [Polynomial.Monic]
  let p : Polynomial (Polynomial ℤ) := modularEquationTwoInt
  change p.leadingCoeff = 1
  have hp : p.natDegree = 3 := by
    dsimp [p, modularEquationTwoInt, modularEquationTwoIntCoeffY2,
      modularEquationTwoIntCoeffY1, modularEquationTwoIntCoeffY0]
    compute_degree!
  change p.coeff p.natDegree = 1
  rw [hp]
  dsimp [p, modularEquationTwoInt, modularEquationTwoIntCoeffY2,
    modularEquationTwoIntCoeffY1, modularEquationTwoIntCoeffY0]
  compute_degree!

private noncomputable def modularEquationTwoIntEvalOneModThree : Polynomial ℤ →+* ZMod 3 :=
  (Polynomial.evalRingHom (1 : ZMod 3)).comp
    (Polynomial.mapRingHom (Int.castRingHom (ZMod 3)))

/-- Specialising the inner variable to `1` modulo `3` gives a cubic over `𝔽₃`. -/
private theorem modularEquationTwoInt_map_evalOneModThree :
    modularEquationTwoInt.map modularEquationTwoIntEvalOneModThree =
      Polynomial.X ^ 3 + Polynomial.C (2 : ZMod 3) * Polynomial.X ^ 2 + 1 := by
  simp only [modularEquationTwoIntEvalOneModThree, modularEquationTwoInt,
    modularEquationTwoIntCoeffY2, eq_intCast, Int.cast_ofNat, map_sub, map_add, map_neg, map_pow,
    map_mul, modularEquationTwoIntCoeffY1, modularEquationTwoIntCoeffY0, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_neg, Polynomial.map_C, RingHom.coe_comp, Polynomial.coe_evalRingHom,
    Polynomial.coe_mapRingHom, comp_apply, Polynomial.eval_X, map_one, one_pow,
    Polynomial.map_ofNat, Polynomial.eval_ofNat, mul_one]
  have h1488 : (1488 : ZMod 3) = 0 := by decide
  have h162000 : (162000 : ZMod 3) = 0 := by decide
  have h40773375 : (40773375 : ZMod 3) = 0 := by decide
  have h8748000000 : (8748000000 : ZMod 3) = 0 := by decide
  have h157464000000000 : (157464000000000 : ZMod 3) = 0 := by decide
  rw [h1488, h162000, h40773375, h8748000000, h157464000000000]
  rw [show (2 : ZMod 3) = -1 by decide]
  simp

/-- The cubic over `𝔽₃` used for irreducibility has no roots. -/
private theorem modularEquationTwoInt_mod_three_cubic_irreducible :
    Irreducible
      (Polynomial.X ^ 3 + Polynomial.C (2 : ZMod 3) * Polynomial.X ^ 2 + 1 :
        Polynomial (ZMod 3)) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [show (Polynomial.X ^ 3 + Polynomial.C (2 : ZMod 3) * Polynomial.X ^ 2 + 1 :
        Polynomial (ZMod 3)).natDegree = 3 by compute_degree!]
    decide
  · intro x hx
    fin_cases x
    · simp only [Polynomial.IsRoot, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_one] at hx
      exact (by decide : (0 ^ 3 + (2 : ZMod 3) * 0 ^ 2 + 1 : ZMod 3) ≠ 0) hx
    · simp only [Polynomial.IsRoot, Nat.reduceAdd, Fin.mk_one, Fin.isValue, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_one] at hx
      exact (by decide : (1 ^ 3 + (2 : ZMod 3) * 1 ^ 2 + 1 : ZMod 3) ≠ 0) hx
    · simp only [Polynomial.IsRoot, Nat.reduceAdd, Fin.reduceFinMk, Polynomial.eval_add,
      Fin.isValue, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_one] at hx
      exact (by decide : (2 ^ 3 + (2 : ZMod 3) * 2 ^ 2 + 1 : ZMod 3) ≠ 0) hx

/-- Cox Theorem 11.18(ii) for `m = 2`: the explicit integral `Φ₂`
is irreducible in the Cox/root variable. -/
theorem modularEquationTwoInt_irreducible :
    Irreducible modularEquationTwoInt := by
  apply Polynomial.Monic.irreducible_of_irreducible_map
    modularEquationTwoIntEvalOneModThree modularEquationTwoInt modularEquationTwoInt_monic
  rw [modularEquationTwoInt_map_evalOneModThree]
  exact modularEquationTwoInt_mod_three_cubic_irreducible

/-- Cox Theorem 11.18(iii) for `m = 2`: the explicit integral `Φ₂` is symmetric. -/
theorem modularEquationTwoInt_swap :
    Polynomial.Bivariate.swap modularEquationTwoInt = modularEquationTwoInt := by
  simp only [modularEquationTwoInt, modularEquationTwoIntCoeffY2, eq_intCast, Int.cast_ofNat,
    map_sub, map_add, map_neg, map_pow, map_mul, modularEquationTwoIntCoeffY1,
    modularEquationTwoIntCoeffY0, Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_C,
    Polynomial.map_X, Polynomial.map_ofNat]
  rw [polynomial_C_ofNat 1488, polynomial_C_ofNat 162000, polynomial_C_ofNat 40773375,
    polynomial_C_ofNat 8748000000, polynomial_C_ofNat 157464000000000]
  ring_nf

/-- Cox Theorem 11.18(v) for `p = 2`: Kronecker's congruence for the
explicit `Φ₂`. -/
theorem modularEquationTwoInt_kronecker_mod_two :
    modularEquationTwoInt.map (Polynomial.mapRingHom (Int.castRingHom (ZMod 2))) =
      (Polynomial.C (Polynomial.X ^ 2) - Polynomial.X) *
        (Polynomial.C Polynomial.X - Polynomial.X ^ 2) := by
  simp only [modularEquationTwoInt, modularEquationTwoIntCoeffY2, eq_intCast, Int.cast_ofNat,
    map_sub, map_add, map_neg, map_pow, map_mul, modularEquationTwoIntCoeffY1,
    modularEquationTwoIntCoeffY0, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_neg, Polynomial.map_C,
    Polynomial.coe_mapRingHom, Polynomial.map_ofNat]
  have h1488 : (1488 : Polynomial (ZMod 2)) = 0 := by
    rw [polynomial_ofNat_zmod_two 1488]
    rw [show (OfNat.ofNat 1488 : ZMod 2) = 0 by decide]
    simp
  have h162000 : (162000 : Polynomial (ZMod 2)) = 0 := by
    rw [polynomial_ofNat_zmod_two 162000]
    rw [show (OfNat.ofNat 162000 : ZMod 2) = 0 by decide]
    simp
  have h40773375 : (40773375 : Polynomial (ZMod 2)) = 1 := by
    rw [polynomial_ofNat_zmod_two 40773375]
    rw [show (OfNat.ofNat 40773375 : ZMod 2) = 1 by decide]
    simp
  have h8748000000 : (8748000000 : Polynomial (ZMod 2)) = 0 := by
    rw [polynomial_ofNat_zmod_two 8748000000]
    rw [show (OfNat.ofNat 8748000000 : ZMod 2) = 0 by decide]
    simp
  have h157464000000000 : (157464000000000 : Polynomial (ZMod 2)) = 0 := by
    rw [polynomial_ofNat_zmod_two 157464000000000]
    rw [show (OfNat.ofNat 157464000000000 : ZMod 2) = 0 by decide]
    simp
  rw [h1488, h162000, h40773375, h8748000000, h157464000000000]
  simp [CharTwo.neg_eq, CharTwo.sub_eq_add]
  ring_nf

/-- The diagonal specialisation `Φ₂(X,X)` over `ℤ`. -/
def modularEquationTwoIntDiagonal : Polynomial ℤ :=
  modularEquationTwoInt.eval Polynomial.X

/-- Explicit diagonal form of the `N = 2` example. -/
theorem modularEquationTwoIntDiagonal_eq :
    modularEquationTwoIntDiagonal =
      -Polynomial.X ^ 4 + Polynomial.C (2978 : ℤ) * Polynomial.X ^ 3 +
        Polynomial.C (40449375 : ℤ) * Polynomial.X ^ 2 +
        Polynomial.C (17496000000 : ℤ) * Polynomial.X -
          Polynomial.C (157464000000000 : ℤ) := by
  simp [modularEquationTwoIntDiagonal, modularEquationTwoInt, modularEquationTwoIntCoeffY2,
    modularEquationTwoIntCoeffY1, modularEquationTwoIntCoeffY0]
  ring_nf

/-- Cox Theorem 11.18(iv) for `m = 2`: diagonal degree. -/
theorem modularEquationTwoIntDiagonal_natDegree :
    modularEquationTwoIntDiagonal.natDegree = 4 := by
  rw [modularEquationTwoIntDiagonal_eq]
  compute_degree!

/-- Cox Theorem 11.18(iv) for `m = 2`: diagonal leading coefficient. -/
theorem modularEquationTwoIntDiagonal_leadingCoeff :
    modularEquationTwoIntDiagonal.leadingCoeff = -1 := by
  rw [modularEquationTwoIntDiagonal_eq]
  let p : Polynomial ℤ :=
    -Polynomial.X ^ 4 + Polynomial.C (2978 : ℤ) * Polynomial.X ^ 3 +
      Polynomial.C (40449375 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (17496000000 : ℤ) * Polynomial.X -
        Polynomial.C (157464000000000 : ℤ)
  change p.leadingCoeff = -1
  have hp : p.natDegree = 4 := by
    dsimp [p]
    compute_degree!
  change p.coeff p.natDegree = -1
  rw [hp]
  dsimp [p]
  compute_degree!

/-- Cox Theorem 11.18(iv) for `m = 2`: the diagonal degree is greater than `1`. -/
theorem modularEquationTwoIntDiagonal_one_lt_natDegree :
    1 < modularEquationTwoIntDiagonal.natDegree := by
  rw [modularEquationTwoIntDiagonal_natDegree]
  norm_num

/-- The complex-coefficient `Φ₂` is symmetric. -/
theorem modularEquationTwo_swap :
    Polynomial.Bivariate.swap modularEquationTwo = modularEquationTwo := by
  simp only [modularEquationTwo, modularEquationTwoCoeffY2, map_sub, map_add, map_neg, map_pow,
    map_mul, modularEquationTwoCoeffY1, modularEquationTwoCoeffY0, Polynomial.Bivariate.swap_Y,
    Polynomial.Bivariate.swap_C, Polynomial.map_X, Polynomial.map_C]
  rw [polynomial_C_ofNat 1488, polynomial_C_ofNat 162000, polynomial_C_ofNat 40773375,
    polynomial_C_ofNat 8748000000, polynomial_C_ofNat 157464000000000]
  ring_nf

/-- Scalar evaluation of the explicit modular polynomial `Φ₂`. -/
theorem modularEquationTwo_evalEval (x y : ℂ) :
    modularEquationTwo.evalEval x y =
      x ^ 3 + y ^ 3 - x ^ 2 * y ^ 2
        + 1488 * x * y * (x + y)
        - 162000 * (x ^ 2 + y ^ 2)
        + 40773375 * x * y
        + 8748000000 * (x + y)
        - 157464000000000 := by
  simp [modularEquationTwo, modularEquationTwoCoeffY2, modularEquationTwoCoeffY1,
    modularEquationTwoCoeffY0, Polynomial.evalEval]
  ring

/-- The `Y^2` coefficient of the explicit `Φ₂`. -/
theorem modularEquationTwo_coeff_two :
    modularEquationTwo.coeff 2 = modularEquationTwoCoeffY2 := by
  simp [modularEquationTwo]

/-- The `Y` coefficient of the explicit `Φ₂`. -/
theorem modularEquationTwo_coeff_one :
    modularEquationTwo.coeff 1 = modularEquationTwoCoeffY1 := by
  simp [modularEquationTwo]

/-- The constant coefficient of the explicit `Φ₂`. -/
theorem modularEquationTwo_coeff_zero :
    modularEquationTwo.coeff 0 = modularEquationTwoCoeffY0 := by
  simp [modularEquationTwo]

end LevelTwoExplicitPolynomial

/-! ### Coefficient identities

This section proves that the three explicit symmetric coefficient functions agree
with the corresponding coefficient polynomials in `j`.
-/

section LevelTwoCoefficientIdentities

/-- At the width-`2` cusp, `P(j)` becomes `P` evaluated at the level-one
cusp function with parameter `q^2`. -/
private theorem cuspFunction_two_polynomialInJ_eventuallyEq (P : Polynomial ℂ) :
    cuspFunction (2 : ℝ) (polynomialInJ P)
      =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
        fun q : ℂ => P.eval (cuspFunction (1 : ℝ) j (q ^ 2)) := by
  have hnorm : {q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
    nhdsWithin_le_nhds (by simpa [Metric.ball, dist_eq_norm]
      using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  filter_upwards [hnorm, self_mem_nhdsWithin] with q hqnorm hqmem
  have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hqmem
  have him2 : 0 < Complex.im (Periodic.invQParam (2 : ℝ) q) :=
    Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hqnorm hq0
  let τ : ℍ := ⟨Periodic.invQParam (2 : ℝ) q, him2⟩
  have hleft : cuspFunction (2 : ℝ) (polynomialInJ P) q = polynomialInJ P τ := by
    change Periodic.cuspFunction (2 : ℝ) _ q = _
    rw [Periodic.cuspFunction_eq_of_nonzero (2 : ℝ) _ hq0]
    simp [τ, UpperHalfPlane.ofComplex_apply_of_im_pos him2]
  have hqparam : 𝕢 (1 : ℝ) (τ : ℂ) = q ^ 2 := by
    change 𝕢 (1 : ℝ) (Periodic.invQParam (2 : ℝ) q) = q ^ 2
    have h := Periodic.qParam_right_inv (h := (2 : ℝ)) (by norm_num) hq0
    rw [Periodic.qParam]
    have harg :
        2 * ↑Real.pi * Complex.I * Periodic.invQParam (2 : ℝ) q / ↑(1 : ℝ) =
          (2 : ℕ) *
            (2 * ↑Real.pi * Complex.I * Periodic.invQParam (2 : ℝ) q / ↑(2 : ℝ)) := by
      norm_num
      ring
    rw [harg, Complex.exp_nat_mul]
    simpa [Periodic.qParam] using congrArg (fun x : ℂ => x ^ 2) h
  have hcusp :=
    Periodic.eq_cuspFunction (h := (1 : ℝ)) (f := j ∘ UpperHalfPlane.ofComplex)
      (by norm_num) j_comp_ofComplex_periodic_one (τ : ℂ)
  rw [hleft]
  change P.eval (j τ) = P.eval
    (Periodic.cuspFunction (1 : ℝ) (j ∘ UpperHalfPlane.ofComplex) (q ^ 2))
  rw [← hqparam]
  exact congrArg P.eval
    (by simpa [UpperHalfPlane.ofComplex_apply_of_im_pos τ.2] using hcusp.symm)

/-- Away from the cusp point, `cuspFunction` commutes with subtraction pointwise. -/
private theorem cuspFunction_sub_apply_of_ne_zero
    (h : ℝ) (f g : ℍ → ℂ) {q : ℂ} (hq : q ≠ 0) :
    cuspFunction h (f - g) q = cuspFunction h f q - cuspFunction h g q := by
  change Periodic.cuspFunction h _ q =
    Periodic.cuspFunction h _ q - Periodic.cuspFunction h _ q
  rw [Periodic.cuspFunction_eq_of_nonzero h _ hq,
    Periodic.cuspFunction_eq_of_nonzero h _ hq,
    Periodic.cuspFunction_eq_of_nonzero h _ hq]
  simp

/-- Away from the cusp point, `cuspFunction` commutes with negation pointwise. -/
private theorem cuspFunction_neg_apply_of_ne_zero (h : ℝ) (f : ℍ → ℂ) {q : ℂ}
    (hq : q ≠ 0) :
    cuspFunction h (-f) q = -cuspFunction h f q := by
  change Periodic.cuspFunction h _ q = -Periodic.cuspFunction h _ q
  rw [Periodic.cuspFunction_eq_of_nonzero h _ hq,
    Periodic.cuspFunction_eq_of_nonzero h _ hq]
  simp

/-- Away from the cusp point, `cuspFunction` commutes with addition pointwise. -/
private theorem cuspFunction_add_apply_of_ne_zero
    (h : ℝ) (f g : ℍ → ℂ) {q : ℂ} (hq : q ≠ 0) :
    cuspFunction h (f + g) q = cuspFunction h f q + cuspFunction h g q := by
  change Periodic.cuspFunction h _ q =
    Periodic.cuspFunction h _ q + Periodic.cuspFunction h _ q
  rw [Periodic.cuspFunction_eq_of_nonzero h _ hq,
    Periodic.cuspFunction_eq_of_nonzero h _ hq,
    Periodic.cuspFunction_eq_of_nonzero h _ hq]
  simp

/-- Away from the cusp point, `cuspFunction` commutes with multiplication pointwise. -/
private theorem cuspFunction_mul_apply_of_ne_zero
    (h : ℝ) (f g : ℍ → ℂ) {q : ℂ} (hq : q ≠ 0) :
    cuspFunction h (f * g) q = cuspFunction h f q * cuspFunction h g q := by
  change Periodic.cuspFunction h _ q =
    Periodic.cuspFunction h _ q * Periodic.cuspFunction h _ q
  rw [Periodic.cuspFunction_eq_of_nonzero h _ hq,
    Periodic.cuspFunction_eq_of_nonzero h _ hq,
    Periodic.cuspFunction_eq_of_nonzero h _ hq]
  simp

/-- Cusp-function form of the `Y^2` coefficient remainder. -/
private theorem coxPhiTwo_coeff_two_remainder_cuspFunction_two_eventuallyEq :
    cuspFunction (2 : ℝ)
      ((coxPhiFunction (2 : ℕ+)).coeff 2 -
        polynomialInJ modularEquationTwoCoeffY2)
      =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
        fun q : ℂ =>
          -(cuspFunction 1 j (q ^ 4) +
            cuspFunction 1 j q +
            cuspFunction 1 j (-q)) -
          (-(cuspFunction 1 j (q ^ 2)) ^ 2 +
            1488 * cuspFunction 1 j (q ^ 2) - 162000) := by
  filter_upwards [cuspFunction_two_jN_two_eventuallyEq,
    cuspFunction_two_j_halfUpper_eventuallyEq,
    cuspFunction_two_j_halfTranslateUpper_eventuallyEq,
    cuspFunction_two_polynomialInJ_eventuallyEq modularEquationTwoCoeffY2,
    self_mem_nhdsWithin] with q hjN hhalf htrans hpoly hqmem
  have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hqmem
  have hcoeff :
      cuspFunction (2 : ℝ) ((coxPhiFunction (2 : ℕ+)).coeff 2) q =
        -(cuspFunction 1 j (q ^ 4) + cuspFunction 1 j q + cuspFunction 1 j (-q)) := by
    rw [coxPhiFunction_two_coeff_two]
    rw [cuspFunction_neg_apply_of_ne_zero (2 : ℝ) _ hq0,
      cuspFunction_add_apply_of_ne_zero (2 : ℝ) _ _ hq0,
      cuspFunction_add_apply_of_ne_zero (2 : ℝ) _ _ hq0, hjN, hhalf, htrans]
  rw [cuspFunction_sub_apply_of_ne_zero (2 : ℝ) _ _ hq0, hcoeff, hpoly]
  simp [modularEquationTwoCoeffY2]

/-- Cusp-function form of the `Y` coefficient remainder. -/
private theorem coxPhiTwo_coeff_one_remainder_cuspFunction_two_eventuallyEq :
    cuspFunction (2 : ℝ)
      ((coxPhiFunction (2 : ℕ+)).coeff 1 -
        polynomialInJ modularEquationTwoCoeffY1)
      =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
        fun q : ℂ =>
          cuspFunction 1 j (q ^ 4) * cuspFunction 1 j q +
          cuspFunction 1 j (q ^ 4) * cuspFunction 1 j (-q) +
          cuspFunction 1 j q * cuspFunction 1 j (-q) -
          (1488 * (cuspFunction 1 j (q ^ 2)) ^ 2 +
            40773375 * cuspFunction 1 j (q ^ 2) + 8748000000) := by
  filter_upwards [cuspFunction_two_jN_two_eventuallyEq,
    cuspFunction_two_j_halfUpper_eventuallyEq,
    cuspFunction_two_j_halfTranslateUpper_eventuallyEq,
    cuspFunction_two_polynomialInJ_eventuallyEq modularEquationTwoCoeffY1,
    self_mem_nhdsWithin] with q hjN hhalf htrans hpoly hqmem
  have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hqmem
  have hcoeff :
      cuspFunction (2 : ℝ) ((coxPhiFunction (2 : ℕ+)).coeff 1) q =
        cuspFunction 1 j (q ^ 4) * cuspFunction 1 j q +
          cuspFunction 1 j (q ^ 4) * cuspFunction 1 j (-q) +
            cuspFunction 1 j q * cuspFunction 1 j (-q) := by
    rw [coxPhiFunction_two_coeff_one]
    rw [cuspFunction_add_apply_of_ne_zero (2 : ℝ) _ _ hq0,
      cuspFunction_add_apply_of_ne_zero (2 : ℝ) _ _ hq0,
      cuspFunction_mul_apply_of_ne_zero (2 : ℝ) _ _ hq0,
      cuspFunction_mul_apply_of_ne_zero (2 : ℝ) _ _ hq0,
      cuspFunction_mul_apply_of_ne_zero (2 : ℝ) _ _ hq0, hjN, hhalf, htrans]
  rw [cuspFunction_sub_apply_of_ne_zero (2 : ℝ) _ _ hq0, hcoeff, hpoly]
  simp [modularEquationTwoCoeffY1]

/-- Cusp-function form of the constant coefficient remainder. -/
private theorem coxPhiTwo_coeff_zero_remainder_cuspFunction_two_eventuallyEq :
    cuspFunction (2 : ℝ)
      ((coxPhiFunction (2 : ℕ+)).coeff 0 -
        polynomialInJ modularEquationTwoCoeffY0)
      =ᶠ[nhdsWithin (0 : ℂ) ({0}ᶜ)]
        fun q : ℂ =>
          -(cuspFunction 1 j (q ^ 4) * cuspFunction 1 j q *
            cuspFunction 1 j (-q)) -
          ((cuspFunction 1 j (q ^ 2)) ^ 3 -
            162000 * (cuspFunction 1 j (q ^ 2)) ^ 2 +
            8748000000 * cuspFunction 1 j (q ^ 2) -
            157464000000000) := by
  filter_upwards [cuspFunction_two_jN_two_eventuallyEq,
    cuspFunction_two_j_halfUpper_eventuallyEq,
    cuspFunction_two_j_halfTranslateUpper_eventuallyEq,
    cuspFunction_two_polynomialInJ_eventuallyEq modularEquationTwoCoeffY0,
    self_mem_nhdsWithin] with q hjN hhalf htrans hpoly hqmem
  have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hqmem
  have hcoeff :
      cuspFunction (2 : ℝ) ((coxPhiFunction (2 : ℕ+)).coeff 0) q =
        -(cuspFunction 1 j (q ^ 4) * cuspFunction 1 j q *
          cuspFunction 1 j (-q)) := by
    rw [coxPhiFunction_two_coeff_zero]
    rw [cuspFunction_neg_apply_of_ne_zero (2 : ℝ) _ hq0,
      cuspFunction_mul_apply_of_ne_zero (2 : ℝ) _ _ hq0,
      cuspFunction_mul_apply_of_ne_zero (2 : ℝ) _ _ hq0, hjN, hhalf, htrans]
  rw [cuspFunction_sub_apply_of_ne_zero (2 : ℝ) _ _ hq0, hcoeff, hpoly]
  simp [modularEquationTwoCoeffY0]

/-- The punctured neighbourhood of `0` in `ℂ`. -/
private abbrev puncturedZero : Filter ℂ :=
  nhdsWithin (0 : ℂ) ({0}ᶜ)

/-- Non-zero powers preserve the punctured neighbourhood of `0` and tend to `0`. -/
private theorem tendsto_pow_puncturedZero (n : ℕ) (hn : n ≠ 0) :
    Tendsto (fun q : ℂ => q ^ n) puncturedZero puncturedZero := by
  have hq : Tendsto (fun q : ℂ => q) puncturedZero (nhds 0) := by
    simpa [puncturedZero] using
      (tendsto_id.mono_right nhdsWithin_le_nhds :
        Tendsto (fun q : ℂ => q) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds 0))
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (by
      have hzero : (0 : ℂ) ^ n = 0 := zero_pow hn
      simpa [hzero] using hq.pow n) ?_
  unfold puncturedZero
  filter_upwards [self_mem_nhdsWithin] with q hqmem
  exact Set.mem_compl_singleton_iff.mpr
    (pow_ne_zero n (Set.mem_compl_singleton_iff.mp hqmem))

/-- Negation preserves the punctured neighbourhood of `0` and tends to `0`. -/
private theorem tendsto_neg_puncturedZero :
    Tendsto (fun q : ℂ => -q) puncturedZero puncturedZero := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (by
      have hq : Tendsto (fun q : ℂ => q) puncturedZero (nhds 0) := by
        simpa [puncturedZero] using
          (tendsto_id.mono_right nhdsWithin_le_nhds :
            Tendsto (fun q : ℂ => q) (nhdsWithin (0 : ℂ) ({0}ᶜ)) (nhds 0))
      simpa using hq.neg) ?_
  unfold puncturedZero
  filter_upwards [self_mem_nhdsWithin] with q hqmem
  exact Set.mem_compl_singleton_iff.mpr
    (neg_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hqmem))

/-- Multiplying a finite-limit function by a positive power of `q` gives limit `0`. -/
private theorem tendsto_qpow_mul_puncturedZero {n : ℕ} (hn : n ≠ 0)
    {g : ℂ → ℂ} {a : ℂ} (hg : Tendsto g puncturedZero (nhds a)) :
    Tendsto (fun q : ℂ => q ^ n * g q) puncturedZero (nhds 0) := by
  have hqn : Tendsto (fun q : ℂ => q ^ n) puncturedZero (nhds 0) :=
    (tendsto_pow_puncturedZero n hn).mono_right nhdsWithin_le_nhds
  simpa using hqn.mul hg

/-- Pointwise addition of two functions tending to zero still tends to zero. -/
private theorem tendsto_function_add_zero {f g : ℂ → ℂ}
    (hf : Tendsto f puncturedZero (nhds 0)) (hg : Tendsto g puncturedZero (nhds 0)) :
    Tendsto (f + g) puncturedZero (nhds 0) := by
  simpa [Pi.add_apply] using hf.add hg

/-- A finite list sum of functions tending to zero also tends to zero. -/
private theorem list_sum_tendsto_zero (l : List (ℂ → ℂ))
    (h : ∀ f ∈ l, Tendsto f puncturedZero (nhds 0)) :
    Tendsto l.sum puncturedZero (nhds 0) := by
  induction l with
  | nil =>
      change Tendsto (fun _ : ℂ => (0 : ℂ)) puncturedZero (nhds 0)
      exact tendsto_const_nhds
  | cons f fs ih =>
      simpa using tendsto_function_add_zero
        (h f (by simp)) (ih fun g hg => h g (by simp [hg]))

/-- The one-term Laurent remainder for `j`, used in the `Y^2` coefficient model. -/
private def coxPhiTwoCoeffTwoR (q : ℂ) : ℂ :=
  (cuspFunction 1 j q - (q⁻¹ + 744 + 196884 * q)) / q

/-- The level-`2` `Y^2`-coefficient Laurent remainder tends to zero. -/
private theorem coxPhiTwoCoeffTwoR_tendsto_zero :
    Tendsto coxPhiTwoCoeffTwoR puncturedZero (nhds 0) := by
  simpa [coxPhiTwoCoeffTwoR, puncturedZero] using j_cuspFunction_three_term_remainder

/-- The simple model obtained after substituting the first Laurent remainder in
the `Y^2` coefficient identity. -/
private def coxPhiTwoCoeffTwoModel : ℂ → ℂ := fun q =>
  2 * coxPhiTwoCoeffTwoR (q ^ 2) - q * coxPhiTwoCoeffTwoR q +
    q * coxPhiTwoCoeffTwoR (-q) +
      q ^ 4 *
        ((196884 + coxPhiTwoCoeffTwoR (q ^ 2)) ^ 2 - 196884 -
          coxPhiTwoCoeffTwoR (q ^ 4))

/-- The `Y^2`-coefficient model tends to zero. -/
private theorem coxPhiTwoCoeffTwoModel_tendsto_zero :
    Tendsto coxPhiTwoCoeffTwoModel puncturedZero (nhds 0) := by
  have hR := coxPhiTwoCoeffTwoR_tendsto_zero
  have hRneg : Tendsto (fun q : ℂ => coxPhiTwoCoeffTwoR (-q)) puncturedZero
      (nhds 0) :=
    hR.comp tendsto_neg_puncturedZero
  have hR2 : Tendsto (fun q : ℂ => coxPhiTwoCoeffTwoR (q ^ 2)) puncturedZero
      (nhds 0) :=
    hR.comp (tendsto_pow_puncturedZero 2 (by norm_num))
  have hR4 : Tendsto (fun q : ℂ => coxPhiTwoCoeffTwoR (q ^ 4)) puncturedZero
      (nhds 0) :=
    hR.comp (tendsto_pow_puncturedZero 4 (by norm_num))
  have hqpow {n : ℕ} (hn : n ≠ 0) {g : ℂ → ℂ} {a : ℂ}
      (hg : Tendsto g puncturedZero (nhds a)) :
      Tendsto (fun q : ℂ => q ^ n * g q) puncturedZero (nhds 0) :=
    tendsto_qpow_mul_puncturedZero hn hg
  have hmodel :
      Tendsto
        (fun q : ℂ =>
          2 * coxPhiTwoCoeffTwoR (q ^ 2) - q * coxPhiTwoCoeffTwoR q +
            q * coxPhiTwoCoeffTwoR (-q) +
              q ^ 4 * ((196884 + coxPhiTwoCoeffTwoR (q ^ 2)) ^ 2 - 196884 -
                coxPhiTwoCoeffTwoR (q ^ 4)))
        puncturedZero (nhds 0) := by
    convert
      ((((tendsto_const_nhds (x := (2 : ℂ))).mul hR2).sub
        (hqpow (show (1 : ℕ) ≠ 0 by norm_num) hR)).add
        (hqpow (show (1 : ℕ) ≠ 0 by norm_num) hRneg)).add
        (hqpow (show (4 : ℕ) ≠ 0 by norm_num)
          ((((tendsto_const_nhds (x := (196884 : ℂ))).add hR2).pow 2).sub
            (tendsto_const_nhds (x := (196884 : ℂ))) |>.sub hR4))
        using 1
    · ring_nf
    · ring_nf
  simpa [coxPhiTwoCoeffTwoModel] using hmodel

/-- The explicit Laurent model for the `Y^2` coefficient remainder tends to zero. -/
private theorem coxPhiTwo_coeff_two_model_tendsto_zero :
    Tendsto
      (fun q : ℂ =>
        -(cuspFunction 1 j (q ^ 4) + cuspFunction 1 j q + cuspFunction 1 j (-q)) -
          (-(cuspFunction 1 j (q ^ 2)) ^ 2 +
            1488 * cuspFunction 1 j (q ^ 2) - 162000))
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds 0) := by
  have hEq :
      (fun q : ℂ =>
        -(cuspFunction 1 j (q ^ 4) + cuspFunction 1 j q + cuspFunction 1 j (-q)) -
          (-(cuspFunction 1 j (q ^ 2)) ^ 2 +
            1488 * cuspFunction 1 j (q ^ 2) - 162000)) =ᶠ[puncturedZero]
        coxPhiTwoCoeffTwoModel := by
    unfold puncturedZero
    filter_upwards [self_mem_nhdsWithin] with q hqmem
    have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hqmem
    have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq0
    have hq4 : q ^ 4 ≠ 0 := pow_ne_zero 4 hq0
    have hnq : -q ≠ 0 := neg_ne_zero.mpr hq0
    simp [coxPhiTwoCoeffTwoModel, coxPhiTwoCoeffTwoR]
    field_simp [hq0, hq2, hq4, hnq]
    ring
  simpa [puncturedZero] using coxPhiTwoCoeffTwoModel_tendsto_zero.congr' hEq.symm

/-- The five-term Laurent remainder for `j` used in the `Y`-coefficient model. -/
private def coxPhiTwoCoeffOneR (q : ℂ) : ℂ :=
  (cuspFunction 1 j q -
    (q⁻¹ + 744 + 196884 * q + 21493760 * q ^ 2 +
      864299970 * q ^ 3 + 20245856256 * q ^ 4)) / q ^ 4

/-- The level-`2` `Y`-coefficient Laurent remainder tends to zero. -/
private theorem coxPhiTwoCoeffOneR_tendsto_zero :
    Tendsto coxPhiTwoCoeffOneR puncturedZero (nhds 0) := by
  simpa [coxPhiTwoCoeffOneR, puncturedZero] using j_cuspFunction_five_term_remainder

/-- A coefficient package for one power of `q` in the `Y`-coefficient model. -/
private def coxPhiTwoCoeffOneB
    (C A0 An A2 A4 A0n A22 An4 A04 : ℂ) (q : ℂ) : ℂ :=
  C + A0 * coxPhiTwoCoeffOneR q + An * coxPhiTwoCoeffOneR (-q) +
    A2 * coxPhiTwoCoeffOneR (q ^ 2) + A4 * coxPhiTwoCoeffOneR (q ^ 4) +
    A0n * coxPhiTwoCoeffOneR q * coxPhiTwoCoeffOneR (-q) +
    A22 * (coxPhiTwoCoeffOneR (q ^ 2)) ^ 2 +
    An4 * coxPhiTwoCoeffOneR (-q) * coxPhiTwoCoeffOneR (q ^ 4) +
    A04 * coxPhiTwoCoeffOneR q * coxPhiTwoCoeffOneR (q ^ 4)

/-- Each `Y`-coefficient package tends to its constant term. -/
private theorem coxPhiTwoCoeffOneB_tendsto
    (C A0 An A2 A4 A0n A22 An4 A04 : ℂ) :
    Tendsto (coxPhiTwoCoeffOneB C A0 An A2 A4 A0n A22 An4 A04)
      puncturedZero (nhds C) := by
  have hR := coxPhiTwoCoeffOneR_tendsto_zero
  have hRneg : Tendsto (fun q : ℂ => coxPhiTwoCoeffOneR (-q)) puncturedZero
      (nhds 0) := hR.comp tendsto_neg_puncturedZero
  have hR2 : Tendsto (fun q : ℂ => coxPhiTwoCoeffOneR (q ^ 2)) puncturedZero
      (nhds 0) := hR.comp (tendsto_pow_puncturedZero 2 (by norm_num))
  have hR4 : Tendsto (fun q : ℂ => coxPhiTwoCoeffOneR (q ^ 4)) puncturedZero
      (nhds 0) := hR.comp (tendsto_pow_puncturedZero 4 (by norm_num))
  convert ((((((((tendsto_const_nhds (x := C)).add
    ((tendsto_const_nhds (x := A0)).mul hR)).add
    ((tendsto_const_nhds (x := An)).mul hRneg)).add
    ((tendsto_const_nhds (x := A2)).mul hR2)).add
    ((tendsto_const_nhds (x := A4)).mul hR4)).add
    ((tendsto_const_nhds (x := A0n)).mul (hR.mul hRneg))).add
    ((tendsto_const_nhds (x := A22)).mul (hR2.pow 2))).add
    ((tendsto_const_nhds (x := An4)).mul (hRneg.mul hR4))).add
    ((tendsto_const_nhds (x := A04)).mul (hR.mul hR4)) using 1
  · ext q
    simp [coxPhiTwoCoeffOneB]
    ring_nf
  · ring_nf

/-- One `q^n`-weighted coefficient package in the `Y`-coefficient model. -/
private def coxPhiTwoCoeffOneT
    (n : ℕ) (C A0 An A2 A4 A0n A22 An4 A04 : ℂ) (q : ℂ) : ℂ :=
  q ^ n * coxPhiTwoCoeffOneB C A0 An A2 A4 A0n A22 An4 A04 q

/-- A positive `q`-power times a `Y`-coefficient package tends to zero. -/
private theorem coxPhiTwoCoeffOneT_tendsto
    (n : ℕ) (hn : n ≠ 0) (C A0 An A2 A4 A0n A22 An4 A04 : ℂ) :
    Tendsto (coxPhiTwoCoeffOneT n C A0 An A2 A4 A0n A22 An4 A04)
      puncturedZero (nhds 0) := by
  simpa [coxPhiTwoCoeffOneT] using tendsto_qpow_mul_puncturedZero hn
    (coxPhiTwoCoeffOneB_tendsto C A0 An A2 A4 A0n A22 An4 A04)

/-- A `Y`-coefficient `T`-term tends to zero when its constant term vanishes
or it carries a positive q-power. -/
private theorem coxPhiTwoCoeffOneT_tendsto_zero_of_const_or_pos
    {n : ℕ} {C A0 An A2 A4 A0n A22 An4 A04 : ℂ} (h : C = 0 ∨ n ≠ 0) :
    Tendsto (coxPhiTwoCoeffOneT n C A0 An A2 A4 A0n A22 An4 A04)
      puncturedZero (nhds 0) := by
  by_cases hn : n = 0
  · subst n
    have hC : C = 0 := by
      rcases h with hC | hnz
      · exact hC
      · contradiction
    convert coxPhiTwoCoeffOneB_tendsto 0 A0 An A2 A4 A0n A22 An4 A04 using 1
    ext q
    rw [hC]
    simp [coxPhiTwoCoeffOneT]
  · exact coxPhiTwoCoeffOneT_tendsto n hn C A0 An A2 A4 A0n A22 An4 A04

/-- The terms in the `Y`-coefficient model after substituting the Laurent remainder. -/
private def coxPhiTwoCoeffOneTerms : List (ℂ → ℂ) := [
  coxPhiTwoCoeffOneT 0 0 1 1 0 0 0 0 0 0,
  coxPhiTwoCoeffOneT 2 (-8504046600192) 0 0 0 0 0 0 0 0,
  coxPhiTwoCoeffOneT 3 0 (-1) 1 0 0 0 0 0 0,
  coxPhiTwoCoeffOneT 4 (-802315368030800) 1488 1488 0 0 0 0 0 0,
  coxPhiTwoCoeffOneT 5 0 (-196884) 196884 0 0 0 0 0 0,
  coxPhiTwoCoeffOneT 6 73505043411651774 21493760 21493760 (-2976) 0 0 0 0 0,
  coxPhiTwoCoeffOneT 7 0 (-864299970) 864299970 0 0 0 0 0 0,
  coxPhiTwoCoeffOneT 8 407838503310834650880 20246053140 20246053140 (-42987519)
    0 1 0 0 0,
  coxPhiTwoCoeffOneT 10 (-67146984504571592704) 0 0 (-585926784) 0 0 0 0 0,
  coxPhiTwoCoeffOneT 12 (-2405722059792721637280) 21493760 21493760
    (-63965429760) 0 0 0 0 0,
  coxPhiTwoCoeffOneT 14 (-52075477879030647889920) 0 0 (-2572156710720) 0 0 0 0 0,
  coxPhiTwoCoeffOneT 16 (-609888309945422929920000) 864299970 864299970
    (-60251668217856) 1488 0 (-1488) 0 0,
  coxPhiTwoCoeffOneT 18 870319150721925120 0 0 0 42987520 0 0 0 0,
  coxPhiTwoCoeffOneT 20 819789391077228675072 20245856256 20245856256 0
    40491712512 0 0 1 1
]

/-- The model obtained after substituting the five-term Laurent remainder in the
`Y` coefficient identity. -/
private def coxPhiTwoCoeffOneModel : ℂ → ℂ :=
  coxPhiTwoCoeffOneTerms.sum

/-- The `Y`-coefficient model tends to zero term by term. -/
private theorem coxPhiTwoCoeffOneModel_tendsto_zero :
    Tendsto coxPhiTwoCoeffOneModel puncturedZero (nhds 0) := by
  rw [coxPhiTwoCoeffOneModel]
  apply list_sum_tendsto_zero
  intro f hf
  simp [coxPhiTwoCoeffOneTerms] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  all_goals exact coxPhiTwoCoeffOneT_tendsto_zero_of_const_or_pos (by norm_num)

/-- The explicit Laurent model for the `Y` coefficient remainder tends to zero. -/
private theorem coxPhiTwo_coeff_one_model_tendsto_zero :
    Tendsto
      (fun q : ℂ =>
        cuspFunction 1 j (q ^ 4) * cuspFunction 1 j q +
        cuspFunction 1 j (q ^ 4) * cuspFunction 1 j (-q) +
        cuspFunction 1 j q * cuspFunction 1 j (-q) -
        (1488 * (cuspFunction 1 j (q ^ 2)) ^ 2 +
          40773375 * cuspFunction 1 j (q ^ 2) + 8748000000))
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds 0) := by
  have hEq :
      (fun q : ℂ =>
        cuspFunction 1 j (q ^ 4) * cuspFunction 1 j q +
        cuspFunction 1 j (q ^ 4) * cuspFunction 1 j (-q) +
        cuspFunction 1 j q * cuspFunction 1 j (-q) -
        (1488 * (cuspFunction 1 j (q ^ 2)) ^ 2 +
          40773375 * cuspFunction 1 j (q ^ 2) + 8748000000)) =ᶠ[puncturedZero]
        coxPhiTwoCoeffOneModel := by
    unfold puncturedZero
    filter_upwards [self_mem_nhdsWithin] with q hqmem
    have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hqmem
    have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq0
    have hq4 : q ^ 4 ≠ 0 := pow_ne_zero 4 hq0
    have hq8 : q ^ 8 ≠ 0 := pow_ne_zero 8 hq0
    have hq16 : q ^ 16 ≠ 0 := pow_ne_zero 16 hq0
    have hnq : -q ≠ 0 := neg_ne_zero.mpr hq0
    have hnq4 : (-q) ^ 4 ≠ 0 := pow_ne_zero 4 hnq
    simp [coxPhiTwoCoeffOneModel, coxPhiTwoCoeffOneTerms, coxPhiTwoCoeffOneT,
      coxPhiTwoCoeffOneB, coxPhiTwoCoeffOneR]
    field_simp [hq0, hq2, hq4, hq8, hq16, hnq, hnq4]
    ring
  simpa [puncturedZero] using coxPhiTwoCoeffOneModel_tendsto_zero.congr' hEq.symm

/-- The six-term Laurent remainder for `j` at the cusp. -/
private def coxPhiTwoCoeffZeroR (q : ℂ) : ℂ :=
  (cuspFunction 1 j q -
    (q⁻¹ + 744 + 196884 * q + 21493760 * q ^ 2 +
      864299970 * q ^ 3 + 20245856256 * q ^ 4 +
        333202640600 * q ^ 5)) / q ^ 5

/-- The level-`2` constant-term Laurent remainder tends to zero. -/
private theorem coxPhiTwoCoeffZeroR_tendsto_zero :
    Tendsto coxPhiTwoCoeffZeroR puncturedZero (nhds 0) := by
  simpa [coxPhiTwoCoeffZeroR, puncturedZero] using j_cuspFunction_six_term_remainder

/-- A coefficient package for one power of `q` in the constant-term model. -/
private def coxPhiTwoCoeffZeroB
    (C A0 An A2 A4 A0n A22 A222 A04 An4 A0n4 : ℂ) (q : ℂ) : ℂ :=
  C + A0 * coxPhiTwoCoeffZeroR q + An * coxPhiTwoCoeffZeroR (-q) +
    A2 * coxPhiTwoCoeffZeroR (q ^ 2) + A4 * coxPhiTwoCoeffZeroR (q ^ 4) +
    A0n * coxPhiTwoCoeffZeroR q * coxPhiTwoCoeffZeroR (-q) +
    A22 * (coxPhiTwoCoeffZeroR (q ^ 2)) ^ 2 +
    A222 * (coxPhiTwoCoeffZeroR (q ^ 2)) ^ 3 +
    A04 * coxPhiTwoCoeffZeroR q * coxPhiTwoCoeffZeroR (q ^ 4) +
    An4 * coxPhiTwoCoeffZeroR (-q) * coxPhiTwoCoeffZeroR (q ^ 4) +
    A0n4 * coxPhiTwoCoeffZeroR q * coxPhiTwoCoeffZeroR (-q) *
      coxPhiTwoCoeffZeroR (q ^ 4)

/-- Each coefficient package tends to its constant term. -/
private theorem coxPhiTwoCoeffZeroB_tendsto
    (C A0 An A2 A4 A0n A22 A222 A04 An4 A0n4 : ℂ) :
    Tendsto (coxPhiTwoCoeffZeroB C A0 An A2 A4 A0n A22 A222 A04 An4 A0n4)
      puncturedZero (nhds C) := by
  have hR := coxPhiTwoCoeffZeroR_tendsto_zero
  have hneg : Tendsto (fun q : ℂ => -q) puncturedZero puncturedZero := by
    simpa using tendsto_neg_puncturedZero
  have hRneg : Tendsto (fun q : ℂ => coxPhiTwoCoeffZeroR (-q)) puncturedZero
      (nhds 0) := hR.comp hneg
  have hR2 : Tendsto (fun q : ℂ => coxPhiTwoCoeffZeroR (q ^ 2)) puncturedZero
      (nhds 0) := hR.comp (tendsto_pow_puncturedZero 2 (by norm_num))
  have hR4 : Tendsto (fun q : ℂ => coxPhiTwoCoeffZeroR (q ^ 4)) puncturedZero
      (nhds 0) := hR.comp (tendsto_pow_puncturedZero 4 (by norm_num))
  convert ((((((((((tendsto_const_nhds (x := C)).add
    ((tendsto_const_nhds (x := A0)).mul hR)).add
    ((tendsto_const_nhds (x := An)).mul hRneg)).add
    ((tendsto_const_nhds (x := A2)).mul hR2)).add
    ((tendsto_const_nhds (x := A4)).mul hR4)).add
    ((tendsto_const_nhds (x := A0n)).mul (hR.mul hRneg))).add
    ((tendsto_const_nhds (x := A22)).mul (hR2.pow 2))).add
    ((tendsto_const_nhds (x := A222)).mul (hR2.pow 3))).add
    ((tendsto_const_nhds (x := A04)).mul (hR.mul hR4))).add
    ((tendsto_const_nhds (x := An4)).mul (hRneg.mul hR4))).add
    ((tendsto_const_nhds (x := A0n4)).mul ((hR.mul hRneg).mul hR4)) using 1
  · ext q
    simp [coxPhiTwoCoeffZeroB]
    ring_nf
  · ring_nf

/-- One `q^n`-weighted coefficient package in the constant-term model. -/
private def coxPhiTwoCoeffZeroT
    (n : ℕ) (C A0 An A2 A4 A0n A22 A222 A04 An4 A0n4 : ℂ) (q : ℂ) : ℂ :=
  q ^ n * coxPhiTwoCoeffZeroB C A0 An A2 A4 A0n A22 A222 A04 An4 A0n4 q

/-- A positive `q`-power times any coefficient package tends to zero. -/
private theorem coxPhiTwoCoeffZeroT_tendsto
    (n : ℕ) (hn : n ≠ 0) (C A0 An A2 A4 A0n A22 A222 A04 An4 A0n4 : ℂ) :
    Tendsto (coxPhiTwoCoeffZeroT n C A0 An A2 A4 A0n A22 A222 A04 An4 A0n4)
      puncturedZero (nhds 0) := by
  simpa [coxPhiTwoCoeffZeroT] using tendsto_qpow_mul_puncturedZero hn
    (coxPhiTwoCoeffZeroB_tendsto C A0 An A2 A4 A0n A22 A222 A04 An4 A0n4)


/-- A `T`-term in the constant-coefficient model tends to zero if either its
constant package term is zero or it carries a positive q-power. -/
private theorem coxPhiTwoCoeffZeroT_tendsto_zero_of_const_or_pos
    {n : ℕ} {C A0 An A2 A4 A0n A22 A222 A04 An4 A0n4 : ℂ}
    (h : C = 0 ∨ n ≠ 0) :
    Tendsto (coxPhiTwoCoeffZeroT n C A0 An A2 A4 A0n A22 A222 A04 An4 A0n4)
      puncturedZero (nhds 0) := by
  by_cases hn : n = 0
  · subst n
    have hC : C = 0 := by
      rcases h with hC | hnz
      · exact hC
      · contradiction
    convert coxPhiTwoCoeffZeroB_tendsto 0 A0 An A2 A4 A0n A22 A222 A04 An4 A0n4
      using 1
    ext q
    rw [hC]
    simp [coxPhiTwoCoeffZeroT]
  · exact coxPhiTwoCoeffZeroT_tendsto n hn C A0 An A2 A4 A0n A22 A222 A04 An4 A0n4

/-- The 31 terms obtained after substituting the six-term Laurent remainder. -/
private def coxPhiTwoCoeffZeroTerms : List (ℂ → ℂ) := [
  coxPhiTwoCoeffZeroT
          0
          0
          1
          1
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          1
          0
          (-744)
          744
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          2
          6237696682398978
          196884
          196884
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          3
          0
          (-21493760)
          21493760
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          4
          165790506970509660000
          864300714
          864300714
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          5
          0
          (-20246409792)
          20246409792
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          6
          111023873495779700020536
          333349122296
          333349122296
          (-3)
          0
          1
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          7
          0
          (-15991357440)
          15991357440
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          8
          123486691818658638327552
          643039374564
          643039374564
          319536
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          9
          0
          (-15063063536160)
          15063063536160
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          10
          82607407331862585457481574
          247941527915856
          247941527915856
          (-8509785912)
          0
          744
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          11
          0
          (-4231777443840)
          4231777443840
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          12
          32940105833913862049000368
          170166856787240
          170166856787240
          62782563264
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          13
          0
          (-3986101154463744)
          3986101154463744
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          14
          21864703946595852025938474648
          65606500469334240
          65606500469334240
          6746554367172
          0
          196884
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          15
          0
          (-461981718937600)
          461981718937600
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          16
          3621649930687494100711031040
          18577056987487170
          18577056987487170
          250662815413344
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          17
          0
          (-435160218400140240)
          435160218400140240
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          18
          2384538878979695861939371091224
          7161947755257949480
          7161947755257949480
          4060334540199936
          1
          21493760
          (-3)
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          19
          0
          (-18577056123187200)
          18577056123187200
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          20
          44366451755678144297973643392
          747014458387857156
          747014458387857156
          (-28908608750999424)
          (-159768)
          0
          159768
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          21
          0
          (-17498508017602166784)
          17498508017602166784
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          22
          93213107619708176158567987936320
          287991018359663888304
          287991018359663888304
          (-5245614378743120460)
          8509194516
          864299970
          (-590652)
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          23
          0
          (-435159575360962560)
          435159575360962560
          0
          0
          0
          0
          0
          0
          0
          0,
  coxPhiTwoCoeffZeroT
          24
          (-47078534368997040157126510559232)
          17498493287887752920
          17498493287887752920
          (-147961623258646609920)
          (-151107477178368)
          0
          (-64481280)
          0
          1
          1
          0,
  coxPhiTwoCoeffZeroT
          25
          0
          (-409894943441378943936)
          409894943441378943936
          0
          0
          0
          0
          0
          (-744)
          744
          0,
  coxPhiTwoCoeffZeroT
          26
          1550170467590357686063965005023200
          6746038367975921484000
          6746038367975921484000
          (-2957606280262847704608)
          7899824803856580
          20245856256
          (-2592899910)
          0
          196884
          196884
          0,
  coxPhiTwoCoeffZeroT
          27
          0
          (-7161777588422656000)
          7161777588422656000
          0
          0
          0
          0
          0
          (-21493760)
          21493760
          0,
  coxPhiTwoCoeffZeroT
          28
          (-6687989732544559248607639579641600)
          287987032274500782000
          287987032274500782000
          (-40475836594243377561600)
          166079369010387226464
          0
          (-60737568768)
          0
          864299970
          864299970
          0,
  coxPhiTwoCoeffZeroT
          29
          0
          (-6745972765707229593600)
          6745972765707229593600
          0
          0
          0
          0
          0
          (-20245856256)
          20245856256
          0,
  coxPhiTwoCoeffZeroT
          30
          0
          111023999702812768360000
          111023999702812768360000
          (-333071999108438305080000)
          111023999702812768360000
          333202640600
          (-999607921800)
          (-1)
          333202640600
          333202640600
          1
]

/-- The 31-term model obtained after substituting the six-term Laurent remainder. -/
private def coxPhiTwoCoeffZeroModel : ℂ → ℂ :=
  coxPhiTwoCoeffZeroTerms.sum

/-- The 31-term constant-coefficient model tends to zero term by term. -/
private theorem coxPhiTwoCoeffZeroModel_tendsto_zero :
    Tendsto coxPhiTwoCoeffZeroModel puncturedZero (nhds 0) := by
  rw [coxPhiTwoCoeffZeroModel]
  apply list_sum_tendsto_zero
  intro f hf
  simp [coxPhiTwoCoeffZeroTerms] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl
  all_goals exact coxPhiTwoCoeffZeroT_tendsto_zero_of_const_or_pos (by norm_num)

/-- The explicit Laurent model for the constant coefficient remainder tends to zero. -/
private theorem coxPhiTwo_coeff_zero_model_tendsto_zero :
    Tendsto
      (fun q : ℂ =>
        -(cuspFunction 1 j (q ^ 4) * cuspFunction 1 j q *
          cuspFunction 1 j (-q)) -
        ((cuspFunction 1 j (q ^ 2)) ^ 3 -
          162000 * (cuspFunction 1 j (q ^ 2)) ^ 2 +
          8748000000 * cuspFunction 1 j (q ^ 2) -
          157464000000000))
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds 0) := by
  have hEq :
      (fun q : ℂ =>
        -(cuspFunction 1 j (q ^ 4) * cuspFunction 1 j q *
          cuspFunction 1 j (-q)) -
        ((cuspFunction 1 j (q ^ 2)) ^ 3 -
          162000 * (cuspFunction 1 j (q ^ 2)) ^ 2 +
          8748000000 * cuspFunction 1 j (q ^ 2) -
          157464000000000)) =ᶠ[puncturedZero]
        coxPhiTwoCoeffZeroModel := by
    unfold puncturedZero
    filter_upwards [self_mem_nhdsWithin] with q hqmem
    have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hqmem
    have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq0
    have hq4 : q ^ 4 ≠ 0 := pow_ne_zero 4 hq0
    have hq10 : q ^ 10 ≠ 0 := pow_ne_zero 10 hq0
    have hq20 : q ^ 20 ≠ 0 := pow_ne_zero 20 hq0
    have hnq : -q ≠ 0 := neg_ne_zero.mpr hq0
    have hnq5 : (-q) ^ 5 ≠ 0 := pow_ne_zero 5 hnq
    simp [coxPhiTwoCoeffZeroModel, coxPhiTwoCoeffZeroTerms, coxPhiTwoCoeffZeroT,
      coxPhiTwoCoeffZeroB, coxPhiTwoCoeffZeroR]
    field_simp [hq0, hq2, hq4, hq10, hq20, hnq, hnq5]
    ring
  simpa [puncturedZero] using coxPhiTwoCoeffZeroModel_tendsto_zero.congr' hEq.symm

/-- The width-`2` cusp function of the `Y^2` coefficient remainder tends to zero. -/
private theorem coxPhiTwo_coeff_two_remainder_cuspFunction_two_tendsto_zero :
    Tendsto
      (cuspFunction (2 : ℝ)
        ((coxPhiFunction (2 : ℕ+)).coeff 2 -
          polynomialInJ modularEquationTwoCoeffY2))
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds 0) :=
  coxPhiTwo_coeff_two_model_tendsto_zero.congr'
    coxPhiTwo_coeff_two_remainder_cuspFunction_two_eventuallyEq.symm

/-- A level-`2` Cox coefficient remainder is invariant under the weight-zero
`SL₂(ℤ)` slash action. -/
private theorem coxPhiTwo_coeff_remainder_slashInvariant
    (n : ℕ) (P : Polynomial ℂ) (γ : SL(2, ℤ)) :
    (((coxPhiFunction (2 : ℕ+)).coeff n - polynomialInJ P) ∣[(0 : ℤ)] γ) =
      (coxPhiFunction (2 : ℕ+)).coeff n - polynomialInJ P := by
  ext z
  have hcoeff := congrFun (coxPhiFunction_coeff_slashInvariant (2 : ℕ+) n γ) z
  have hpoly := congrFun (polynomialInJ_slashInvariant P γ) z
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one] at hcoeff
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one] at hpoly
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one, Pi.sub_apply]
  rw [hcoeff, hpoly]

/-- A level-`2` coefficient remainder is zero at imaginary infinity once its
width-`2` cusp function tends to zero at the punctured cusp. -/
private theorem coxPhiTwo_coeff_remainder_IsZeroAtImInfty_of_cusp_tendsto_zero
    (n : ℕ) (P : Polynomial ℂ)
    (hcusp :
      Tendsto
        (cuspFunction (2 : ℝ)
          ((coxPhiFunction (2 : ℕ+)).coeff n - polynomialInJ P))
        puncturedZero (nhds 0)) :
    IsZeroAtImInfty ((coxPhiFunction (2 : ℕ+)).coeff n - polynomialInJ P) := by
  let F : ℍ → ℂ := (coxPhiFunction (2 : ℕ+)).coeff n - polynomialInJ P
  change IsZeroAtImInfty F
  have hslashF : ∀ γ : SL(2, ℤ), F ∣[(0 : ℤ)] γ = F := by
    intro γ
    simpa [F] using coxPhiTwo_coeff_remainder_slashInvariant n P γ
  have hper1 : Periodic (F ∘ UpperHalfPlane.ofComplex) (1 : ℝ) :=
    periodic_comp_of_slashInvariant_one hslashF
  have hper2 : Periodic (F ∘ UpperHalfPlane.ofComplex) (2 : ℝ) := by
    simpa using hper1.nat_mul 2
  have hq :
      Tendsto (fun τ : ℍ => 𝕢 (2 : ℝ) τ) atImInfty puncturedZero := by
    simpa [puncturedZero] using
      (Periodic.qParam_tendsto (h := (2 : ℝ)) (by norm_num)).comp
        tendsto_coe_atImInfty
  have ht :
      Tendsto (fun τ : ℍ => cuspFunction (2 : ℝ) F (𝕢 (2 : ℝ) τ))
        atImInfty (nhds 0) := by
    have hcuspF : Tendsto (cuspFunction (2 : ℝ) F) puncturedZero (nhds 0) := by
      simpa [F] using hcusp
    exact hcuspF.comp hq
  have hfun : (fun τ : ℍ => cuspFunction (2 : ℝ) F (𝕢 (2 : ℝ) τ)) = F := by
    funext τ
    exact UpperHalfPlane.eq_cuspFunction (h := (2 : ℝ)) (f := F) τ (by norm_num) hper2
  rw [hfun] at ht
  exact ht

/-- If a level-`2` Cox coefficient remainder is zero at infinity, the
corresponding coefficient is the prescribed polynomial in `j`. -/
private theorem coxPhiTwo_coeff_eq_polynomialInJ_of_remainder_zero
    (n : ℕ) (P : Polynomial ℂ)
    (hzero :
      IsZeroAtImInfty ((coxPhiFunction (2 : ℕ+)).coeff n - polynomialInJ P)) :
    (coxPhiFunction (2 : ℕ+)).coeff n = polynomialInJ P := by
  let F : ℍ → ℂ := (coxPhiFunction (2 : ℕ+)).coeff n - polynomialInJ P
  have hslashF : ∀ γ : SL(2, ℤ), F ∣[(0 : ℤ)] γ = F := by
    intro γ
    simpa [F] using coxPhiTwo_coeff_remainder_slashInvariant n P γ
  have hmdiffF : MDiff F :=
    (coxPhiFunction_coeff_MDifferentiable (2 : ℕ+) n).sub
      (polynomialInJ_MDifferentiable P)
  have hFzero : F = 0 :=
    levelOne_weightZero_eq_zero_of_slash_zero_at_infty hslashF hmdiffF (by
      simpa [F] using hzero)
  ext z
  have hz := congrFun hFzero z
  simpa [F] using sub_eq_zero.mp hz

/-- The `Y^2` coefficient remainder vanishes at imaginary infinity. -/
private theorem coxPhiTwo_coeff_two_remainder_IsZeroAtImInfty :
    IsZeroAtImInfty
      ((coxPhiFunction (2 : ℕ+)).coeff 2 -
        polynomialInJ modularEquationTwoCoeffY2) :=
  coxPhiTwo_coeff_remainder_IsZeroAtImInfty_of_cusp_tendsto_zero
    2 modularEquationTwoCoeffY2 coxPhiTwo_coeff_two_remainder_cuspFunction_two_tendsto_zero

/-- The `Y^2` coefficient identity for the explicit `Φ₂` in the `N = 2` example. -/
theorem coxPhiTwo_coeff_two_identity :
    -((jN (2 : ℕ+)) +
      (fun z : ℍ => j (halfUpper z)) +
      (fun z : ℍ => j (halfTranslateUpper z))) =
      polynomialInJ modularEquationTwoCoeffY2 := by
  have hcoeff :
      (coxPhiFunction (2 : ℕ+)).coeff 2 = polynomialInJ modularEquationTwoCoeffY2 :=
    coxPhiTwo_coeff_eq_polynomialInJ_of_remainder_zero
      2 modularEquationTwoCoeffY2 coxPhiTwo_coeff_two_remainder_IsZeroAtImInfty
  rw [← coxPhiFunction_two_coeff_two]
  exact hcoeff

/-- The width-`2` cusp function of the `Y` coefficient remainder tends to zero. -/
private theorem coxPhiTwo_coeff_one_remainder_cuspFunction_two_tendsto_zero :
    Tendsto
      (cuspFunction (2 : ℝ)
        ((coxPhiFunction (2 : ℕ+)).coeff 1 -
          polynomialInJ modularEquationTwoCoeffY1))
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds 0) :=
  coxPhiTwo_coeff_one_model_tendsto_zero.congr'
    coxPhiTwo_coeff_one_remainder_cuspFunction_two_eventuallyEq.symm

/-- The `Y` coefficient remainder vanishes at imaginary infinity. -/
private theorem coxPhiTwo_coeff_one_remainder_IsZeroAtImInfty :
    IsZeroAtImInfty
      ((coxPhiFunction (2 : ℕ+)).coeff 1 -
        polynomialInJ modularEquationTwoCoeffY1) :=
  coxPhiTwo_coeff_remainder_IsZeroAtImInfty_of_cusp_tendsto_zero
    1 modularEquationTwoCoeffY1 coxPhiTwo_coeff_one_remainder_cuspFunction_two_tendsto_zero

/-- The `Y` coefficient identity for the explicit `Φ₂` in the `N = 2` example. -/
theorem coxPhiTwo_coeff_one_identity :
    (jN (2 : ℕ+)) * (fun z : ℍ => j (halfUpper z)) +
    (jN (2 : ℕ+)) * (fun z : ℍ => j (halfTranslateUpper z)) +
    (fun z : ℍ => j (halfUpper z)) *
      (fun z : ℍ => j (halfTranslateUpper z)) =
      polynomialInJ modularEquationTwoCoeffY1 := by
  have hcoeff :
      (coxPhiFunction (2 : ℕ+)).coeff 1 = polynomialInJ modularEquationTwoCoeffY1 :=
    coxPhiTwo_coeff_eq_polynomialInJ_of_remainder_zero
      1 modularEquationTwoCoeffY1 coxPhiTwo_coeff_one_remainder_IsZeroAtImInfty
  rw [← coxPhiFunction_two_coeff_one]
  exact hcoeff

/-- The width-`2` cusp function of the constant coefficient remainder tends to zero. -/
private theorem coxPhiTwo_coeff_zero_remainder_cuspFunction_two_tendsto_zero :
    Tendsto
      (cuspFunction (2 : ℝ)
        ((coxPhiFunction (2 : ℕ+)).coeff 0 -
          polynomialInJ modularEquationTwoCoeffY0))
      (nhdsWithin (0 : ℂ) ({0}ᶜ))
      (nhds 0) :=
  coxPhiTwo_coeff_zero_model_tendsto_zero.congr'
    coxPhiTwo_coeff_zero_remainder_cuspFunction_two_eventuallyEq.symm

/-- The constant coefficient remainder vanishes at imaginary infinity. -/
private theorem coxPhiTwo_coeff_zero_remainder_IsZeroAtImInfty :
    IsZeroAtImInfty
      ((coxPhiFunction (2 : ℕ+)).coeff 0 -
        polynomialInJ modularEquationTwoCoeffY0) :=
  coxPhiTwo_coeff_remainder_IsZeroAtImInfty_of_cusp_tendsto_zero
    0 modularEquationTwoCoeffY0 coxPhiTwo_coeff_zero_remainder_cuspFunction_two_tendsto_zero

/-- The constant coefficient identity for the explicit `Φ₂` in the `N = 2` example. -/
theorem coxPhiTwo_coeff_zero_identity :
    -((jN (2 : ℕ+)) *
      (fun z : ℍ => j (halfUpper z)) *
      (fun z : ℍ => j (halfTranslateUpper z))) =
      polynomialInJ modularEquationTwoCoeffY0 := by
  have hcoeff :
      (coxPhiFunction (2 : ℕ+)).coeff 0 = polynomialInJ modularEquationTwoCoeffY0 :=
    coxPhiTwo_coeff_eq_polynomialInJ_of_remainder_zero
      0 modularEquationTwoCoeffY0 coxPhiTwo_coeff_zero_remainder_IsZeroAtImInfty
  rw [← coxPhiFunction_two_coeff_zero]
  exact hcoeff

/-- Reduction of the `N = 2` example to the three explicit symmetric coefficient identities. -/
theorem modularEquationTwo_map_eq_coxPhiFunction_two_of_symmetric_identities
    (h2 :
      -((jN (2 : ℕ+)) +
        (fun z : ℍ => j (halfUpper z)) +
        (fun z : ℍ => j (halfTranslateUpper z))) =
        polynomialInJ modularEquationTwoCoeffY2)
    (h1 :
      (jN (2 : ℕ+)) * (fun z : ℍ => j (halfUpper z)) +
      (jN (2 : ℕ+)) * (fun z : ℍ => j (halfTranslateUpper z)) +
      (fun z : ℍ => j (halfUpper z)) *
        (fun z : ℍ => j (halfTranslateUpper z)) =
        polynomialInJ modularEquationTwoCoeffY1)
    (h0 :
      -((jN (2 : ℕ+)) *
        (fun z : ℍ => j (halfUpper z)) *
        (fun z : ℍ => j (halfTranslateUpper z))) =
        polynomialInJ modularEquationTwoCoeffY0) :
    modularEquationTwo.map polynomialInJRingHom = coxPhiFunction (2 : ℕ+) := by
  apply Polynomial.ext
  intro n
  ext z
  have h2z :
      -(jN (2 : ℕ+) z + j (halfUpper z) + j (halfTranslateUpper z)) =
        -(j z) ^ 2 + 1488 * j z - 162000 := by
    simpa [polynomialInJ, modularEquationTwoCoeffY2] using congrFun h2 z
  have h1z :
      jN (2 : ℕ+) z * j (halfUpper z) +
        jN (2 : ℕ+) z * j (halfTranslateUpper z) +
        j (halfUpper z) * j (halfTranslateUpper z) =
          1488 * (j z) ^ 2 + 40773375 * j z + 8748000000 := by
    simpa [polynomialInJ, modularEquationTwoCoeffY1] using congrFun h1 z
  have h0z :
      -(jN (2 : ℕ+) z * j (halfUpper z) * j (halfTranslateUpper z)) =
        (j z) ^ 3 - 162000 * (j z) ^ 2 +
          8748000000 * j z - 157464000000000 := by
    simpa [polynomialInJ, modularEquationTwoCoeffY0] using congrFun h0 z
  have h2eval :
      modularEquationTwoCoeffY2.eval (j z) =
        -(jN (2 : ℕ+) z + j (halfUpper z) + j (halfTranslateUpper z)) :=
    by simpa [modularEquationTwoCoeffY2] using h2z.symm
  have h1eval :
      modularEquationTwoCoeffY1.eval (j z) =
        jN (2 : ℕ+) z * j (halfUpper z) +
          jN (2 : ℕ+) z * j (halfTranslateUpper z) +
            j (halfUpper z) * j (halfTranslateUpper z) :=
    by simpa [modularEquationTwoCoeffY1] using h1z.symm
  have h0eval :
      modularEquationTwoCoeffY0.eval (j z) =
        -(jN (2 : ℕ+) z * j (halfUpper z) * j (halfTranslateUpper z)) :=
    by simpa [modularEquationTwoCoeffY0] using h0z.symm
  have hpoly :
      (modularEquationTwo.map polynomialInJRingHom).map (evalAtUpper z) =
        (coxPhiFunction (2 : ℕ+)).map (evalAtUpper z) := by
    rw [coxPhiFunction_two_eq_explicit, coxPhiTwoFunctionExplicit_map_eval]
    rw [coxPhiTwoExplicit, Cubic.prod_X_sub_C_eq]
    simp [modularEquationTwo, polynomialInJRingHom, polynomialInJ, evalAtUpper,
      Cubic.toPoly, h2eval, h1eval, h0eval]
  have hcoeff := congrArg (fun P : Polynomial ℂ => P.coeff n) hpoly
  simpa [Polynomial.coeff_map] using hcoeff

/-- The fully formalised `N = 2` example: the classical explicit `Φ₂` maps to
the level-`2` Cox product. -/
theorem modularEquationTwo_map_eq_coxPhiFunction_two :
    modularEquationTwo.map polynomialInJRingHom = coxPhiFunction (2 : ℕ+) :=
  modularEquationTwo_map_eq_coxPhiFunction_two_of_symmetric_identities
    coxPhiTwo_coeff_two_identity
    coxPhiTwo_coeff_one_identity
    coxPhiTwo_coeff_zero_identity

end LevelTwoCoefficientIdentities

/-! ### Final vanishing statements

This section packages the identified polynomial as the explicit relation
`Φ₂(j(τ), j(2τ)) = 0`.
-/

section LevelTwoFinalVanishing

/-- If the explicit `Φ₂` equals the Cox product after mapping coefficients
through `polynomialInJRingHom`, then it vanishes at `(j z, j₂ z)`. -/
theorem modularEquationTwo_eval_j_jN_of_map_eq
    (hmap : modularEquationTwo.map polynomialInJRingHom = coxPhiFunction (2 : ℕ+))
    (z : ℍ) :
    modularEquationTwo.evalEval (j z) (jN (2 : ℕ+) z) = 0 := by
  have hroot := congrFun (coxPhiFunction_eval_jN (2 : ℕ+)) z
  rw [← hmap] at hroot
  rw [polynomialInJRingHom_eval_apply] at hroot
  simpa using hroot

/-- Displayed scalar form of the conditional `N = 2` example vanishing statement. -/
theorem modularEquationTwo_explicit_eval_j_jN_of_map_eq
    (hmap : modularEquationTwo.map polynomialInJRingHom = coxPhiFunction (2 : ℕ+))
    (z : ℍ) :
    (j z) ^ 3 + (jN (2 : ℕ+) z) ^ 3 - (j z) ^ 2 * (jN (2 : ℕ+) z) ^ 2
      + 1488 * (j z) * (jN (2 : ℕ+) z) * (j z + jN (2 : ℕ+) z)
      - 162000 * ((j z) ^ 2 + (jN (2 : ℕ+) z) ^ 2)
      + 40773375 * (j z) * (jN (2 : ℕ+) z)
      + 8748000000 * (j z + jN (2 : ℕ+) z)
      - 157464000000000 = 0 := by
  have hroot := modularEquationTwo_eval_j_jN_of_map_eq hmap z
  rw [modularEquationTwo_evalEval] at hroot
  simpa using hroot

/-- The `N = 2` example, i.e. the classical equation `Φ₂(j(τ), j(2τ)) = 0`,
in bivariate polynomial-evaluation form. -/
theorem modularEquationTwo_eval_j_jN (z : ℍ) :
    modularEquationTwo.evalEval (j z) (jN (2 : ℕ+) z) = 0 :=
  modularEquationTwo_eval_j_jN_of_map_eq modularEquationTwo_map_eq_coxPhiFunction_two z

/-- Displayed scalar form of the `N = 2` example:
`Φ₂(j(τ), j(2τ)) = 0`. -/
theorem modularEquationTwo_explicit_eval_j_jN (z : ℍ) :
    (j z) ^ 3 + (jN (2 : ℕ+) z) ^ 3 - (j z) ^ 2 * (jN (2 : ℕ+) z) ^ 2
      + 1488 * (j z) * (jN (2 : ℕ+) z) * (j z + jN (2 : ℕ+) z)
      - 162000 * ((j z) ^ 2 + (jN (2 : ℕ+) z) ^ 2)
      + 40773375 * (j z) * (jN (2 : ℕ+) z)
      + 8748000000 * (j z + jN (2 : ℕ+) z)
      - 157464000000000 = 0 :=
  modularEquationTwo_explicit_eval_j_jN_of_map_eq
    modularEquationTwo_map_eq_coxPhiFunction_two z

end LevelTwoFinalVanishing

end LevelTwoEquation

end modularEquation
