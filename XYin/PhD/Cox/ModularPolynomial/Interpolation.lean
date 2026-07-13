/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.ModularPolynomial.Construction
import XYin.PhD.Cox.UpperHalfPlaneFunctionField

/-!
# Interpolation for modular functions

This file proves Cox's interpolation and recovery formulas and deduces Theorem 11.9(ii).
-/

open Complex Function MatrixGroups ModularForm UpperHalfPlane
open scoped Manifold Polynomial.Bivariate

noncomputable section

namespace Cox

/-- Equation (11.16), Cox's interpolation polynomial at a point of the upper half-plane. -/
noncomputable def interpolationAt (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (τ : ℍ) : Polynomial ℂ :=
  ∑ σ : CoxMatrix m,
    Polynomial.C
        (rightCosetTranslate m hf (coxMatrixEquivRightCosets m σ) τ) *
      ∏ σ' ∈ (Finset.univ.erase σ),
        (Polynomial.X - Polynomial.C (j (σ'.act τ)))

private noncomputable def interpolationAtCosetsAux (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (τ : ℍ) : Polynomial ℂ := by
  classical
  exact ∑ c : Gamma0RightCosets m,
    Polynomial.C (rightCosetTranslate m hf c τ) *
      ∏ d ∈ Finset.univ.erase c,
        (Polynomial.X - Polynomial.C (rightCosetEval m d τ))

private theorem interpolationAt_eq_cosets_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (τ : ℍ) :
    interpolationAt m hf τ = interpolationAtCosetsAux m hf τ := by
  classical
  rw [interpolationAt, interpolationAtCosetsAux]
  let e := coxMatrixEquivRightCosets m
  calc
    ∑ σ : CoxMatrix m,
        Polynomial.C (rightCosetTranslate m hf (e σ) τ) *
          ∏ σ' ∈ Finset.univ.erase σ,
            (Polynomial.X - Polynomial.C (j (σ'.act τ))) =
        ∑ σ : CoxMatrix m,
          (Polynomial.C (rightCosetTranslate m hf (e σ) τ) *
            ∏ c ∈ Finset.univ.erase (e σ),
              (Polynomial.X - Polynomial.C (rightCosetEval m c τ))) := by
      apply Finset.sum_congr rfl
      intro σ _
      congr 1
      apply Finset.prod_equiv e
      · intro σ'
        simp
      · intro σ' _
        rw [rightCosetEval_equiv]
    _ = _ := e.sum_comp fun c ↦
      Polynomial.C (rightCosetTranslate m hf c τ) *
        ∏ d ∈ Finset.univ.erase c,
          (Polynomial.X - Polynomial.C (rightCosetEval m d τ))

private theorem interpolationAtCosets_smul_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (δ : SL(2, ℤ)) (τ : ℍ) :
    interpolationAtCosetsAux m hf (δ • τ) = interpolationAtCosetsAux m hf τ := by
  classical
  rw [interpolationAtCosetsAux, interpolationAtCosetsAux]
  let e := rightCosetMul m δ
  let term : Gamma0RightCosets m → ℍ → Polynomial ℂ := fun c z ↦
    Polynomial.C (rightCosetTranslate m hf c z) *
      ∏ d ∈ Finset.univ.erase c,
        (Polynomial.X - Polynomial.C (rightCosetEval m d z))
  have hterm (c : Gamma0RightCosets m) : term c (δ • τ) = term (e c) τ := by
    dsimp only [term]
    have hprod :
        (∏ d ∈ Finset.univ.erase c,
          (Polynomial.X - Polynomial.C (rightCosetEval m d (δ • τ)))) =
        ∏ d ∈ Finset.univ.erase (e c),
          (Polynomial.X - Polynomial.C (rightCosetEval m d τ)) := by
      apply Finset.prod_equiv e
      · intro d
        simp
      · intro d _
        simpa only [e] using congrArg
          (fun z ↦ Polynomial.X - Polynomial.C z) (rightCosetEval_smul m δ d τ)
    rw [rightCosetTranslate_smul, hprod]
  change (∑ c : Gamma0RightCosets m, term c (δ • τ)) = ∑ c, term c τ
  calc
    ∑ c : Gamma0RightCosets m, term c (δ • τ) = ∑ c, term (e c) τ := by
      apply Finset.sum_congr rfl
      intro c _
      exact hterm c
    _ = _ := e.sum_comp fun c ↦ term c τ

private theorem interpolationAt_smul_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (δ : SL(2, ℤ)) (τ : ℍ) :
    interpolationAt m hf (δ • τ) = interpolationAt m hf τ := by
  rw [interpolationAt_eq_cosets_aux, interpolationAt_eq_cosets_aux,
    interpolationAtCosets_smul_aux]

private theorem rightCosetTranslate_meromorphicOnH_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (c : Gamma0RightCosets m) :
    ∀ z : ℂ, 0 < z.im →
      MeromorphicAt ((rightCosetTranslate m hf c) ∘ UpperHalfPlane.ofComplex) z := by
  refine Quotient.inductionOn c ?_
  intro γ z hz
  let τ : ℍ := ⟨z, hz⟩
  have hact : MDiff (fun w : ℍ ↦ ((γ • w : ℍ) : ℂ)) :=
    UpperHalfPlane.mdifferentiable_coe.comp <|
      UpperHalfPlane.mdifferentiable_smul (g := (γ : GL (Fin 2) ℝ)) (by simp)
  have hinner : AnalyticAt ℂ
      ((fun w : ℍ ↦ ((γ • w : ℍ) : ℂ)) ∘ UpperHalfPlane.ofComplex) z := by
    have hdiff := UpperHalfPlane.mdifferentiable_iff.mp hact
    exact hdiff.analyticAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
  have hmer : MeromorphicAt (f ∘ UpperHalfPlane.ofComplex)
      (((fun w : ℍ ↦ ((γ • w : ℍ) : ℂ)) ∘ UpperHalfPlane.ofComplex) z) := by
    simpa [Function.comp_def, τ, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
      hf.1 (((γ • τ : ℍ) : ℂ)) (γ • τ).im_pos
  simpa [Function.comp_def, τ, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
    hmer.comp_analyticAt hinner

private noncomputable def interpolationFunctionAux (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) : Polynomial (ℍ → ℂ) := by
  classical
  exact ∑ σ : CoxMatrix m,
    Polynomial.C
        (rightCosetTranslate m hf (coxMatrixEquivRightCosets m σ)) *
      ∏ σ' ∈ Finset.univ.erase σ,
        (Polynomial.X - Polynomial.C (fun τ ↦ j (σ'.act τ)))

private theorem interpolationFunction_map_eval_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (τ : ℍ) :
    (interpolationFunctionAux m hf).map
        (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ) =
      interpolationAt m hf τ := by
  classical
  simp [interpolationFunctionAux, interpolationAt, Polynomial.map_sum,
    Polynomial.map_prod]

private theorem interpolationFunction_coeff_apply_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (n : ℕ) (τ : ℍ) :
    (interpolationFunctionAux m hf).coeff n τ =
      (interpolationAt m hf τ).coeff n := by
  simpa using congrArg (fun p : Polynomial ℂ ↦ p.coeff n)
    (interpolationFunction_map_eval_aux m hf τ)

private noncomputable def interpolationRootProductAux (m : ℕ+)
    (σ : CoxMatrix m) : Polynomial (ℍ → ℂ) :=
  ∏ σ' ∈ Finset.univ.erase σ,
    (Polynomial.X - Polynomial.C (fun τ ↦ j (σ'.act τ)))

private theorem interpolationFunction_coeff_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (n : ℕ) :
    (interpolationFunctionAux m hf).coeff n =
      ∑ σ : CoxMatrix m,
        rightCosetTranslate m hf (coxMatrixEquivRightCosets m σ) *
          (interpolationRootProductAux m σ).coeff n := by
  classical
  simp [interpolationFunctionAux, interpolationRootProductAux]

private theorem coxRoot_mdifferentiable_aux (m : ℕ+)
    (σ : CoxMatrix m) : MDiff (fun τ : ℍ ↦ j (σ.act τ)) := by
  rw [← funext (rightCosetEval_equiv m σ)]
  exact (UpperHalfPlaneFunctionField.rightCosetFunction m
    (coxMatrixEquivRightCosets m σ)).property

private theorem coxLinearFactor_coeff_mdifferentiable_aux (m : ℕ+)
    (σ : CoxMatrix m) (n : ℕ) :
    MDiff ((Polynomial.X - Polynomial.C (fun τ : ℍ ↦ j (σ.act τ)) :
      Polynomial (ℍ → ℂ)).coeff n) := by
  cases n with
  | zero => simpa using (coxRoot_mdifferentiable_aux m σ).neg
  | succ n =>
      cases n with
      | zero => simpa using (mdifferentiable_const : MDiff (fun _ : ℍ ↦ (1 : ℂ)))
      | succ n =>
          simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Nat.right_eq_add,
            Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
            Polynomial.coeff_C_succ, sub_zero]
          exact mdifferentiable_const

private theorem polynomial_prod_coeff_mdifferentiable_aux {ι : Type*}
    (P : ι → Polynomial (ℍ → ℂ)) :
    ∀ s : Finset ι,
      (∀ i ∈ s, ∀ n, MDiff ((P i).coeff n)) →
      ∀ n, MDiff ((s.prod P).coeff n) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ n
      by_cases hn : n = 0
      · subst n
        simpa [Polynomial.coeff_one] using
          (mdifferentiable_const : MDiff (fun _ : ℍ ↦ (1 : ℂ)))
      · simpa [Polynomial.coeff_one, hn] using
          (mdifferentiable_const : MDiff (fun _ : ℍ ↦ (0 : ℂ)))
  | insert a s ha ih =>
      intro hP n
      rw [Finset.prod_insert ha, Polynomial.coeff_mul]
      exact MDifferentiable.sum fun x _ ↦
        (hP a (Finset.mem_insert_self a s) x.1).mul
          (ih (fun i hi k ↦ hP i (Finset.mem_insert_of_mem hi) k) x.2)

private theorem interpolationRootProduct_coeff_mdifferentiable_aux (m : ℕ+)
    (σ : CoxMatrix m) (n : ℕ) :
    MDiff ((interpolationRootProductAux m σ).coeff n) := by
  classical
  rw [interpolationRootProductAux]
  exact polynomial_prod_coeff_mdifferentiable_aux
    (fun σ' : CoxMatrix m ↦
      Polynomial.X - Polynomial.C (fun τ : ℍ ↦ j (σ'.act τ)))
    (Finset.univ.erase σ)
    (fun σ' _ k ↦ coxLinearFactor_coeff_mdifferentiable_aux m σ' k) n

private theorem interpolation_coeff_eq_function_coeff_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (n : ℕ) :
    (fun τ ↦ (interpolationAt m hf τ).coeff n) =
      (interpolationFunctionAux m hf).coeff n := by
  funext τ
  exact (interpolationFunction_coeff_apply_aux m hf n τ).symm

private theorem interpolation_coeff_meromorphicOnH_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (n : ℕ) :
    ∀ z : ℂ, 0 < z.im →
      MeromorphicAt
        ((fun τ ↦ (interpolationAt m hf τ).coeff n) ∘
          UpperHalfPlane.ofComplex) z := by
  intro z hz
  rw [interpolation_coeff_eq_function_coeff_aux,
    interpolationFunction_coeff_aux]
  have hsum : MeromorphicAt
      (fun w ↦ ∑ σ : CoxMatrix m,
        (rightCosetTranslate m hf (coxMatrixEquivRightCosets m σ) ∘
            UpperHalfPlane.ofComplex) w *
          (((interpolationRootProductAux m σ).coeff n) ∘
            UpperHalfPlane.ofComplex) w) z := by
    apply MeromorphicAt.fun_sum
    intro σ _
    have hweight := rightCosetTranslate_meromorphicOnH_aux m hf
      (coxMatrixEquivRightCosets m σ) z hz
    have hdiff := UpperHalfPlane.mdifferentiable_iff.mp
      (interpolationRootProduct_coeff_mdifferentiable_aux m σ n)
    have hroot : MeromorphicAt
        (((interpolationRootProductAux m σ).coeff n) ∘
          UpperHalfPlane.ofComplex) z :=
      (hdiff.analyticAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)).meromorphicAt
    exact hweight.mul hroot
  convert hsum using 1
  funext w
  simp

private theorem rightCosetTranslate_cuspMeromorphicAt_aux (m : ℕ+)
    {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f)
    (c : Gamma0RightCosets m) :
    MeromorphicAt
      (cuspFunction ((m : ℕ) : ℝ) (rightCosetTranslate m hf c)) 0 := by
  refine Quotient.inductionOn c ?_
  intro γ
  change MeromorphicAt
    (cuspFunction ((m : ℕ) : ℝ) (fun τ : ℍ ↦ f (γ • τ))) 0
  exact hf.2.2 γ

private theorem interpolationRootProduct_coeff_cuspMeromorphicAt_aux (m : ℕ+)
    (σ : CoxMatrix m) (n : ℕ) :
    MeromorphicAt
      (cuspFunction ((m : ℕ) : ℝ)
        ((interpolationRootProductAux m σ).coeff n)) 0 := by
  classical
  rw [interpolationRootProductAux]
  exact polynomial_prod_coeff_cuspMeromorphicAt ((m : ℕ) : ℝ)
    (fun σ' : CoxMatrix m ↦
      Polynomial.X - Polynomial.C (fun τ : ℍ ↦ j (σ'.act τ)))
    (Finset.univ.erase σ)
    (fun σ' _ k ↦ coxLinearFactor_coeff_cuspMeromorphicAt m σ' k) n

private theorem interpolation_coeff_widthM_cuspMeromorphicAt_aux (m : ℕ+)
    {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (n : ℕ) :
    MeromorphicAt
      (cuspFunction ((m : ℕ) : ℝ)
        (fun τ ↦ (interpolationAt m hf τ).coeff n)) 0 := by
  rw [interpolation_coeff_eq_function_coeff_aux,
    interpolationFunction_coeff_aux]
  simpa using meromorphicAt_cuspFunction_finset_sum
    (s := (Finset.univ : Finset (CoxMatrix m)))
    (f := fun σ ↦
      rightCosetTranslate m hf (coxMatrixEquivRightCosets m σ) *
        (interpolationRootProductAux m σ).coeff n)
    (fun σ _ ↦ meromorphicAt_cuspFunction_mul
      (rightCosetTranslate_cuspMeromorphicAt_aux m hf
        (coxMatrixEquivRightCosets m σ))
      (interpolationRootProduct_coeff_cuspMeromorphicAt_aux m σ n))

private theorem interpolation_coeff_slashInvariant_aux (m : ℕ+)
    {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (n : ℕ)
    (δ : SL(2, ℤ)) :
    (fun τ ↦ (interpolationAt m hf τ).coeff n) ∣[(0 : ℤ)] δ =
      fun τ ↦ (interpolationAt m hf τ).coeff n := by
  funext τ
  simp only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
  exact congrArg (fun P : Polynomial ℂ ↦ P.coeff n)
    (interpolationAt_smul_aux m hf δ τ)

private theorem interpolation_coeff_widthOne_cuspMeromorphicAt_aux (m : ℕ+)
    {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (n : ℕ) :
    MeromorphicAt
      (cuspFunction 1 (fun τ ↦ (interpolationAt m hf τ).coeff n)) 0 := by
  apply meromorphicAt_cuspFunction_of_nat_mul (m := (m : ℕ)) (h := 1)
    (PNat.ne_zero m)
  · simpa using interpolation_coeff_widthM_cuspMeromorphicAt_aux m hf n
  · exact periodic_comp_of_slashInvariant_one
      (interpolation_coeff_slashInvariant_aux m hf n)

/-- Exercise 11.11: every coefficient of the interpolation polynomial is a level-one modular
function of `τ`. -/
theorem interpolation_coeff_isLevelOne (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (n : ℕ) :
    IsLevelOneModularFunction (fun τ ↦ (interpolationAt m hf τ).coeff n) := by
  let g := fun τ ↦ (interpolationAt m hf τ).coeff n
  have hslash := interpolation_coeff_slashInvariant_aux m hf n
  refine ⟨interpolation_coeff_meromorphicOnH_aux m hf n, ?_, ?_⟩
  · intro γ
    exact hslash γ
  · intro γ
    have hfun : (fun τ : ℍ ↦ g (γ • τ)) = g := by
      funext τ
      have h := congrFun (hslash γ) τ
      simpa only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one, g] using h
    rw [show (fun τ : ℍ ↦
      (interpolationAt m hf (γ • τ)).coeff n) = g from hfun]
    simpa [g] using interpolation_coeff_widthOne_cuspMeromorphicAt_aux m hf n

private theorem eval_derivative_prod_X_sub_C_at
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (r : ι → R) (i : ι) :
    (Polynomial.derivative
        (∏ k : ι, (Polynomial.X - Polynomial.C (r k)))).eval (r i) =
      ∏ k ∈ Finset.univ.erase i, (r i - r k) := by
  rw [Polynomial.derivative_prod_finset,
    Polynomial.eval_finsetSum Finset.univ]
  have hsum :
      (∑ k : ι,
        ((∏ l ∈ Finset.univ.erase k,
            (Polynomial.X - Polynomial.C (r l))) *
          Polynomial.derivative
            (Polynomial.X - Polynomial.C (r k))).eval (r i)) =
        ((∏ l ∈ Finset.univ.erase i,
            (Polynomial.X - Polynomial.C (r l))) *
          Polynomial.derivative
            (Polynomial.X - Polynomial.C (r i))).eval (r i) := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro k hk hki
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      apply mul_eq_zero_of_left
      apply Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨hki.symm, Finset.mem_univ i⟩)
      simp
    · simp
  rw [hsum, Polynomial.eval_mul, Polynomial.eval_prod]
  simp

private theorem eval_interpolation_sum_at
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (a r : ι → R) (i : ι) :
    (∑ k : ι,
        Polynomial.C (a k) *
          ∏ l ∈ Finset.univ.erase k,
            (Polynomial.X - Polynomial.C (r l))).eval (r i) =
      a i * ∏ l ∈ Finset.univ.erase i, (r i - r l) := by
  rw [Polynomial.eval_finsetSum Finset.univ]
  have hsum :
      (∑ k : ι,
        (Polynomial.C (a k) *
          ∏ l ∈ Finset.univ.erase k,
            (Polynomial.X - Polynomial.C (r l))).eval (r i)) =
        (Polynomial.C (a i) *
          ∏ l ∈ Finset.univ.erase i,
            (Polynomial.X - Polynomial.C (r l))).eval (r i) := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro k hk hki
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨hki.symm, Finset.mem_univ i⟩)
      simp
    · simp
  rw [hsum, Polynomial.eval_mul, Polynomial.eval_prod]
  simp

/-- Equation (11.17), stated at points where the separability denominator does not vanish.
This guard is essential: specialized roots can collide at CM points even though the polynomial
is separable over the function field.
-/
theorem recoveryFormula (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (τ : ℍ)
    (hderiv : ((modularPolynomialC m).specializeY (j τ)).derivative.eval
      (levelJ m τ) ≠ 0) :
    f τ = (interpolationAt m hf τ).eval (levelJ m τ) /
      ((modularPolynomialC m).specializeY (j τ)).derivative.eval (levelJ m τ) := by
  classical
  have hsigma : j ((sigmaZero m).act τ) = levelJ m τ :=
    congrFun (j_act_sigmaZero m) τ
  have hden :
      (coxPhiAtJ m τ).derivative.eval (j ((sigmaZero m).act τ)) =
        ∏ σ ∈ Finset.univ.erase (sigmaZero m),
          (j ((sigmaZero m).act τ) - j (σ.act τ)) := by
    simpa [coxPhiAtJ] using
      (eval_derivative_prod_X_sub_C_at
        (fun σ : CoxMatrix m ↦ j (σ.act τ)) (sigmaZero m))
  have hnum :
      (interpolationAt m hf τ).eval (j ((sigmaZero m).act τ)) =
        rightCosetTranslate m hf
            (coxMatrixEquivRightCosets m (sigmaZero m)) τ *
          ∏ σ ∈ Finset.univ.erase (sigmaZero m),
            (j ((sigmaZero m).act τ) - j (σ.act τ)) := by
    simpa [interpolationAt] using
      (eval_interpolation_sum_at
        (fun σ : CoxMatrix m ↦
          rightCosetTranslate m hf (coxMatrixEquivRightCosets m σ) τ)
        (fun σ : CoxMatrix m ↦ j (σ.act τ)) (sigmaZero m))
  rw [← hsigma] at hderiv ⊢
  rw [modularPolynomialC_specializeY] at hderiv ⊢
  have hprod :
      (∏ σ ∈ Finset.univ.erase (sigmaZero m),
        (j ((sigmaZero m).act τ) - j (σ.act τ))) ≠ 0 := by
    rwa [hden] at hderiv
  rw [hnum, rightCosetTranslate_sigmaZero, hden]
  exact (mul_div_cancel_right₀ _ hprod).symm

section Theorem119

open UpperHalfPlaneFunctionField

private theorem interpolationAt_natDegree_lt (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (τ : ℍ) :
    (interpolationAt m hf τ).natDegree < Fintype.card (CoxMatrix m) := by
  classical
  rw [interpolationAt]
  have hcard : 0 < Fintype.card (CoxMatrix m) :=
    Fintype.card_pos_iff.mpr ⟨sigmaZero m⟩
  have hdegree :
      (∑ σ : CoxMatrix m,
        Polynomial.C
            (rightCosetTranslate m hf
              (coxMatrixEquivRightCosets m σ) τ) *
          ∏ σ' ∈ Finset.univ.erase σ,
            (Polynomial.X - Polynomial.C (j (σ'.act τ)))).natDegree ≤
        Fintype.card (CoxMatrix m) - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
      (n := Fintype.card (CoxMatrix m) - 1) Finset.univ
    intro σ _
    apply Polynomial.natDegree_mul_le.trans
    rw [Polynomial.natDegree_C, zero_add]
    apply (Polynomial.natDegree_prod_le _ _).trans
    have hsum :
        (∑ σ' ∈ Finset.univ.erase σ,
            (Polynomial.X - Polynomial.C (j (σ'.act τ))).natDegree) =
          Fintype.card (CoxMatrix m) - 1 := by
      calc
        (∑ σ' ∈ Finset.univ.erase σ,
            (Polynomial.X - Polynomial.C (j (σ'.act τ))).natDegree) =
            (Finset.univ.erase σ).card := by
              simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const,
                smul_eq_mul, mul_one]
        _ = Fintype.card (CoxMatrix m) - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ σ), Finset.card_univ]
    exact hsum.le
  exact lt_of_le_of_lt hdegree (by omega)

private theorem exists_commonDenominator_polynomialEval_of_natDegree_lt
    {A : ℍ → Polynomial ℂ} {g h : ℍ → ℂ} (d : ℕ)
    (hdegree : ∀ τ, (A τ).natDegree < d)
    (hcoeff : ∀ n, RationalIn (fun τ ↦ (A τ).coeff n) g) :
    ∃ numerator : ℂ[X][Y], ∃ commonDenom : Polynomial ℂ,
      commonDenom ≠ 0 ∧
        ∀ τ, commonDenom.eval (g τ) ≠ 0 →
          (A τ).eval (h τ) =
            numerator.evalEval (g τ) (h τ) / commonDenom.eval (g τ) := by
  classical
  choose p q hq hrepr using hcoeff
  let s := Finset.range d
  let commonDenom : Polynomial ℂ := ∏ n ∈ s, q n
  let numerator : ℂ[X][Y] :=
    ∑ n ∈ s,
      Polynomial.C (p n * ∏ k ∈ s.erase n, q k) * Polynomial.X ^ n
  refine ⟨numerator, commonDenom, ?_, ?_⟩
  · simp only [commonDenom]
    exact Finset.prod_ne_zero_iff.mpr fun n _ ↦ hq n
  · intro τ hdenom
    have hcommon_eval :
        commonDenom.eval (g τ) = ∏ n ∈ s, (q n).eval (g τ) := by
      simp only [commonDenom, Polynomial.eval_prod]
    have hqeval {n : ℕ} (hn : n ∈ s) : (q n).eval (g τ) ≠ 0 := by
      intro hnzero
      apply hdenom
      rw [hcommon_eval]
      exact Finset.prod_eq_zero hn hnzero
    rw [eq_div_iff hdenom]
    rw [Polynomial.eval_eq_sum_range' (hdegree τ)]
    change
      (∑ n ∈ s, (A τ).coeff n * h τ ^ n) * commonDenom.eval (g τ) =
        numerator.evalEval (g τ) (h τ)
    rw [Finset.sum_mul]
    simp only [numerator, Polynomial.evalEval_finsetSum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Polynomial.evalEval_mul, Polynomial.evalEval_C,
      Polynomial.evalEval_pow, Polynomial.evalEval_X,
      Polynomial.eval_mul, Polynomial.eval_prod]
    have hcoeffτ := hrepr n τ (hqeval hn)
    change (A τ).coeff n = (p n).eval (g τ) / (q n).eval (g τ) at hcoeffτ
    rw [hcoeffτ, Polynomial.eval_prod]
    rw [← Finset.mul_prod_erase s (fun k ↦ (q k).eval (g τ)) hn]
    field_simp [hqeval hn]

private theorem modularPolynomialC_derivative_evalEval (m : ℕ+) (τ : ℍ) :
    ((modularPolynomialC m).derivative).evalEval (j τ) (levelJ m τ) =
      ((modularPolynomialC m).specializeY (j τ)).derivative.eval
        (levelJ m τ) := by
  rw [BivariatePolynomial.specializeY, Polynomial.derivative_map,
    Polynomial.map_evalRingHom_eval]

private def modularDerivativeHolomorphic (m : ℕ+) : HolomorphicFunction := by
  classical
  exact ∏ c ∈ Finset.univ.erase (baseRightCoset m),
    (rightCosetFunction m (baseRightCoset m) - rightCosetFunction m c)

private theorem modularDerivativeHolomorphic_apply (m : ℕ+) (τ : ℍ) :
    (modularDerivativeHolomorphic m).1 τ =
      ((modularPolynomialC m).specializeY (j τ)).derivative.eval
        (levelJ m τ) := by
  classical
  let b := baseRightCoset m
  have hpoly := congrArg Polynomial.derivative
    (modularPolynomialC_rightCosetProduct m τ)
  have happly :
      (modularDerivativeHolomorphic m).1 τ =
        ∏ c ∈ Finset.univ.erase b,
          (rightCosetEval m b τ - rightCosetEval m c τ) := by
    simp [modularDerivativeHolomorphic, b, rightCosetFunction]
  have hbase : rightCosetEval m b τ = levelJ m τ := by
    simp [b, baseRightCoset]
  have hderiv :
      ((modularPolynomialC m).specializeY (j τ)).derivative.eval
          (levelJ m τ) =
        ∏ c ∈ Finset.univ.erase b,
          (rightCosetEval m b τ - rightCosetEval m c τ) := by
    rw [hpoly, ← hbase]
    rw [← Finset.mul_prod_erase
      (Finset.univ : Finset (Gamma0RightCosets m))
      (fun c ↦ Polynomial.X - Polynomial.C (rightCosetEval m c τ))
      (Finset.mem_univ b)]
    simp [Polynomial.derivative_mul, Polynomial.eval_prod]
  exact happly.trans hderiv.symm

private theorem modularDerivativeHolomorphic_ne_zero (m : ℕ+) :
    modularDerivativeHolomorphic m ≠ 0 := by
  classical
  dsimp only [modularDerivativeHolomorphic]
  apply Finset.prod_ne_zero_iff.mpr
  intro c hc
  apply sub_ne_zero.mpr
  intro hbc
  have hcb : c ≠ baseRightCoset m := (Finset.mem_erase.mp hc).1
  exact hcb ((rightCosetFunction_injective m hbc).symm)

private def interpolationDenominator (m : ℕ+) (D : Polynomial ℂ) : ℂ[X][Y] :=
  Polynomial.C D * (modularPolynomialC m).derivative

private theorem interpolationDenominator_eval (m : ℕ+) (D : Polynomial ℂ)
    (τ : ℍ) :
    (interpolationDenominator m D).evalEval (j τ) (levelJ m τ) =
      D.eval (j τ) *
        ((modularPolynomialC m).specializeY (j τ)).derivative.eval
          (levelJ m τ) := by
  rw [interpolationDenominator, Polynomial.evalEval_mul,
    Polynomial.evalEval_C, modularPolynomialC_derivative_evalEval]

private theorem interpolationDenominator_onCurve_ne_zero (m : ℕ+)
    {D : Polynomial ℂ} (hD : D ≠ 0) :
    (fun τ : ℍ ↦
      (interpolationDenominator m D).evalEval (j τ) (levelJ m τ)) ≠ 0 := by
  have hEvalJ : evalJ D ≠ 0 := by
    intro hzero
    apply hD
    apply evalJ_injective
    simpa using hzero
  have hproduct :
      evalJ D * modularDerivativeHolomorphic m ≠ 0 :=
    mul_ne_zero hEvalJ (modularDerivativeHolomorphic_ne_zero m)
  intro hzero
  apply hproduct
  apply Subtype.ext
  funext τ
  change (evalJ D).1 τ * (modularDerivativeHolomorphic m).1 τ = 0
  rw [evalJ_apply, modularDerivativeHolomorphic_apply,
    ← interpolationDenominator_eval]
  exact congrFun hzero τ

private theorem rationalInTwo_of_interpolation_coeff_rational
    (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f)
    (hcoeff : ∀ n,
      RationalIn (fun τ ↦ (interpolationAt m hf τ).coeff n) j) :
    RationalInTwo f j (levelJ m) := by
  obtain ⟨P, D, hD, hP⟩ :=
    exists_commonDenominator_polynomialEval_of_natDegree_lt
      (Fintype.card (CoxMatrix m))
      (interpolationAt_natDegree_lt m hf) hcoeff
  refine ⟨P, interpolationDenominator m D,
    interpolationDenominator_onCurve_ne_zero m hD, ?_⟩
  intro τ hdenom
  rw [interpolationDenominator_eval] at hdenom ⊢
  have hDeval : D.eval (j τ) ≠ 0 := left_ne_zero_of_mul hdenom
  have hderiv :
      ((modularPolynomialC m).specializeY (j τ)).derivative.eval
          (levelJ m τ) ≠ 0 :=
    right_ne_zero_of_mul hdenom
  calc
    f τ = (interpolationAt m hf τ).eval (levelJ m τ) /
        ((modularPolynomialC m).specializeY (j τ)).derivative.eval
          (levelJ m τ) := recoveryFormula m hf τ hderiv
    _ = (P.evalEval (j τ) (levelJ m τ) / D.eval (j τ)) /
        ((modularPolynomialC m).specializeY (j τ)).derivative.eval
          (levelJ m τ) := by rw [hP τ hDeval]
    _ = P.evalEval (j τ) (levelJ m τ) /
        (D.eval (j τ) *
          ((modularPolynomialC m).specializeY (j τ)).derivative.eval
            (levelJ m τ)) := div_div _ _ _

/-- Theorem 11.9(ii): every level-`N` modular function is rational in `j(τ)` and
`j(Nτ)`. The chosen denominator is nonzero as a function along the modular curve, though it
may vanish at individual branch points as expected for a rational representation. -/
theorem theorem_11_9_ii (N : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction N f) :
    RationalInTwo f j (levelJ N) := by
  apply rationalInTwo_of_interpolation_coeff_rational N hf
  intro n
  exact theorem_11_9_i (interpolation_coeff_isLevelOne N hf n)

end Theorem119

end Cox
