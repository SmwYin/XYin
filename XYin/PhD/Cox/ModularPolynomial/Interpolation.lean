/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.LinearAlgebra.Lagrange
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
    (hf : CuspData m f) (τ : ℍ) : Polynomial ℂ :=
  ∑ σ : CoxMatrix m,
    Polynomial.C
        (rightCosetTranslate m hf (coxMatrixEquivRightCosets m σ) τ) *
      ∏ σ' ∈ (Finset.univ.erase σ),
        (Polynomial.X - Polynomial.C (j (σ'.act τ)))

open Classical in
private noncomputable def interpolationAtCosetsAux (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) (τ : ℍ) : Polynomial ℂ :=
  ∑ c : Gamma0RightCosets m,
    Polynomial.C (rightCosetTranslate m hf c τ) *
      ∏ d ∈ Finset.univ.erase c,
        (Polynomial.X - Polynomial.C (rightCosetEval m d τ))

private theorem interpolationAt_eq_cosets_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) (τ : ℍ) :
    interpolationAt m hf τ = interpolationAtCosetsAux m hf τ := by
  classical
  rw [interpolationAt, interpolationAtCosetsAux]
  apply Finset.sum_equiv (coxMatrixEquivRightCosets m)
  · simp
  · intro σ _
    congr 1
    apply Finset.prod_equiv (coxMatrixEquivRightCosets m)
    · simp
    · intro σ' _
      rw [rightCosetEval_equiv]

private theorem interpolationAtCosets_smul_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) (δ : SL(2, ℤ)) (τ : ℍ) :
    interpolationAtCosetsAux m hf (δ • τ) = interpolationAtCosetsAux m hf τ := by
  classical
  rw [interpolationAtCosetsAux, interpolationAtCosetsAux]
  apply Finset.sum_equiv (rightCosetMul m δ)
  · simp
  · intro c _
    apply congrArg₂ (· * ·)
    · exact congrArg Polynomial.C (rightCosetTranslate_smul m hf δ c τ)
    · apply Finset.prod_equiv (rightCosetMul m δ)
      · simp
      · intro d _
        rw [rightCosetEval_smul]

private theorem interpolationAt_smul_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) (δ : SL(2, ℤ)) (τ : ℍ) :
    interpolationAt m hf (δ • τ) = interpolationAt m hf τ := by
  rw [interpolationAt_eq_cosets_aux, interpolationAt_eq_cosets_aux,
    interpolationAtCosets_smul_aux]

private theorem rightCosetTranslate_meromorphicOnH_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) (c : Gamma0RightCosets m) :
    ∀ z : ℂ, 0 < z.im →
      MeromorphicAt ((rightCosetTranslate m hf c) ∘ UpperHalfPlane.ofComplex) z :=
  Quotient.inductionOn c (MeromorphicField.meromorphicOn_comp_sl2_smul hf.meromorphicOn)

private noncomputable def interpolationFunctionAux (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) : Polynomial (ℍ → ℂ) :=
  ∑ σ : CoxMatrix m,
    Polynomial.C
        (rightCosetTranslate m hf (coxMatrixEquivRightCosets m σ)) *
      ∏ σ' ∈ Finset.univ.erase σ,
        (Polynomial.X - Polynomial.C (fun τ ↦ j (σ'.act τ)))

private theorem interpolationFunction_map_eval_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) (τ : ℍ) :
    (interpolationFunctionAux m hf).map
        (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ) =
      interpolationAt m hf τ := by
  simp [interpolationFunctionAux, interpolationAt, Polynomial.map_sum,
    Polynomial.map_prod]

/-- The interpolation coefficients, as functions of `τ`. -/
private theorem interpolation_coeff_eq_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) (n : ℕ) :
    (fun τ ↦ (interpolationAt m hf τ).coeff n) =
      ∑ σ : CoxMatrix m,
        rightCosetTranslate m hf (coxMatrixEquivRightCosets m σ) *
          (∏ σ' ∈ Finset.univ.erase σ,
            (Polynomial.X - Polynomial.C (fun τ : ℍ ↦ j (σ'.act τ)))).coeff n := by
  funext τ
  rw [← interpolationFunction_map_eval_aux, Polynomial.coeff_map]
  simp [interpolationFunctionAux]

private theorem interpolation_coeff_meromorphicOnH_aux (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) (n : ℕ) :
    ∀ z : ℂ, 0 < z.im →
      MeromorphicAt
        ((fun τ ↦ (interpolationAt m hf τ).coeff n) ∘
          UpperHalfPlane.ofComplex) z := by
  intro z hz
  rw [interpolation_coeff_eq_aux]
  simp only [Function.comp_def, Finset.sum_apply, Pi.mul_apply]
  exact MeromorphicAt.fun_sum fun σ _ ↦
    (rightCosetTranslate_meromorphicOnH_aux m hf (coxMatrixEquivRightCosets m σ) z hz).mul
      (meromorphicAt_comp_ofComplex_of_mdifferentiable
        (coxNodal_coeff_mdifferentiable m (Finset.univ.erase σ) n) hz)

private theorem interpolation_coeff_widthM_cuspMeromorphicAt_aux (m : ℕ+)
    {f : ℍ → ℂ} (hf : CuspData m f) (n : ℕ) :
    MeromorphicAt
      (cuspFunction ((m : ℕ) : ℝ)
        (fun τ ↦ (interpolationAt m hf τ).coeff n)) 0 := by
  rw [interpolation_coeff_eq_aux]
  exact meromorphicAt_cuspFunction_finset_sum fun σ _ ↦ meromorphicAt_cuspFunction_mul
    (rightCosetTranslate_cuspMeromorphicAt m hf (coxMatrixEquivRightCosets m σ))
    (coxNodal_coeff_cuspMeromorphicAt m (Finset.univ.erase σ) n)

private theorem interpolation_coeff_slashInvariant_aux (m : ℕ+)
    {f : ℍ → ℂ} (hf : CuspData m f) (n : ℕ)
    (δ : SL(2, ℤ)) :
    (fun τ ↦ (interpolationAt m hf τ).coeff n) ∣[(0 : ℤ)] δ =
      fun τ ↦ (interpolationAt m hf τ).coeff n :=
  SL_slash_zero_eq_iff.2 fun τ ↦ congrArg (·.coeff n) (interpolationAt_smul_aux m hf δ τ)

/-- Exercise 11.11: the raw interpolation coefficients have level-one analytic cusp data.
They need not be canonical representatives at removable singularities. -/
theorem interpolation_coeff_cuspData (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) (n : ℕ) :
    LevelOneCuspData (fun τ ↦ (interpolationAt m hf τ).coeff n) :=
  .of_widthM (interpolation_coeff_meromorphicOnH_aux m hf n)
    (interpolation_coeff_slashInvariant_aux m hf n)
    (interpolation_coeff_widthM_cuspMeromorphicAt_aux m hf n)

private theorem eval_interpolation_sum_at
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (a r : ι → R) (i : ι) :
    (∑ k : ι,
        Polynomial.C (a k) *
          ∏ l ∈ Finset.univ.erase k,
            (Polynomial.X - Polynomial.C (r l))).eval (r i) =
      a i * ∏ l ∈ Finset.univ.erase i, (r i - r l) := by
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
  refine Finset.sum_eq_single i ?_ (by simp)
  intro k _ hki
  rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hki.symm, Finset.mem_univ i⟩)
    (sub_self _), mul_zero]

/-- Equation (11.17), stated at points where the separability denominator does not vanish.
This guard is essential: specialized roots can collide at CM points even though the polynomial
is separable over the function field.
-/
theorem recoveryFormula (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) (τ : ℍ)
    (hderiv : ((modularPolynomialC m).map (Polynomial.evalRingHom (j τ))).derivative.eval
      (levelJ m τ) ≠ 0) :
    f τ = (interpolationAt m hf τ).eval (levelJ m τ) /
      ((modularPolynomialC m).map (Polynomial.evalRingHom (j τ))).derivative.eval
        (levelJ m τ) := by
  classical
  rw [← congrFun (j_act_sigmaZero m) τ, modularPolynomialC_map_evalRingHom, coxPhiAtJ_eq_nodal,
    Lagrange.eval_nodal_derivative_eval_node_eq (v := fun σ : CoxMatrix m ↦ j (σ.act τ))
      (Finset.mem_univ (sigmaZero m)), Lagrange.eval_nodal] at hderiv ⊢
  rw [interpolationAt, eval_interpolation_sum_at
    (fun σ : CoxMatrix m ↦ rightCosetTranslate m hf (coxMatrixEquivRightCosets m σ) τ)
    (fun σ : CoxMatrix m ↦ j (σ.act τ)) (sigmaZero m), rightCosetTranslate_sigmaZero]
  exact (mul_div_cancel_right₀ _ hderiv).symm

section Theorem119

open UpperHalfPlaneFunctionField

private theorem interpolationAt_natDegree_lt (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f) (τ : ℍ) :
    (interpolationAt m hf τ).natDegree < Fintype.card (CoxMatrix m) := by
  classical
  rw [interpolationAt]
  have hcard : 0 < Fintype.card (CoxMatrix m) :=
    Fintype.card_pos_iff.mpr ⟨sigmaZero m⟩
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ ?_)
    (Nat.sub_lt hcard zero_lt_one)
  intro σ _
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

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

open Classical in
private def modularDerivativeHolomorphic (m : ℕ+) : HolomorphicFunction :=
  ∏ c ∈ Finset.univ.erase (baseRightCoset m),
    (rightCosetFunction m (baseRightCoset m) - rightCosetFunction m c)

private theorem modularDerivativeHolomorphic_apply (m : ℕ+) (τ : ℍ) :
    (modularDerivativeHolomorphic m).1 τ =
      ((modularPolynomialC m).map (Polynomial.evalRingHom (j τ))).derivative.eval
        (levelJ m τ) := by
  classical
  rw [modularPolynomialC_rightCosetProduct, ← congrFun (rightCosetEval_baseRightCoset m) τ,
    ← Lagrange.nodal_eq, Lagrange.eval_nodal_derivative_eval_node_eq
      (v := fun c ↦ rightCosetEval m c τ) (Finset.mem_univ (baseRightCoset m)),
    Lagrange.eval_nodal]
  simp [modularDerivativeHolomorphic]

open Classical in
private theorem modularDerivativeHolomorphic_ne_zero (m : ℕ+) :
    modularDerivativeHolomorphic m ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ hc ↦ sub_ne_zero.2 fun h ↦
    Finset.ne_of_mem_erase hc (rightCosetFunction_injective m h).symm

private def interpolationDenominator (m : ℕ+) (D : Polynomial ℂ) : ℂ[X][Y] :=
  Polynomial.C D * (modularPolynomialC m).derivative

private theorem interpolationDenominator_eval (m : ℕ+) (D : Polynomial ℂ)
    (τ : ℍ) :
    (interpolationDenominator m D).evalEval (j τ) (levelJ m τ) =
      D.eval (j τ) *
        ((modularPolynomialC m).map (Polynomial.evalRingHom (j τ))).derivative.eval
          (levelJ m τ) := by
  rw [interpolationDenominator, Polynomial.evalEval_mul, Polynomial.evalEval_C,
    Polynomial.derivative_map, Polynomial.map_evalRingHom_eval]

private theorem interpolationDenominator_onCurve_ne_zero (m : ℕ+)
    {D : Polynomial ℂ} (hD : D ≠ 0) :
    (fun τ : ℍ ↦
      (interpolationDenominator m D).evalEval (j τ) (levelJ m τ)) ≠ 0 := by
  have hproduct : evalJ D * modularDerivativeHolomorphic m ≠ 0 :=
    mul_ne_zero ((map_ne_zero_iff _ evalJ_injective).2 hD)
      (modularDerivativeHolomorphic_ne_zero m)
  intro hzero
  refine hproduct (HolomorphicFunction.ext fun τ ↦ ?_)
  change (evalJ D).1 τ * (modularDerivativeHolomorphic m).1 τ = 0
  rw [evalJ_apply, modularDerivativeHolomorphic_apply,
    ← interpolationDenominator_eval]
  exact congrFun hzero τ

private theorem rationalInTwo_of_interpolation_coeff_rational
    (m : ℕ+) {f : ℍ → ℂ}
    (hf : CuspData m f)
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
      ((modularPolynomialC m).map (Polynomial.evalRingHom (j τ))).derivative.eval
          (levelJ m τ) ≠ 0 :=
    right_ne_zero_of_mul hdenom
  rw [recoveryFormula m hf τ hderiv, hP τ hDeval, div_div]

/-- Theorem 11.9(ii): every level-`N` modular function is rational in `j(τ)` and
`j(Nτ)`. The chosen denominator is nonzero as a function along the modular curve, though it
may vanish at individual branch points as expected for a rational representation. -/
theorem theorem_11_9_ii_pointwise (N : ℕ+)
    (f : ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ))) :
    RationalInTwo f j (levelJ N) :=
  rationalInTwo_of_interpolation_coeff_rational N (CuspData.of_modularFunction N f) fun n ↦
    (interpolation_coeff_cuspData N _ n).rationalInJ

end Theorem119

end Cox
