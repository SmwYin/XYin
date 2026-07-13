/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.FormalCoxProduct
import XYin.PhD.Cox.ModularPolynomial.AnalyticSupport

/-!
# Construction of Cox's modular polynomial

This file develops the bivariate-polynomial API, the function-valued Cox product, and the
canonical complex modular polynomial characterized by its specializations at `Y = j(τ)`.
-/

open Complex Function MatrixGroups ModularForm UpperHalfPlane
open scoped Manifold Polynomial.Bivariate

noncomputable section

namespace Cox

/-- Bivariate polynomials with the outer variable interpreted as Cox's `X` and the inner
variable as Cox's `Y`. -/
abbrev BivariatePolynomial (R : Type*) [Semiring R] := Polynomial (Polynomial R)

namespace BivariatePolynomial

variable {R S : Type*}

/-- Cox's first/root variable (the outer polynomial variable). -/
def varX [Semiring R] : BivariatePolynomial R := Polynomial.X

/-- Cox's second/parameter variable (the inner coefficient variable). -/
def varY [Semiring R] : BivariatePolynomial R := Polynomial.C Polynomial.X

/-- Evaluate with the semantic argument order `(x,y)`, compensating for mathlib's inner-first
`Polynomial.evalEval` convention. -/
def eval [Semiring R] (Φ : BivariatePolynomial R) (x y : R) : R :=
  Φ.evalEval y x

/-- Substitute a value for the parameter variable `Y`, leaving a polynomial in `X`. -/
def specializeY [CommSemiring R] (y : R) (Φ : BivariatePolynomial R) : Polynomial R :=
  Polynomial.map (Polynomial.evalRingHom y) Φ

/-- Coefficientwise map of a bivariate polynomial. -/
def map [Semiring R] [Semiring S] (f : R →+* S) (Φ : BivariatePolynomial R) :
    BivariatePolynomial S :=
  Polynomial.map (Polynomial.mapRingHom f) Φ

/-- Diagonal specialization `Φ(X,X)`. -/
def diagonal [CommSemiring R] (Φ : BivariatePolynomial R) : Polynomial R :=
  Polynomial.eval Polynomial.X Φ

end BivariatePolynomial

/-- Equation (11.15) after specializing `Y=j(τ)`. -/
noncomputable def coxPhiAtJ (m : ℕ+) (τ : ℍ) : Polynomial ℂ :=
  ∏ σ : CoxMatrix m, (Polynomial.X - Polynomial.C (j (σ.act τ)))

/-- The same Cox product before evaluating `τ`, with function-valued coefficients. -/
noncomputable def coxPhiFunction (m : ℕ+) : Polynomial (ℍ → ℂ) :=
  ∏ σ : CoxMatrix m,
    (Polynomial.X - Polynomial.C (fun τ ↦ j (σ.act τ)))

namespace BivariatePolynomial

/-- Evaluating after specialization in `Y` agrees with bivariate evaluation. -/
theorem specializeY_eval {R : Type*} [CommSemiring R] (Φ : BivariatePolynomial R)
    (x y : R) : (specializeY y Φ).eval x = eval Φ x y :=
  Polynomial.map_evalRingHom_eval y x Φ

/-- Bivariate polynomials are determined by all specializations of their inner variable. -/
theorem specializeY_ext {R : Type*} [CommRing R] [IsDomain R] [Infinite R]
    {Φ Ψ : BivariatePolynomial R}
    (h : ∀ y : R, Φ.specializeY y = Ψ.specializeY y) : Φ = Ψ := by
  apply Polynomial.ext
  intro n
  apply Polynomial.funext
  intro y
  have hy := congrArg (fun p : Polynomial R ↦ p.coeff n) (h y)
  simpa [specializeY, Polynomial.coeff_map] using hy

end BivariatePolynomial

/-- Swapping the variables exchanges the two semantic evaluation arguments. -/
theorem BivariatePolynomial.eval_swap {R : Type*} [CommSemiring R]
    (Φ : BivariatePolynomial R) (x y : R) :
    BivariatePolynomial.eval (Polynomial.Bivariate.swap Φ) x y =
      BivariatePolynomial.eval Φ y x := by
  change Polynomial.evalEval y x (Polynomial.Bivariate.swap Φ) =
    Polynomial.evalEval x y Φ
  rw [← congrFun (Polynomial.coe_aevalAeval_eq_evalEval y x) _,
    ← congrFun (Polynomial.coe_aevalAeval_eq_evalEval x y) _]
  exact Polynomial.Bivariate.aevalAeval_swap y x Φ

/-- The coefficient at `(i,j)` after swapping variables is the original coefficient at
`(j,i)`. -/
theorem BivariatePolynomial.coeff_coeff_swap {R : Type*} [CommSemiring R]
    (Φ : BivariatePolynomial R) (i j : ℕ) :
    ((Polynomial.Bivariate.swap Φ).coeff i).coeff j = (Φ.coeff j).coeff i := by
  induction Φ using Polynomial.induction_on' with
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | monomial n P =>
      rw [Polynomial.Bivariate.swap_monomial, Polynomial.coeff_mul_C,
        Polynomial.coeff_map]
      by_cases h : j = n <;> simp [Polynomial.coeff_monomial, h, eq_comm]

/-- Swapping variables commutes with a coefficientwise ring homomorphism. -/
theorem BivariatePolynomial.map_swap {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (Φ : BivariatePolynomial R) :
    BivariatePolynomial.map f (Polynomial.Bivariate.swap Φ) =
      Polynomial.Bivariate.swap (BivariatePolynomial.map f Φ) := by
  induction Φ using Polynomial.induction_on' with
  | add P Q hP hQ =>
      unfold BivariatePolynomial.map at hP hQ ⊢
      simp only [map_add, Polynomial.map_add] at ⊢
      rw [hP, hQ]
  | monomial n P =>
      rw [Polynomial.Bivariate.swap_monomial]
      simp only [BivariatePolynomial.map, Polynomial.map_mul, Polynomial.map_map,
        Polynomial.map_C,
        Polynomial.map_monomial, Polynomial.Bivariate.swap_monomial]
      have hmap :
          Polynomial.map ((Polynomial.mapRingHom f).comp Polynomial.C) P =
            Polynomial.map Polynomial.C ((Polynomial.mapRingHom f) P) := by
        ext k
        simp [Polynomial.coeff_map]
      have hpow : (Polynomial.mapRingHom f) (Polynomial.X ^ n) =
          Polynomial.X ^ n := by
        simp
      rw [hmap, hpow]

/-- Evaluating the diagonal specialization at `x` is bivariate evaluation at `(x,x)`. -/
theorem BivariatePolynomial.diagonal_eval {R : Type*} [CommSemiring R]
    (Φ : BivariatePolynomial R) (x : R) :
    (BivariatePolynomial.diagonal Φ).eval x = BivariatePolynomial.eval Φ x x := by
  rw [BivariatePolynomial.diagonal, BivariatePolynomial.eval]
  rw [← congrFun (congrFun (Polynomial.eval₂_evalRingHom x) x) Φ]
  simpa using
    (Polynomial.hom_eval₂ Φ (RingHom.id (Polynomial R))
      (Polynomial.evalRingHom x) Polynomial.X)

/-- Coefficientwise maps commute with diagonal specialization. -/
theorem BivariatePolynomial.diagonal_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (Φ : BivariatePolynomial R) :
    BivariatePolynomial.diagonal (BivariatePolynomial.map f Φ) =
      (BivariatePolynomial.diagonal Φ).map f := by
  simpa only [BivariatePolynomial.diagonal, BivariatePolynomial.map, Polynomial.map_X] using
    Polynomial.map_mapRingHom_eval_map f Φ Polynomial.X

/-- Evaluating a diagonal after changing coefficients is simultaneous evaluation in both
variables. -/
theorem BivariatePolynomial.diagonal_eval₂ {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x : S) (Φ : BivariatePolynomial R) :
    (BivariatePolynomial.diagonal Φ).eval₂ f x =
      Φ.eval₂ (Polynomial.eval₂RingHom f x) x := by
  simpa [BivariatePolynomial.diagonal] using
    Polynomial.hom_eval₂ Φ (RingHom.id (Polynomial R))
      (Polynomial.eval₂RingHom f x) Polynomial.X

/-- The diagonal specialization is unchanged by swapping the two variables. -/
@[simp]
theorem BivariatePolynomial.diagonal_swap {R : Type*} [CommSemiring R]
    (Φ : BivariatePolynomial R) :
    BivariatePolynomial.diagonal (Polynomial.Bivariate.swap Φ) =
      BivariatePolynomial.diagonal Φ := by
  induction Φ using Polynomial.induction_on' with
  | add P Q hP hQ =>
      change Polynomial.eval Polynomial.X (Polynomial.Bivariate.swap P) =
        Polynomial.eval Polynomial.X P at hP
      change Polynomial.eval Polynomial.X (Polynomial.Bivariate.swap Q) =
        Polynomial.eval Polynomial.X Q at hQ
      change Polynomial.eval Polynomial.X (Polynomial.Bivariate.swap (P + Q)) =
        Polynomial.eval Polynomial.X (P + Q)
      rw [map_add, Polynomial.eval_add, Polynomial.eval_add, hP, hQ]
  | monomial n P =>
      rw [Polynomial.Bivariate.swap_monomial]
      simp only [diagonal, Polynomial.eval_mul, Polynomial.eval_map,
        Polynomial.eval₂_C_X, Polynomial.eval_C, Polynomial.eval_monomial]

/-- The specialized Cox product is monic in its root variable. -/
theorem coxPhiAtJ_monic (m : ℕ+) (τ : ℍ) : (coxPhiAtJ m τ).Monic := by
  classical
  simpa [coxPhiAtJ] using Polynomial.monic_prod_X_sub_C
    (fun σ : CoxMatrix m ↦ j (σ.act τ)) Finset.univ

/-- The degree of the specialized Cox product is the cardinality of `C(m)`. -/
theorem coxPhiAtJ_natDegree (m : ℕ+) (τ : ℍ) :
    (coxPhiAtJ m τ).natDegree = Fintype.card (CoxMatrix m) := by
  classical
  simp [coxPhiAtJ]

/-- Pointwise evaluation of the function-valued Cox product gives the specialized product. -/
theorem coxPhiFunction_map_eval (m : ℕ+) (τ : ℍ) :
    (coxPhiFunction m).map (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ) = coxPhiAtJ m τ := by
  classical
  simp [coxPhiFunction, coxPhiAtJ, Polynomial.map_prod]

/-- Pointwise evaluation of a Cox-product coefficient gives the corresponding specialized
coefficient. -/
theorem coxPhiFunction_coeff_apply (m : ℕ+) (n : ℕ) (τ : ℍ) :
    (coxPhiFunction m).coeff n τ = (coxPhiAtJ m τ).coeff n := by
  simpa using congrArg (fun p : Polynomial ℂ ↦ p.coeff n) (coxPhiFunction_map_eval m τ)

/-- Equation (11.15) reindexed by the right cosets of `Γ₀(m)`. -/
theorem coxPhiAtJ_eq_rightCosetProduct (m : ℕ+) (τ : ℍ) :
    coxPhiAtJ m τ =
      ∏ c : Gamma0RightCosets m,
        (Polynomial.X - Polynomial.C (rightCosetEval m c τ)) := by
  classical
  rw [coxPhiAtJ]
  calc
    ∏ σ : CoxMatrix m, (Polynomial.X - Polynomial.C (j (σ.act τ))) =
        ∏ σ : CoxMatrix m,
          (Polynomial.X - Polynomial.C
            (rightCosetEval m (coxMatrixEquivRightCosets m σ) τ)) := by
      apply Finset.prod_congr rfl
      intro σ _
      rw [rightCosetEval_equiv]
    _ = _ := by
      simpa using
        (Equiv.prod_comp (coxMatrixEquivRightCosets m)
          (fun c : Gamma0RightCosets m ↦
            Polynomial.X - Polynomial.C (rightCosetEval m c τ)))

/-- The specialized Cox product is invariant under the full modular group. -/
theorem coxPhiAtJ_sl2_smul (m : ℕ+) (δ : SL(2, ℤ)) (τ : ℍ) :
    coxPhiAtJ m (δ • τ) = coxPhiAtJ m τ := by
  classical
  rw [coxPhiAtJ_eq_rightCosetProduct, coxPhiAtJ_eq_rightCosetProduct]
  calc
    ∏ c : Gamma0RightCosets m,
        (Polynomial.X - Polynomial.C (rightCosetEval m c (δ • τ))) =
        ∏ c : Gamma0RightCosets m,
          (Polynomial.X - Polynomial.C
            (rightCosetEval m (rightCosetMul m δ c) τ)) := by
      apply Finset.prod_congr rfl
      intro c _
      rw [rightCosetEval_smul]
    _ = _ := by
      simpa using
        (Equiv.prod_comp (rightCosetMul m δ)
          (fun c : Gamma0RightCosets m ↦
            Polynomial.X - Polynomial.C (rightCosetEval m c τ)))

/-- Every coefficient of the Cox product is invariant under `SL₂(ℤ)`. -/
theorem coxPhiFunction_coeff_slashInvariant
    (m : ℕ+) (n : ℕ) (δ : SL(2, ℤ)) :
    ((coxPhiFunction m).coeff n) ∣[(0 : ℤ)] δ =
      (coxPhiFunction m).coeff n := by
  funext τ
  simp only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
  rw [coxPhiFunction_coeff_apply, coxPhiFunction_coeff_apply, coxPhiAtJ_sl2_smul]

open scoped Manifold in
/-- Every coefficient of the function-valued Cox product is holomorphic on the upper
half-plane. -/
theorem coxPhiFunction_coeff_mdifferentiable (m : ℕ+) (n : ℕ) :
    MDiff ((coxPhiFunction m).coeff n) := by
  classical
  letI : NeZero (m : ℕ) := ⟨PNat.ne_zero m⟩
  have hlevel : MDiff (levelJ m) := UpperHalfPlane.mdifferentiable_iff.mpr fun z hz ↦
    (jN_Meromorphic (m : ℕ) (z := ⟨z, hz⟩)).differentiableWithinAt
  have hcoset (c : Gamma0RightCosets m) : MDiff (rightCosetEval m c) :=
    Quotient.inductionOn c fun γ ↦ hlevel.comp <| UpperHalfPlane.mdifferentiable_smul
      (g := (γ : GL (Fin 2) ℝ)) (by simp)
  have hroot (σ : CoxMatrix m) : MDiff (fun τ : ℍ ↦ j (σ.act τ)) := by
    rw [← funext (rightCosetEval_equiv m σ)]
    exact hcoset (coxMatrixEquivRightCosets m σ)
  by_cases hn : n ≤ Fintype.card (CoxMatrix m)
  · have hcoeff := Finset.prod_X_add_C_coeff
      (R := ℍ → ℂ) (Finset.univ : Finset (CoxMatrix m))
      (fun σ ↦ -(fun τ ↦ j (σ.act τ))) hn
    have hcoeff' : (coxPhiFunction m).coeff n =
        ∑ t ∈ (Finset.univ : Finset (CoxMatrix m)).powersetCard
          (Fintype.card (CoxMatrix m) - n),
          ∏ σ ∈ t, -(fun τ ↦ j (σ.act τ)) := by
      simpa [coxPhiFunction, sub_eq_add_neg] using hcoeff
    rw [hcoeff']
    exact MDifferentiable.sum fun t _ ↦
      MDifferentiable.prod fun σ _ ↦ (hroot σ).neg
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [coxPhiFunction] using
      (lt_of_not_ge hn))]
    exact mdifferentiable_const

/-- Every Cox-product coefficient is meromorphic in the width-`m` cusp parameter. -/
theorem coxPhiFunction_coeff_widthM_cuspMeromorphicAt (m : ℕ+) (n : ℕ) :
    MeromorphicAt
      (cuspFunction ((m : ℕ) : ℝ) ((coxPhiFunction m).coeff n)) 0 := by
  classical
  rw [coxPhiFunction]
  exact polynomial_prod_coeff_cuspMeromorphicAt ((m : ℕ) : ℝ)
    (fun σ : CoxMatrix m ↦
      Polynomial.X - Polynomial.C (fun τ : ℍ ↦ j (σ.act τ)))
    Finset.univ (fun σ _ k ↦ coxLinearFactor_coeff_cuspMeromorphicAt m σ k) n


/-- Every Cox-product coefficient is meromorphic in the ordinary width-one cusp parameter. -/
theorem coxPhiFunction_coeff_widthOne_cuspMeromorphicAt (m : ℕ+) (n : ℕ) :
    MeromorphicAt (cuspFunction 1 ((coxPhiFunction m).coeff n)) 0 := by
  apply meromorphicAt_cuspFunction_of_nat_mul (m := (m : ℕ)) (h := 1)
    (PNat.ne_zero m)
  · simpa using coxPhiFunction_coeff_widthM_cuspMeromorphicAt m n
  · exact periodic_comp_of_slashInvariant_one
      (coxPhiFunction_coeff_slashInvariant m n)

/-- Every Cox-product coefficient is meromorphic on the upper half-plane. -/
theorem coxPhiFunction_coeff_meromorphicOnH (m : ℕ+) (n : ℕ) :
    ∀ z : ℂ, 0 < z.im →
      MeromorphicAt (((coxPhiFunction m).coeff n) ∘ UpperHalfPlane.ofComplex) z := by
  intro z hz
  have hd := UpperHalfPlane.mdifferentiable_iff.mp
    (coxPhiFunction_coeff_mdifferentiable m n)
  exact (hd.analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)).meromorphicAt

/-- Coefficients of the Cox product are level-one modular functions; this is the invariant
coefficient argument immediately preceding equation (11.14). -/
theorem coxPhiFunction_coeff_isLevelOne (m : ℕ+) (n : ℕ) :
    IsLevelOneModularFunction ((coxPhiFunction m).coeff n) := by
  let f := (coxPhiFunction m).coeff n
  have hslash := coxPhiFunction_coeff_slashInvariant m n
  refine ⟨coxPhiFunction_coeff_meromorphicOnH m n, ?_, ?_⟩
  · intro γ
    exact hslash γ
  · intro γ
    have hfun : (fun τ : ℍ ↦ f (γ • τ)) = f := by
      funext τ
      have h := congrFun (hslash γ) τ
      simpa only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one, f] using h
    rw [show (fun τ : ℍ ↦ (coxPhiFunction m).coeff n (γ • τ)) = f from hfun]
    simpa [f] using coxPhiFunction_coeff_widthOne_cuspMeromorphicAt m n

/-- Lemma 11.10 turns every coefficient of the Cox product into a polynomial in `j`. -/
theorem coxPhiFunction_coeff_polynomialInJ (m : ℕ+) (n : ℕ) :
    ∃ P : Polynomial ℂ, (coxPhiFunction m).coeff n = polynomialIn P j := by
  exact levelOne_polynomialInJ_of_holomorphic
    (coxPhiFunction_coeff_isLevelOne m n)
    (coxPhiFunction_coeff_mdifferentiable m n)

private noncomputable def coxCoefficientPolynomialAux
    (m : ℕ+) (n : ℕ) : Polynomial ℂ :=
  (coxPhiFunction_coeff_polynomialInJ m n).choose

private theorem coxCoefficientPolynomialAux_eval
    (m : ℕ+) (n : ℕ) (τ : ℍ) :
    (coxCoefficientPolynomialAux m n).eval (j τ) =
      (coxPhiFunction m).coeff n τ := by
  simpa [polynomialIn] using congrFun
    (coxPhiFunction_coeff_polynomialInJ m n).choose_spec.symm τ

private noncomputable def modularPolynomialCandidateAux
    (m : ℕ+) : BivariatePolynomial ℂ :=
  Polynomial.X ^ Fintype.card (CoxMatrix m) +
    ∑ n ∈ Finset.range (Fintype.card (CoxMatrix m)),
      Polynomial.monomial n (coxCoefficientPolynomialAux m n)

private theorem modularPolynomialCandidateAux_specializeY
    (m : ℕ+) (τ : ℍ) :
    (modularPolynomialCandidateAux m).specializeY (j τ) = coxPhiAtJ m τ := by
  classical
  calc
    (modularPolynomialCandidateAux m).specializeY (j τ) =
        Polynomial.X ^ Fintype.card (CoxMatrix m) +
          ∑ n ∈ Finset.range (Fintype.card (CoxMatrix m)),
            Polynomial.monomial n ((coxCoefficientPolynomialAux m n).eval (j τ)) := by
      simp [modularPolynomialCandidateAux, BivariatePolynomial.specializeY,
        Polynomial.map_sum]
    _ = Polynomial.X ^ Fintype.card (CoxMatrix m) +
          ∑ n ∈ Finset.range (Fintype.card (CoxMatrix m)),
            Polynomial.monomial n ((coxPhiAtJ m τ).coeff n) := by
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      rw [coxCoefficientPolynomialAux_eval, coxPhiFunction_coeff_apply]
    _ = coxPhiAtJ m τ := by
      rw [← coxPhiAtJ_natDegree m τ]
      simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
        (coxPhiAtJ_monic m τ).as_sum.symm

private theorem modularPolynomialCandidateAux_monic (m : ℕ+) :
    (modularPolynomialCandidateAux m).Monic := by
  classical
  apply Polynomial.monic_X_pow_add
  apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
  rw [Finset.sup_lt_iff]
  · intro n hn
    simp only [Finset.mem_range] at hn
    exact (Polynomial.degree_monomial_le _ _).trans_lt (WithBot.coe_lt_coe.mpr hn)
  · exact WithBot.bot_lt_coe _


/-- Existence and uniqueness of equation (11.14), normalized to be monic in the outer/root
variable `X`. -/
theorem existsUnique_modularPolynomialC (m : ℕ+) :
    ∃! Φ : BivariatePolynomial ℂ,
      Φ.Monic ∧ ∀ τ : ℍ, Φ.specializeY (j τ) = coxPhiAtJ m τ := by
  refine ⟨modularPolynomialCandidateAux m,
    ⟨modularPolynomialCandidateAux_monic m,
      modularPolynomialCandidateAux_specializeY m⟩, ?_⟩
  intro Φ hΦ
  apply BivariatePolynomial.specializeY_ext
  intro y
  obtain ⟨τ, rfl⟩ := j_surjective y
  rw [hΦ.2 τ, modularPolynomialCandidateAux_specializeY]

/-- Cox's complex modular polynomial. -/
noncomputable def modularPolynomialC (m : ℕ+) : BivariatePolynomial ℂ :=
  (existsUnique_modularPolynomialC m).choose

theorem modularPolynomialC_monic (m : ℕ+) : (modularPolynomialC m).Monic := by
  exact (existsUnique_modularPolynomialC m).choose_spec.1.1

/-- Equation (11.15), the product formula indexed by `C(m)`. -/
theorem modularPolynomialC_specializeY (m : ℕ+) (τ : ℍ) :
    (modularPolynomialC m).specializeY (j τ) = coxPhiAtJ m τ := by
  exact (existsUnique_modularPolynomialC m).choose_spec.1.2 τ

/-- Equation (11.14), the equivalent right-coset product. -/
theorem modularPolynomialC_rightCosetProduct (m : ℕ+) (τ : ℍ) :
    (modularPolynomialC m).specializeY (j τ) =
      ∏ c : Gamma0RightCosets m,
        (Polynomial.X - Polynomial.C (rightCosetEval m c τ)) := by
  rw [modularPolynomialC_specializeY, coxPhiAtJ_eq_rightCosetProduct]

/-- The distinguished root `Φ_m(j(mτ),j(τ))=0`. -/
theorem modularPolynomialC_eval_levelJ_j (m : ℕ+) (τ : ℍ) :
    (modularPolynomialC m).eval (levelJ m τ) (j τ) = 0 := by
  rw [← BivariatePolynomial.specializeY_eval,
    modularPolynomialC_specializeY, coxPhiAtJ]
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (sigmaZero m))
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
  exact (congrFun (j_act_sigmaZero m) τ).symm

/-- Degree in the root variable. -/
theorem modularPolynomialC_natDegree (m : ℕ+) :
    (modularPolynomialC m).natDegree = Fintype.card (CoxMatrix m) := by
  let τ : ℍ := ⟨Complex.I, by norm_num⟩
  calc
    (modularPolynomialC m).natDegree =
        ((modularPolynomialC m).specializeY (j τ)).natDegree :=
      ((modularPolynomialC_monic m).natDegree_map
        (Polynomial.evalRingHom (j τ))).symm
    _ = Fintype.card (CoxMatrix m) := by
      rw [modularPolynomialC_specializeY, coxPhiAtJ_natDegree]

end Cox

