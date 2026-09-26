/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.LinearAlgebra.Lagrange
import XYin.PhD.Cox.ModularFunction
import XYin.PhD.Cox.ModularPolynomial.AnalyticSupport

/-!
# Construction of Cox's modular polynomial

This file develops the bivariate-polynomial API, the function-valued Cox product, and the
canonical complex modular polynomial characterized by its specializations at `Y = j(τ)`.

`BivariatePolynomial.eval Φ x y` evaluates with the semantic argument order (root `x`,
parameter `y`); it is mathlib's `Polynomial.evalEval y x` (`BivariatePolynomial.eval_eq_evalEval`).
The specialized Cox product `coxPhiAtJ m τ` is the Lagrange nodal polynomial of the nodes
`j(σ τ)` (`coxPhiAtJ_eq_nodal`).
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

/-- Bivariate evaluation in the semantic order `(x, y)` is mathlib's `evalEval y x`. -/
theorem eval_eq_evalEval {R : Type*} [Semiring R] (Φ : BivariatePolynomial R) (x y : R) :
    eval Φ x y = Φ.evalEval y x :=
  rfl

/-- Specializing the parameter commutes with differentiation in the root variable. -/
theorem derivative_specializeY {R : Type*} [CommSemiring R] (y : R)
    (Φ : BivariatePolynomial R) :
    (specializeY y Φ).derivative = specializeY y Φ.derivative :=
  Polynomial.derivative_map Φ _

/-- `BivariatePolynomial.map` as a ring homomorphism. -/
abbrev mapRingHom {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) :
    BivariatePolynomial R →+* BivariatePolynomial S :=
  Polynomial.mapRingHom (Polynomial.mapRingHom f)

/-- `BivariatePolynomial.mapRingHom f` is `BivariatePolynomial.map f`. (Not `@[simp]`: `simp`
unfolds the abbreviation `mapRingHom` first, so the left-hand side is not in simp normal form.) -/
theorem coe_mapRingHom {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) :
    ⇑(mapRingHom f) = map f :=
  rfl

/-- Coefficientwise maps along injective ring homomorphisms are injective. -/
theorem map_injective {R S : Type*} [Semiring R] [Semiring S] {f : R →+* S}
    (hf : Function.Injective f) : Function.Injective (map f) :=
  Polynomial.map_injective _ (Polynomial.map_injective f hf)

/-- Coefficientwise maps commute with negation. -/
theorem map_neg {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (Φ : BivariatePolynomial R) :
    map f (-Φ) = -map f Φ :=
  Polynomial.map_neg _

/-- Coefficientwise maps commute with subtraction. -/
theorem map_sub {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (Φ Ψ : BivariatePolynomial R) :
    map f (Φ - Ψ) = map f Φ - map f Ψ :=
  Polynomial.map_sub _

end BivariatePolynomial

/-- Swapping the variables exchanges the two semantic evaluation arguments. -/
theorem BivariatePolynomial.eval_swap {R : Type*} [CommSemiring R]
    (Φ : BivariatePolynomial R) (x y : R) :
    BivariatePolynomial.eval (Polynomial.Bivariate.swap Φ) x y =
      BivariatePolynomial.eval Φ y x := by
  simpa only [BivariatePolynomial.eval, Polynomial.coe_aevalAeval_eq_evalEval] using
    Polynomial.Bivariate.aevalAeval_swap y x Φ

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
  ext i j
  simp [BivariatePolynomial.map, BivariatePolynomial.coeff_coeff_swap, Polynomial.coeff_map]

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
      simpa only [BivariatePolynomial.diagonal, map_add, Polynomial.eval_add] using
        congrArg₂ (· + ·) hP hQ
  | monomial n P =>
      rw [Polynomial.Bivariate.swap_monomial]
      simp only [diagonal, Polynomial.eval_mul, Polynomial.eval_map,
        Polynomial.eval₂_C_X, Polynomial.eval_C, Polynomial.eval_monomial]

/-- The linear coefficient of the diagonal specialization. -/
theorem BivariatePolynomial.diagonal_coeff_one {R : Type*} [CommSemiring R]
    (Φ : BivariatePolynomial R) :
    (BivariatePolynomial.diagonal Φ).coeff 1 =
      (Φ.coeff 0).coeff 1 + (Φ.coeff 1).coeff 0 := by
  induction Φ using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [BivariatePolynomial.diagonal, Polynomial.eval_add,
        Polynomial.coeff_add] at hP hQ ⊢
      rw [hP, hQ]
      ring
  | monomial n P =>
      rcases n with _ | _ | n
      · simp [BivariatePolynomial.diagonal]
      · simp [BivariatePolynomial.diagonal]
      · simp only [BivariatePolynomial.diagonal, Polynomial.eval_monomial]
        rw [Polynomial.coeff_mul_X_pow']
        simp [Polynomial.coeff_monomial]

/-- The specialized Cox product is the Lagrange nodal polynomial of the nodes `j(σ τ)`. -/
theorem coxPhiAtJ_eq_nodal (m : ℕ+) (τ : ℍ) :
    coxPhiAtJ m τ = Lagrange.nodal Finset.univ (fun σ : CoxMatrix m ↦ j (σ.act τ)) :=
  rfl

/-- The specialized Cox product is monic in its root variable. -/
theorem coxPhiAtJ_monic (m : ℕ+) (τ : ℍ) : (coxPhiAtJ m τ).Monic :=
  Lagrange.nodal_monic

/-- The degree of the specialized Cox product is the cardinality of `C(m)`. -/
theorem coxPhiAtJ_natDegree (m : ℕ+) (τ : ℍ) :
    (coxPhiAtJ m τ).natDegree = Fintype.card (CoxMatrix m) :=
  Lagrange.natDegree_nodal

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
  simpa only [coxPhiAtJ, rightCosetEval_equiv] using
    (Equiv.prod_comp (coxMatrixEquivRightCosets m)
      (fun c : Gamma0RightCosets m ↦ Polynomial.X - Polynomial.C (rightCosetEval m c τ)))

/-- The specialized Cox product is invariant under the full modular group. -/
theorem coxPhiAtJ_sl2_smul (m : ℕ+) (δ : SL(2, ℤ)) (τ : ℍ) :
    coxPhiAtJ m (δ • τ) = coxPhiAtJ m τ := by
  classical
  simp only [coxPhiAtJ_eq_rightCosetProduct, rightCosetEval_smul]
  exact Equiv.prod_comp (rightCosetMul m δ)
    (fun c : Gamma0RightCosets m ↦ Polynomial.X - Polynomial.C (rightCosetEval m c τ))

/-- Every coefficient of the Cox product is invariant under `SL₂(ℤ)`. -/
theorem coxPhiFunction_coeff_slashInvariant
    (m : ℕ+) (n : ℕ) (δ : SL(2, ℤ)) :
    ((coxPhiFunction m).coeff n) ∣[(0 : ℤ)] δ =
      (coxPhiFunction m).coeff n :=
  SL_slash_zero_eq_iff.2 fun τ ↦ by
    rw [coxPhiFunction_coeff_apply, coxPhiFunction_coeff_apply, coxPhiAtJ_sl2_smul]

/-- Every coefficient of the function-valued Cox product is holomorphic on the upper
half-plane. -/
theorem coxPhiFunction_coeff_mdifferentiable (m : ℕ+) (n : ℕ) :
    MDiff ((coxPhiFunction m).coeff n) :=
  coxNodal_coeff_mdifferentiable m Finset.univ n

/-- Every Cox-product coefficient is meromorphic in the width-`m` cusp parameter. -/
theorem coxPhiFunction_coeff_widthM_cuspMeromorphicAt (m : ℕ+) (n : ℕ) :
    MeromorphicAt
      (cuspFunction ((m : ℕ) : ℝ) ((coxPhiFunction m).coeff n)) 0 :=
  coxNodal_coeff_cuspMeromorphicAt m Finset.univ n

/-- Every Cox-product coefficient is level-one raw analytic data. -/
theorem coxPhiFunction_coeff_cuspData (m : ℕ+) (n : ℕ) :
    LevelOneCuspData ((coxPhiFunction m).coeff n) :=
  .of_widthM (m := m)
    (fun _ hz ↦ meromorphicAt_comp_ofComplex_of_mdifferentiable
      (coxPhiFunction_coeff_mdifferentiable m n) hz)
    (coxPhiFunction_coeff_slashInvariant m n) (coxPhiFunction_coeff_widthM_cuspMeromorphicAt m n)

/-- Every Cox-product coefficient is meromorphic in the ordinary width-one cusp parameter. -/
theorem coxPhiFunction_coeff_widthOne_cuspMeromorphicAt (m : ℕ+) (n : ℕ) :
    MeromorphicAt (cuspFunction 1 ((coxPhiFunction m).coeff n)) 0 :=
  (coxPhiFunction_coeff_cuspData m n).meromorphicAt_cuspFunction_one

/-- Coefficients of the Cox product are level-one modular functions; this is the invariant
coefficient argument immediately preceding equation (11.14). -/
def coxPhiFunction_coeff_modularFunction (m : ℕ+) (n : ℕ) : ModularFunction 𝒮ℒ :=
  ModularFunction.ofLevelOneHolomorphic _ (coxPhiFunction_coeff_mdifferentiable m n)
    (coxPhiFunction_coeff_slashInvariant m n) (coxPhiFunction_coeff_widthOne_cuspMeromorphicAt m n)

/-- Lemma 11.10 turns every coefficient of the Cox product into a polynomial in `j`. -/
theorem coxPhiFunction_coeff_polynomialInJ (m : ℕ+) (n : ℕ) :
    ∃ P : Polynomial ℂ, (coxPhiFunction m).coeff n = polynomialIn P j :=
  levelOne_polynomialInJ_of_holomorphic
    (coxPhiFunction_coeff_modularFunction m n)
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
  simpa [modularPolynomialCandidateAux, BivariatePolynomial.specializeY,
    Polynomial.map_sum, coxCoefficientPolynomialAux_eval, coxPhiFunction_coeff_apply,
    coxPhiAtJ_natDegree, Polynomial.C_mul_X_pow_eq_monomial] using
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

theorem modularPolynomialC_monic (m : ℕ+) : (modularPolynomialC m).Monic :=
  (existsUnique_modularPolynomialC m).choose_spec.1.1

/-- Equation (11.15), the product formula indexed by `C(m)`. -/
theorem modularPolynomialC_specializeY (m : ℕ+) (τ : ℍ) :
    (modularPolynomialC m).specializeY (j τ) = coxPhiAtJ m τ :=
  (existsUnique_modularPolynomialC m).choose_spec.1.2 τ

/-- The coefficient polynomials of `Φ_m` recover the function-valued Cox-product
coefficients after substituting `Y = j`. -/
theorem modularPolynomialC_coeff_polynomialIn (m : ℕ+) (n : ℕ) :
    polynomialIn ((modularPolynomialC m).coeff n) j =
      (coxPhiFunction m).coeff n := by
  funext τ
  have hcoeff := congrArg (fun P : Polynomial ℂ ↦ P.coeff n)
    (modularPolynomialC_specializeY m τ)
  rw [coxPhiFunction_coeff_apply]
  simpa [polynomialIn, BivariatePolynomial.specializeY,
    Polynomial.coeff_map] using hcoeff

/-- Equation (11.14), the equivalent right-coset product. -/
theorem modularPolynomialC_rightCosetProduct (m : ℕ+) (τ : ℍ) :
    (modularPolynomialC m).specializeY (j τ) =
      ∏ c : Gamma0RightCosets m,
        (Polynomial.X - Polynomial.C (rightCosetEval m c τ)) := by
  rw [modularPolynomialC_specializeY, coxPhiAtJ_eq_rightCosetProduct]

/-- The roots of `Φ_m(X, j(τ))` are exactly the values `j(σ τ)`, `σ ∈ C(m)`. -/
theorem modularPolynomialC_eval_eq_zero_iff (m : ℕ+) (τ : ℍ) (u : ℂ) :
    (modularPolynomialC m).eval u (j τ) = 0 ↔ ∃ σ : CoxMatrix m, u = j (σ.act τ) := by
  simp [← BivariatePolynomial.specializeY_eval, modularPolynomialC_specializeY, coxPhiAtJ,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

/-- Every Cox transform gives a root: `Φ_m(j(σ τ), j(τ)) = 0`. -/
theorem modularPolynomialC_eval_act_j (m : ℕ+) (σ : CoxMatrix m) (τ : ℍ) :
    (modularPolynomialC m).eval (j (σ.act τ)) (j τ) = 0 :=
  (modularPolynomialC_eval_eq_zero_iff m τ _).2 ⟨σ, rfl⟩

/-- The distinguished root `Φ_m(j(mτ),j(τ))=0`. -/
theorem modularPolynomialC_eval_levelJ_j (m : ℕ+) (τ : ℍ) :
    (modularPolynomialC m).eval (levelJ m τ) (j τ) = 0 := by
  rw [← j_act_sigmaZero]
  exact modularPolynomialC_eval_act_j m (sigmaZero m) τ

/-- Degree in the root variable. -/
theorem modularPolynomialC_natDegree (m : ℕ+) :
    (modularPolynomialC m).natDegree = Fintype.card (CoxMatrix m) := by
  rw [← coxPhiAtJ_natDegree m UpperHalfPlane.I,
    ← modularPolynomialC_specializeY m UpperHalfPlane.I]
  exact ((modularPolynomialC_monic m).natDegree_map
    (Polynomial.evalRingHom (j UpperHalfPlane.I))).symm

end Cox
