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

This file constructs Cox's complex modular polynomial `modularPolynomialC m`, the unique
bivariate polynomial that is monic in its root variable and whose specializations at `j(τ)` are
the Cox products `coxPhiAtJ m τ` of equation (11.15). It also proves a few general lemmas on
bivariate polynomials that mathlib lacks (namespace `Polynomial.Bivariate`).

## Variable convention

Bivariate polynomials are mathlib's `R[X][Y] = Polynomial (Polynomial R)` (scope
`Polynomial.Bivariate`), whose **outer** variable is `Y = Polynomial.X` and whose **inner**
variable is `C X = Polynomial.C Polynomial.X`. Cox writes `Φ_m(X, Y)` with root variable `X`
(`Φ_m` is monic of degree `|C(m)|` in `X`) and parameter `Y`. The formalization represents
`Φ_m` by `Φ : ℤ[X][Y]` (or `ℂ[X][Y]`) whose outer variable `Y` plays Cox's root variable `X`
and whose inner variable `C X` plays Cox's parameter `Y`. Consequently:

* Cox's value `Φ_m(x, y)` is `Φ.evalEval y x`: mathlib's `evalEval` substitutes its first
  argument into the inner variable and its second into the outer one;
* Cox's `Φ_m(X, j(τ))`, a polynomial in the root variable, is `Φ.map (evalRingHom (j τ))`;
* Cox's diagonal `Φ_m(X, X)` is `Φ.eval X`;
* Cox's `X` and `Y` are written `Y` and `C X`; for instance Cox's `(X ^ p - Y) * (X - Y ^ p)`
  is `(Y ^ p - C X) * (Y - C X ^ p)`;
* `Φ.Monic`, `Φ.natDegree` and `Φ.coeff` refer to the root variable, and
  `Polynomial.Bivariate.swap` exchanges the two variables.

The specialized Cox product `coxPhiAtJ m τ` is the Lagrange nodal polynomial of the nodes
`j(σ τ)` (`coxPhiAtJ_eq_nodal`).
-/

open Complex Function MatrixGroups ModularForm UpperHalfPlane
open scoped Manifold Polynomial.Bivariate

noncomputable section

namespace Polynomial.Bivariate

variable {R S : Type*}

/-- A bivariate polynomial over an infinite domain is determined by its specializations
`p.map (evalRingHom y)` of the inner variable. -/
theorem ext_of_map_evalRingHom [CommRing R] [IsDomain R] [Infinite R] {p q : R[X][Y]}
    (h : ∀ y : R, p.map (evalRingHom y) = q.map (evalRingHom y)) : p = q :=
  Polynomial.ext fun n ↦ Polynomial.funext fun y ↦ by
    simpa only [coeff_map, coe_evalRingHom] using congrArg (coeff · n) (h y)

/-- The coefficient of `Y ^ i * X ^ j` in `swap p` is the coefficient of `Y ^ j * X ^ i`
in `p`. -/
theorem coeff_coeff_swap [CommSemiring R] (p : R[X][Y]) (i j : ℕ) :
    ((swap p).coeff i).coeff j = (p.coeff j).coeff i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using congrArg₂ (· + ·) hp hq
  | monomial n a =>
      rw [swap_monomial, coeff_mul_C, coeff_map]
      by_cases h : j = n <;> simp [coeff_monomial, h, eq_comm]

/-- Swapping the variables commutes with a coefficientwise ring homomorphism. -/
theorem map_mapRingHom_swap [CommSemiring R] [CommSemiring S] (f : R →+* S) (p : R[X][Y]) :
    (swap p).map (mapRingHom f) = swap (p.map (mapRingHom f)) := by
  ext i j
  simp [coeff_coeff_swap, coeff_map]

/-- Evaluating the diagonal `p.eval X` at `x` is evaluating `p` at `(x, x)`. -/
theorem eval_eval_X [CommSemiring R] (x : R) (p : R[X][Y]) :
    (p.eval X).eval x = p.evalEval x x := by
  rw [← map_evalRingHom_eval, eval_map, ← coe_evalRingHom, eval, hom_eval₂]
  simp

/-- Evaluating the diagonal `p.eval X` along `f` at `x` evaluates `p` along `f` at `(x, x)`. -/
theorem eval₂_eval_X [CommSemiring R] [CommSemiring S] (f : R →+* S) (x : S) (p : R[X][Y]) :
    (p.eval X).eval₂ f x = p.eval₂ (eval₂RingHom f x) x := by
  simpa using hom_eval₂ p (RingHom.id R[X]) (eval₂RingHom f x) X

/-- The diagonal `p.eval X` is unchanged by swapping the two variables. -/
@[simp]
theorem eval_X_swap [CommSemiring R] (p : R[X][Y]) : (swap p).eval X = p.eval X := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, eval_add, hp, hq]
  | monomial n a =>
      rw [swap_monomial]
      simp only [eval_mul, eval_map, eval₂_C_X, eval_C, eval_monomial]

/-- The linear coefficient of the diagonal `p.eval X`. -/
theorem coeff_eval_X_one [CommSemiring R] (p : R[X][Y]) :
    (p.eval X).coeff 1 = (p.coeff 0).coeff 1 + (p.coeff 1).coeff 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [eval_add, coeff_add, hp, hq]
      ring
  | monomial n a =>
      rcases n with _ | _ | n
      · simp
      · simp
      · rw [eval_monomial, coeff_mul_X_pow']
        simp [coeff_monomial]

end Polynomial.Bivariate

namespace Cox

/-- Equation (11.15): Cox's `Φ_m(X, j(τ)) = ∏_{σ ∈ C(m)} (X - j(σ τ))`, a polynomial in the
root variable. -/
noncomputable def coxPhiAtJ (m : ℕ+) (τ : ℍ) : Polynomial ℂ :=
  ∏ σ : CoxMatrix m, (Polynomial.X - Polynomial.C (j (σ.act τ)))

/-- The same Cox product before evaluating `τ`, with function-valued coefficients. -/
noncomputable def coxPhiFunction (m : ℕ+) : Polynomial (ℍ → ℂ) :=
  ∏ σ : CoxMatrix m,
    (Polynomial.X - Polynomial.C (fun τ ↦ j (σ.act τ)))

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
def coxPhiFunctionCoeffModularFunction (m : ℕ+) (n : ℕ) : ModularFunction 𝒮ℒ :=
  ModularFunction.ofLevelOneHolomorphic _ (coxPhiFunction_coeff_mdifferentiable m n)
    (coxPhiFunction_coeff_slashInvariant m n) (coxPhiFunction_coeff_widthOne_cuspMeromorphicAt m n)

/-- Lemma 11.10 turns every coefficient of the Cox product into a polynomial in `j`. -/
theorem coxPhiFunction_coeff_polynomialInJ (m : ℕ+) (n : ℕ) :
    ∃ P : Polynomial ℂ, (coxPhiFunction m).coeff n = polynomialIn P j :=
  levelOne_polynomialInJ_of_holomorphic
    (coxPhiFunctionCoeffModularFunction m n)
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

private noncomputable def modularPolynomialCandidateAux (m : ℕ+) : ℂ[X][Y] :=
  Y ^ Fintype.card (CoxMatrix m) +
    ∑ n ∈ Finset.range (Fintype.card (CoxMatrix m)),
      Polynomial.monomial n (coxCoefficientPolynomialAux m n)

private theorem modularPolynomialCandidateAux_map_evalRingHom (m : ℕ+) (τ : ℍ) :
    (modularPolynomialCandidateAux m).map (Polynomial.evalRingHom (j τ)) = coxPhiAtJ m τ := by
  classical
  simpa [modularPolynomialCandidateAux, Polynomial.map_sum, coxCoefficientPolynomialAux_eval,
    coxPhiFunction_coeff_apply, coxPhiAtJ_natDegree, Polynomial.C_mul_X_pow_eq_monomial] using
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

/-- Existence and uniqueness of equation (11.14): exactly one `Φ : ℂ[X][Y]` is monic in the
root variable and satisfies Cox's `Φ(X, j(τ)) = coxPhiAtJ m τ` for every `τ`. -/
theorem existsUnique_modularPolynomialC (m : ℕ+) :
    ∃! Φ : ℂ[X][Y],
      Φ.Monic ∧ ∀ τ : ℍ, Φ.map (Polynomial.evalRingHom (j τ)) = coxPhiAtJ m τ := by
  refine ⟨modularPolynomialCandidateAux m,
    ⟨modularPolynomialCandidateAux_monic m,
      modularPolynomialCandidateAux_map_evalRingHom m⟩, ?_⟩
  intro Φ hΦ
  apply Polynomial.Bivariate.ext_of_map_evalRingHom
  intro y
  obtain ⟨τ, rfl⟩ := j_surjective y
  rw [hΦ.2 τ, modularPolynomialCandidateAux_map_evalRingHom]

/-- Cox's complex modular polynomial `Φ_m`. The outer variable `Y` of `ℂ[X][Y]` is Cox's root
variable `X` and the inner variable `C X` is Cox's parameter `Y`, so Cox's `Φ_m(x, y)` is
`(modularPolynomialC m).evalEval y x` (see the module docstring). -/
noncomputable def modularPolynomialC (m : ℕ+) : ℂ[X][Y] :=
  (existsUnique_modularPolynomialC m).choose

/-- `Φ_m` is monic in the root variable. -/
theorem modularPolynomialC_monic (m : ℕ+) : (modularPolynomialC m).Monic :=
  (existsUnique_modularPolynomialC m).choose_spec.1.1

/-- Equation (11.15), the product formula indexed by `C(m)`: Cox's
`Φ_m(X, j(τ)) = ∏_{σ ∈ C(m)} (X - j(σ τ))`. -/
theorem modularPolynomialC_map_evalRingHom (m : ℕ+) (τ : ℍ) :
    (modularPolynomialC m).map (Polynomial.evalRingHom (j τ)) = coxPhiAtJ m τ :=
  (existsUnique_modularPolynomialC m).choose_spec.1.2 τ

/-- The coefficient polynomials of `Φ_m` recover the function-valued Cox-product
coefficients after substituting `j` for the parameter. -/
theorem modularPolynomialC_coeff_polynomialIn (m : ℕ+) (n : ℕ) :
    polynomialIn ((modularPolynomialC m).coeff n) j =
      (coxPhiFunction m).coeff n := by
  funext τ
  have hcoeff := congrArg (fun P : Polynomial ℂ ↦ P.coeff n)
    (modularPolynomialC_map_evalRingHom m τ)
  rw [coxPhiFunction_coeff_apply]
  simpa [polynomialIn, Polynomial.coeff_map] using hcoeff

/-- Equation (11.14), the equivalent right-coset product. -/
theorem modularPolynomialC_rightCosetProduct (m : ℕ+) (τ : ℍ) :
    (modularPolynomialC m).map (Polynomial.evalRingHom (j τ)) =
      ∏ c : Gamma0RightCosets m,
        (Polynomial.X - Polynomial.C (rightCosetEval m c τ)) := by
  rw [modularPolynomialC_map_evalRingHom, coxPhiAtJ_eq_rightCosetProduct]

/-- The roots of Cox's `Φ_m(X, j(τ))` are exactly the values `j(σ τ)`, `σ ∈ C(m)`. -/
theorem modularPolynomialC_evalEval_eq_zero_iff (m : ℕ+) (τ : ℍ) (u : ℂ) :
    (modularPolynomialC m).evalEval (j τ) u = 0 ↔ ∃ σ : CoxMatrix m, u = j (σ.act τ) := by
  rw [← Polynomial.map_evalRingHom_eval, modularPolynomialC_map_evalRingHom]
  simp [coxPhiAtJ, Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

/-- Every Cox transform gives a root: Cox's `Φ_m(j(σ τ), j(τ)) = 0`. -/
theorem modularPolynomialC_evalEval_j_act (m : ℕ+) (σ : CoxMatrix m) (τ : ℍ) :
    (modularPolynomialC m).evalEval (j τ) (j (σ.act τ)) = 0 :=
  (modularPolynomialC_evalEval_eq_zero_iff m τ _).2 ⟨σ, rfl⟩

/-- The distinguished root, Cox's `Φ_m(j(mτ), j(τ)) = 0`. -/
theorem modularPolynomialC_evalEval_j_levelJ (m : ℕ+) (τ : ℍ) :
    (modularPolynomialC m).evalEval (j τ) (levelJ m τ) = 0 := by
  rw [← j_act_sigmaZero]
  exact modularPolynomialC_evalEval_j_act m (sigmaZero m) τ

/-- Degree in the root variable. -/
theorem modularPolynomialC_natDegree (m : ℕ+) :
    (modularPolynomialC m).natDegree = Fintype.card (CoxMatrix m) := by
  rw [← coxPhiAtJ_natDegree m UpperHalfPlane.I,
    ← modularPolynomialC_map_evalRingHom m UpperHalfPlane.I]
  exact ((modularPolynomialC_monic m).natDegree_map
    (Polynomial.evalRingHom (j UpperHalfPlane.I))).symm

end Cox
