import Mathlib.FieldTheory.RatFunc.Defs
import XYin.PhD.Cox.CoxMatrices

/-!
# Cox's modular polynomial and the proof of Theorem 11.9(ii)

Variable convention is fixed explicitly to avoid the ambiguity in the earlier experimental
files: the **outer** polynomial variable is Cox's root variable `X`, and the inner coefficient
variable is Cox's parameter `Y`.  Thus irreducibility of the outer polynomial is literally
"irreducible as a polynomial in `X`".
-/

open Complex Function MatrixGroups UpperHalfPlane
open scoped Polynomial.Bivariate

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

/-- Coefficients of the Cox product are level-one modular functions; this is the invariant
coefficient argument immediately preceding equation (11.14). -/
theorem coxPhiFunction_coeff_isLevelOne (m : ℕ+) (n : ℕ) :
    IsLevelOneModularFunction ((coxPhiFunction m).coeff n) := by
  sorry

/-- Lemma 11.10 turns every coefficient of the Cox product into a polynomial in `j`. -/
theorem coxPhiFunction_coeff_polynomialInJ (m : ℕ+) (n : ℕ) :
    ∃ P : Polynomial ℂ, (coxPhiFunction m).coeff n = polynomialIn P j := by
  sorry

/-- Existence and uniqueness of equation (11.14), normalized to be monic in the outer/root
variable `X`. -/
theorem existsUnique_modularPolynomialC (m : ℕ+) :
    ∃! Φ : BivariatePolynomial ℂ,
      Φ.Monic ∧ ∀ τ : ℍ, Φ.specializeY (j τ) = coxPhiAtJ m τ := by
  sorry

/-- Cox's complex modular polynomial. -/
noncomputable def modularPolynomialC (m : ℕ+) : BivariatePolynomial ℂ :=
  (existsUnique_modularPolynomialC m).choose

theorem modularPolynomialC_monic (m : ℕ+) : (modularPolynomialC m).Monic := by
  sorry

/-- Equation (11.15), the product formula indexed by `C(m)`. -/
theorem modularPolynomialC_specializeY (m : ℕ+) (τ : ℍ) :
    (modularPolynomialC m).specializeY (j τ) = coxPhiAtJ m τ := by
  sorry

/-- Equation (11.14), the equivalent right-coset product. -/
theorem modularPolynomialC_rightCosetProduct (m : ℕ+) (τ : ℍ) :
    (modularPolynomialC m).specializeY (j τ) =
      ∏ c : Gamma0RightCosets m,
        (Polynomial.X - Polynomial.C (rightCosetEval m c τ)) := by
  sorry

/-- The distinguished root `Φ_m(j(mτ),j(τ))=0`. -/
theorem modularPolynomialC_eval_levelJ_j (m : ℕ+) (τ : ℍ) :
    (modularPolynomialC m).eval (levelJ m τ) (j τ) = 0 := by
  sorry

/-- Degree in the root variable. -/
theorem modularPolynomialC_natDegree (m : ℕ+) :
    (modularPolynomialC m).natDegree = Fintype.card (CoxMatrix m) := by
  sorry

/-- Equation (11.16), Cox's interpolation polynomial at a point of the upper half-plane. -/
noncomputable def interpolationAt (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (τ : ℍ) : Polynomial ℂ :=
  ∑ σ : CoxMatrix m,
    Polynomial.C
        (rightCosetTranslate m hf (coxMatrixEquivRightCosets m σ) τ) *
      ∏ σ' ∈ (Finset.univ.erase σ),
        (Polynomial.X - Polynomial.C (j (σ'.act τ)))

/-- Exercise 11.11: every coefficient of the interpolation polynomial is a level-one modular
function of `τ`. -/
theorem interpolation_coeff_isLevelOne (m : ℕ+) {f : ℍ → ℂ}
    (hf : IsGamma0ModularFunction m f) (n : ℕ) :
    IsLevelOneModularFunction (fun τ ↦ (interpolationAt m hf τ).coeff n) := by
  sorry

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
  sorry

/-- Exercise 11.10 / Theorem 11.18(ii), function-field form: `Φ_m` is irreducible in the
root variable over `ℂ(Y)`. -/
theorem modularPolynomialC_irreducibleInX (m : ℕ+) :
    Irreducible (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      (modularPolynomialC m)) := by
  sorry

/-- Hasse's q-expansion principle in the coefficient form needed for integral descent. -/
theorem hasse_qExpansion_principle {P : Polynomial ℂ}
    (hint : ∀ n : ℤ, ∃ k : ℤ,
      (laurentqExpansion 1 (polynomialIn P j)).coeff n = (k : ℂ)) :
    ∃ Q : Polynomial ℤ, P = Q.map (Int.castRingHom ℂ) := by
  sorry

/-- Galois descent from (11.13): every Laurent coefficient of every elementary symmetric
function in the Cox roots is an ordinary integer. -/
theorem coxPhiFunction_coeff_integerLaurent (m : ℕ+) (n : ℕ) (k : ℤ) :
    ∃ z : ℤ,
      (laurentqExpansion 1 ((coxPhiFunction m).coeff n)).coeff k = (z : ℂ) := by
  sorry

/-- Cox Theorem 11.18(i): the complex modular polynomial descends to `ℤ[X,Y]`. -/
theorem exists_modularPolynomialZ (m : ℕ+) :
    ∃ Φ : BivariatePolynomial ℤ,
      BivariatePolynomial.map (Int.castRingHom ℂ) Φ = modularPolynomialC m := by
  sorry

/-- The canonical integer descent of the modular polynomial. -/
noncomputable def modularPolynomial (m : ℕ+) : BivariatePolynomial ℤ :=
  (exists_modularPolynomialZ m).choose

theorem modularPolynomial_map_complex (m : ℕ+) :
    BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m) =
      modularPolynomialC m := by
  sorry

end Cox
