import XYin.PhD.Test.JLevelN.Existence

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups
  PowerSeries SlashInvariantFormClass Real Function IntegralPowerSeries Polynomial
open scoped Manifold

/-!
# Cox Theorem 11.18(i): the integer modular polynomial `Φ_m`

This file packages the abstract complex Cox product `coxPhiFunction m` as a single
bivariate polynomial `modularEquationComplex m ∈ ℂ[X][Y]`, states Cox Theorem 11.18(i)
— that this polynomial descends to `ℤ[X][Y]` — and defines the canonical integer
modular polynomial `modularPolynomial m ∈ ℤ[X][Y]` as that descent.

The descent statement `modularEquation_integer_descent` is the SKELETON form of
Theorem 11.18(i); its proof (the Galois-on-q-expansion + Hasse-q-expansion-principle
argument of Cox pp. 231–232) is decomposed in `QExpansion1113.lean` / `HasseQPrinciple.lean`
and is left as `sorry` here.
-/

namespace Test

noncomputable section

section ModularPolynomialInteger

/-- The complex Cox modular polynomial `Φ_m ∈ ℂ[X][Y]`, chosen from
`cox_modularEquation_exists`.  By `modularEquationComplex_map_eq` its image under
`polynomialInJRingHom` is the function-valued Cox product `coxPhiFunction m`. -/
noncomputable def modularEquationComplex (m : ℕ+) : ℂ[X][X] :=
  (cox_modularEquation_exists m).choose

/-- Defining property of `modularEquationComplex`: mapping its coefficients through
`polynomialInJRingHom` recovers the function-valued Cox product. -/
theorem modularEquationComplex_map_eq (m : ℕ+) :
    (modularEquationComplex m).map polynomialInJRingHom = coxPhiFunction m :=
  (cox_modularEquation_exists m).choose_spec.1

/-- The root relation, Cox equation (11.14): the complex modular polynomial vanishes
on `jN m`. -/
theorem modularEquationComplex_eval_jN (m : ℕ+) :
    Polynomial.eval (jN m) ((modularEquationComplex m).map polynomialInJRingHom) = 0 := by
  rw [modularEquationComplex_map_eq]
  exact coxPhiFunction_eval_jN m

/-- **Cox Theorem 11.18(i).** The complex Cox modular polynomial `Φ_m` has integer
coefficients: it is the image of an integer bivariate polynomial under the coefficientwise
map `ℤ → ℂ`.

Cox's proof (pp. 231–232): each elementary symmetric function of the `j(στ)`, `σ ∈ C(m)`,
lies in `ℚ(ζ_m)((q^{1/m}))` by (11.13); the Galois group of `ℚ(ζ_m)/ℚ` permutes the
`j(στ)`, so the symmetric functions lie in `ℚ((q^{1/m}))`; being `SL₂(ℤ)`-periodic with
algebraic-integer coefficients they lie in `ℤ((q))`; and the Hasse q-expansion principle
upgrades `f = A(j)` to `A ∈ ℤ[X]`. -/
theorem modularEquation_integer_descent (m : ℕ+) :
    ∃ Φ : ℤ[X][X],
      Φ.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) = modularEquationComplex m := by
  sorry -- T013: depends on the Galois descent (T012) + Hasse principle (T007); blocked by those

/-- The coefficientwise map `ℤ[X][Y] → ℂ[X][Y]` is injective, so the integer descent in
`modularEquation_integer_descent` is unique. -/
theorem modularPolynomial_descent_injective :
    Function.Injective
      (fun Φ : ℤ[X][X] => Φ.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) := by
  have h1 : Function.Injective (Polynomial.map (Int.castRingHom ℂ)) :=
    Polynomial.map_injective _ Int.cast_injective
  have h2 : Function.Injective ⇑(Polynomial.mapRingHom (Int.castRingHom ℂ)) := by
    simpa [Polynomial.coe_mapRingHom] using h1
  exact Polynomial.map_injective _ h2

/-- The canonical **integer modular polynomial** `Φ_m ∈ ℤ[X][Y]` (Cox Theorem 11.18(i)),
defined as the unique integer descent of the complex Cox product. -/
noncomputable def modularPolynomial (m : ℕ+) : ℤ[X][X] :=
  (modularEquation_integer_descent m).choose

/-- Defining property of `modularPolynomial`: its image under `ℤ → ℂ` is the complex
modular polynomial. -/
theorem modularPolynomial_map_complex (m : ℕ+) :
    (modularPolynomial m).map (Polynomial.mapRingHom (Int.castRingHom ℂ)) =
      modularEquationComplex m :=
  (modularEquation_integer_descent m).choose_spec

end ModularPolynomialInteger


end Test
