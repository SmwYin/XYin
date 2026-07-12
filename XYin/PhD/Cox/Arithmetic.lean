import XYin.PhD.Cox.CyclicSublattice

/-!
# Arithmetic of the modular polynomial: Cox Theorem 11.18
-/

open UpperHalfPlane

noncomputable section

namespace Cox

/-- Theorem 11.18(i), retained as a named theorem although the chosen object itself already
lives in `ℤ[Y][X]`. -/
theorem theorem_11_18_i (m : ℕ+) :
    BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m) =
      modularPolynomialC m := by
  sorry

/-- Theorem 11.18(ii): irreducibility as a polynomial in the root variable `X`, over the
coefficient field `ℂ(Y)`. -/
theorem theorem_11_18_ii (m : ℕ+) :
    Irreducible (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      (modularPolynomialC m)) := by
  sorry

/-- Geometric divisibility input for symmetry: Theorem 11.23 and the dual cyclic sublattice
show that swapping the two variables preserves the modular curve. -/
theorem modularPolynomial_dvd_swap (m : ℕ+) (hm : 1 < (m : ℕ)) :
    modularPolynomial m ∣ Polynomial.Bivariate.swap (modularPolynomial m) := by
  sorry

/-- Theorem 11.18(iii).  This internal proof replaces Cox's unavailable Lang citation by
Theorem 11.23, dual cyclic sublattices, irreducibility, and the monic normalization. -/
theorem theorem_11_18_iii (m : ℕ+) (hm : 1 < (m : ℕ)) :
    Polynomial.Bivariate.swap (modularPolynomial m) = modularPolynomial m := by
  sorry

/-- The diagonal polynomial `Φ_m(X,X)`. -/
def modularPolynomialDiagonal (m : ℕ+) : Polynomial ℤ :=
  BivariatePolynomial.diagonal (modularPolynomial m)

/-- Cox equation (11.19): before integrality is used, the leading diagonal coefficient is a
root of unity. -/
theorem modularPolynomialDiagonal_leadingCoeff_isRootOfUnity
    (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) :
    ∃ k : ℕ, 0 < k ∧ (modularPolynomialDiagonal m).leadingCoeff ^ k = 1 := by
  sorry

/-- Theorem 11.18(iv), degree assertion. -/
theorem theorem_11_18_iv_degree (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) :
    1 < (modularPolynomialDiagonal m).natDegree := by
  sorry

/-- Theorem 11.18(iv), leading coefficient assertion. -/
theorem theorem_11_18_iv_leadingCoeff (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) :
    (modularPolynomialDiagonal m).leadingCoeff = 1 ∨
      (modularPolynomialDiagonal m).leadingCoeff = -1 := by
  sorry

/-- For a prime `p`, Cox's representatives are the `p` matrices `(1 i;0 p)` together with
`(p 0;0 1)`. -/
noncomputable def primeCoxMatrixEquiv (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    CoxMatrix p ≃ Fin ((p : ℕ) + 1) := by
  sorry

/-- The reduction modulo `p` of the integral Laurent series of `j`. -/
noncomputable def jLaurentSeriesMod (p : ℕ+) : LaurentSeries (ZMod (p : ℕ)) := by
  sorry

/-- Substitution `Y ↦ j(q)` modulo `p`, coefficientwise in the root variable `X`. -/
noncomputable def specializeJMod (p : ℕ+) :
    BivariatePolynomial (ZMod (p : ℕ)) →+*
      Polynomial (LaurentSeries (ZMod (p : ℕ))) := by
  sorry

/-- Exercise 11.15, the coefficientwise Hasse q-expansion principle modulo `p`. -/
theorem specializeJMod_injective (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    Function.Injective (specializeJMod p) := by
  sorry

/-- Equations (11.20)–(11.21) and Exercise 11.13, assembled before applying Hasse
injectivity. -/
theorem kronecker_after_specializeJ (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    specializeJMod p
        (BivariatePolynomial.map (Int.castRingHom (ZMod (p : ℕ)))
          (modularPolynomial p)) =
      specializeJMod p
        ((BivariatePolynomial.varX : BivariatePolynomial (ZMod (p : ℕ))) ^ (p : ℕ) -
            BivariatePolynomial.varY) *
        specializeJMod p
          (BivariatePolynomial.varX -
            (BivariatePolynomial.varY : BivariatePolynomial (ZMod (p : ℕ))) ^ (p : ℕ)) := by
  sorry

/-- Theorem 11.18(v), Kronecker's congruence. -/
theorem theorem_11_18_v (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    BivariatePolynomial.map (Int.castRingHom (ZMod (p : ℕ))) (modularPolynomial p) =
      ((BivariatePolynomial.varX : BivariatePolynomial (ZMod (p : ℕ))) ^ (p : ℕ) -
          BivariatePolynomial.varY) *
        (BivariatePolynomial.varX -
          (BivariatePolynomial.varY : BivariatePolynomial (ZMod (p : ℕ))) ^ (p : ℕ)) := by
  sorry

/-- Cox's explicit polynomial (11.22). -/
def modularPolynomialThreeExplicit : BivariatePolynomial ℤ :=
  let X : BivariatePolynomial ℤ := BivariatePolynomial.varX
  let Y : BivariatePolynomial ℤ := BivariatePolynomial.varY
  X * (X + 2 ^ 15 * 3 * 5 ^ 3) ^ 3 +
  Y * (Y + 2 ^ 15 * 3 * 5 ^ 3) ^ 3 -
  X ^ 3 * Y ^ 3 +
  2 ^ 3 * 3 ^ 2 * 31 * X ^ 2 * Y ^ 2 * (X + Y) -
  2 ^ 2 * 3 ^ 3 * 9907 * X * Y * (X ^ 2 + Y ^ 2) +
  2 * 3 ^ 4 * 13 * 193 * 6367 * X ^ 2 * Y ^ 2 +
  2 ^ 16 * 3 ^ 5 * 5 ^ 3 * 17 * 263 * X * Y * (X + Y) -
  2 ^ 31 * 5 ^ 6 * 22973 * X * Y

theorem modularPolynomial_three :
    modularPolynomial (3 : ℕ+) = modularPolynomialThreeExplicit := by
  sorry

end Cox
