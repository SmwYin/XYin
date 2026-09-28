/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.LaurentPolynomialEvaluation
import XYin.PhD.Cox.ModularPolynomial

/-!
# The Laurent leading term of the diagonal modular polynomial

This file formalizes Cox equation (11.19). At the width-`m` cusp, `j` has order `-m`, while
the root indexed by `σ` has order `-σ.a ^ 2`. For nonsquare `m` these orders never agree, so
the leading coefficient of every difference is either `1` or a signed power of `ζ_m`. The
diagonal `Φ_m(X, X)` of Cox's modular polynomial is `(modularPolynomialC m).eval X`.
-/

open UpperHalfPlane

noncomputable section

namespace Cox

/-- For nonsquare `m`, the two possible principal exponents in a diagonal Cox factor are
distinct. This is the leading-term calculation in equation (11.19). -/
theorem cox_diagonal_factor_leadingCoeff (m : ℕ+) (hm : ¬ IsSquare (m : ℕ))
    (σ : CoxMatrix m) :
    (laurentqExpansion ((m : ℕ) : ℝ) j -
        transformedJSeries (zeta m) σ).leadingCoeff =
      if σ.a ^ 2 < (m : ℕ) then 1
      else -(zeta m ^ (-((σ.a : ℤ) * (σ.b : ℤ)))) := by
  have hζ := zeta_ne_zero m
  have horderTop {x : LaurentSeries ℂ} {g : ℤ} (hx : x.leadingCoeff ≠ 0) (hg : x.order = g) :
      x.orderTop = g := by
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero (HahnSeries.leadingCoeff_ne_zero.mp hx), hg]
  have hJ := horderTop (by simp [laurentqExpansion_j_leadingCoeff_widthM])
    (laurentqExpansion_j_order_widthM m)
  have hT := horderTop (by rw [transformedJSeries_leadingCoeff _ hζ]; exact zpow_ne_zero _ hζ)
    (transformedJSeries_order _ hζ σ)
  split_ifs with hlt
  · have hlt' : -(m : ℤ) < -((σ.a : ℤ) ^ 2) := neg_lt_neg (by exact_mod_cast hlt)
    rw [HahnSeries.leadingCoeff_sub (by rw [hJ, hT]; exact_mod_cast hlt'),
      laurentqExpansion_j_leadingCoeff_widthM]
  · have hgt : -((σ.a : ℤ) ^ 2) < -(m : ℤ) := neg_lt_neg <| by
      exact_mod_cast lt_of_le_of_ne (not_lt.1 hlt) fun h ↦ hm ⟨σ.a, by rw [h, sq]⟩
    rw [sub_eq_add_neg, HahnSeries.leadingCoeff_add_eq_right
        (by rw [HahnSeries.orderTop_neg, hJ, hT]; exact_mod_cast hgt),
      HahnSeries.leadingCoeff_neg, transformedJSeries_leadingCoeff _ hζ]

/-- Every diagonal Cox factor has root-of-unity leading coefficient of exponent `2m`. -/
theorem cox_diagonal_factor_leadingCoeff_pow (m : ℕ+) (hm : ¬ IsSquare (m : ℕ))
    (σ : CoxMatrix m) :
    (laurentqExpansion ((m : ℕ) : ℝ) j -
        transformedJSeries (zeta m) σ).leadingCoeff ^ (2 * (m : ℕ)) = 1 := by
  rw [cox_diagonal_factor_leadingCoeff m hm σ]
  split_ifs
  · simp
  · let x := zeta m ^ (-((σ.a : ℤ) * (σ.b : ℤ)))
    have hx : x ^ (m : ℕ) = 1 := by
      dsimp only [x]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        (zeta_isPrimitiveRoot m).zpow_eq_one, one_zpow]
    rw [(even_two_mul (m : ℕ)).neg_pow, Nat.mul_comm, pow_mul, hx, one_pow]

/-- The formal Cox polynomial is obtained from `Φ_m` by substituting the width-`m` Laurent
series of `j` for its parameter (the inner variable). -/
theorem formalCoxPolynomial_eq_modularPolynomialC_map_j (m : ℕ+) :
    formalCoxPolynomial m (zeta m) =
      Polynomial.map
        (Polynomial.eval₂RingHom (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
          (laurentqExpansion ((m : ℕ) : ℝ) j)) (modularPolynomialC m) := by
  ext1 n
  rw [Polynomial.coeff_map, ← coxPhiFunction_coeff_laurentqExpansion_widthM,
    ← modularPolynomialC_coeff_polynomialIn]
  exact laurentqExpansion_polynomial_eval (by positivity)
    (by simpa using (j_cuspData m).meromorphicAt_cuspFunction 1) _

/-- Substituting the width-`m` Laurent series of `j` into the diagonal `Φ_m(X, X)` gives the
product of the diagonal Cox factors. -/
theorem modularPolynomialC_eval_X_eval₂_j (m : ℕ+) :
    ((modularPolynomialC m).eval Polynomial.X).eval₂
        (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
        (laurentqExpansion ((m : ℕ) : ℝ) j) =
      ∏ σ : CoxMatrix m,
        (laurentqExpansion ((m : ℕ) : ℝ) j -
          transformedJSeries (zeta m) σ) := by
  rw [Polynomial.Bivariate.eval₂_eval_X, ← Polynomial.eval_map,
    ← formalCoxPolynomial_eq_modularPolynomialC_map_j]
  simp [formalCoxPolynomial, Polynomial.eval_prod]

/-- Cox equation (11.19): for nonsquare `m`, the leading coefficient of the complex diagonal
`Φ_m(X, X)` has `2m`-th power one. -/
theorem modularPolynomialC_eval_X_leadingCoeff_pow
    (m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) :
    ((modularPolynomialC m).eval Polynomial.X).leadingCoeff ^ (2 * (m : ℕ)) = 1 := by
  rw [← polynomial_eval₂_laurentSeries_leadingCoeff _ m m.pos (laurentqExpansion_j_order_widthM m)
      (laurentqExpansion_j_leadingCoeff_widthM m), modularPolynomialC_eval_X_eval₂_j]
  exact Finset.prod_induction _ (fun F : LaurentSeries ℂ ↦ F.leadingCoeff ^ (2 * (m : ℕ)) = 1)
    (fun a b ha hb ↦ by
      dsimp only at ha hb ⊢
      rw [HahnSeries.leadingCoeff_mul, mul_pow, ha, hb, one_mul])
    (by simp)
    fun σ _ ↦ cox_diagonal_factor_leadingCoeff_pow m hm σ

end Cox
