/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Algebra.BigOperators.Fin

import XYin.PhD.Cox.Kronecker

/-!
# The Frobenius calculation in Kronecker's congruence

At a prime level and after setting the cyclotomic phase to one, the first `p` Cox roots
coincide with the unit-step reduction of `j`. The remaining root is the `p`-th power of the
width-`p` reduction, i.e. the `p²`-th power of the unit-step one. This file evaluates that
product in characteristic `p` and completes Cox Theorem 11.18(v).
-/

open scoped Polynomial.Bivariate

noncomputable section

namespace Cox

open Polynomial

/-- At phase one, every lower prime-level root is the unit-step reduction of `j`. -/
theorem transformedJSeries_one_primeLower_eq_jUnit
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (i : Fin (p : ℕ)) :
    transformedJSeries (1 : ZMod (p : ℕ)) (primeLowerCoxMatrix p i) =
      jLaurentSeriesWidth (ZMod p) 1 :=
  transformedJSeries_eq_jLaurentSeriesWidth _ _ (one_zpow _)

/-- At prime level and phase one, the formal Cox product has one repeated lower factor and one
distinguished factor. -/
theorem formalCoxPolynomial_prime_one_factorization
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    formalCoxPolynomial p (1 : ZMod (p : ℕ)) =
      (X - C (jLaurentSeriesWidth (ZMod p) 1)) ^ (p : ℕ) *
        (X - C (transformedJSeries (1 : ZMod (p : ℕ)) (sigmaZero p))) := by
  let f : CoxMatrix p → Polynomial (LaurentSeries (ZMod (p : ℕ))) := fun σ ↦
    X - C (transformedJSeries (1 : ZMod (p : ℕ)) σ)
  rw [formalCoxPolynomial]
  calc
    ∏ σ : CoxMatrix p, f σ =
        ∏ i : Fin ((p : ℕ) + 1), f ((primeCoxMatrixEquiv p).symm i) := by
      exact ((primeCoxMatrixEquiv p).symm.prod_comp f).symm
    _ = (∏ i : Fin (p : ℕ),
          f ((primeCoxMatrixEquiv p).symm i.castSucc)) *
          f ((primeCoxMatrixEquiv p).symm (Fin.last (p : ℕ))) := by
      exact Fin.prod_univ_castSucc _
    _ = (∏ _i : Fin (p : ℕ), (X - C (jLaurentSeriesWidth (ZMod p) 1))) *
          (X - C (transformedJSeries (1 : ZMod (p : ℕ)) (sigmaZero p))) := by
      have hcast (i : Fin (p : ℕ)) :
          (primeCoxMatrixEquiv p).symm i.castSucc = primeLowerCoxMatrix p i := by
        simp [primeCoxMatrixEquiv_symm_apply_of_lt p i.castSucc i.isLt]
      simp only [hcast, primeCoxMatrixEquiv_symm_apply_last, f]
      simp_rw [transformedJSeries_one_primeLower_eq_jUnit]
    _ = _ := by rw [Fin.prod_const]

/-- The distinguished root is the `p`-th power of the width-`p` `j`-series. -/
theorem transformedJSeries_one_sigmaZero_eq_jLaurent_pow
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    transformedJSeries (1 : ZMod (p : ℕ)) (sigmaZero p) =
      jLaurentSeriesWidth (ZMod p) p ^ (p : ℕ) := by
  rw [transformedJSeries_eq_jLaurentSeriesWidth _ _ (one_zpow _), jLaurentSeriesWidth_pow_prime]
  congr 1
  exact PNat.eq (sq _)

/-- The prime-level formal Cox product in the Frobenius form used for Kronecker's congruence. -/
theorem formalCoxPolynomial_prime_one_frobenius
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    formalCoxPolynomial p (1 : ZMod (p : ℕ)) =
      (X ^ (p : ℕ) - C (jLaurentSeriesWidth (ZMod p) p)) *
        (X - C (jLaurentSeriesWidth (ZMod p) p ^ (p : ℕ))) := by
  rw [formalCoxPolynomial_prime_one_factorization,
    transformedJSeries_one_sigmaZero_eq_jLaurent_pow, sub_pow_char, ← C_pow,
    jLaurentSeriesWidth_pow_prime, one_mul]

/-- After specializing the parameter (the inner variable `C X`) at the width-`p` `j`-series, the
modular polynomial modulo `p` has the Kronecker factorization. -/
theorem kronecker_after_specializeJ
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    specializeJMod p ((modularPolynomial p).map (mapRingHom (Int.castRingHom (ZMod (p : ℕ))))) =
      specializeJMod p ((Y : (ZMod (p : ℕ))[X][Y]) ^ (p : ℕ) - C X) *
        specializeJMod p (Y - (C X : (ZMod (p : ℕ))[X][Y]) ^ (p : ℕ)) := by
  rw [specializeJMod_modularPolynomial_eq_formal,
    formalCoxPolynomial_prime_one_frobenius]
  simp

/-- Cox Theorem 11.18(v), Kronecker's congruence: Cox's `Φ_p(X, Y) ≡ (X ^ p - Y) (X - Y ^ p)`
modulo `p`, written in the letters of `(ZMod p)[X][Y]`, whose outer variable `Y` is Cox's root
variable `X` and whose inner variable `C X` is Cox's parameter `Y`. -/
theorem theorem_11_18_v
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    (modularPolynomial p).map (mapRingHom (Int.castRingHom (ZMod (p : ℕ)))) =
      (Y ^ (p : ℕ) - C X) * (Y - C X ^ (p : ℕ)) := by
  apply specializeJMod_injective p
  simpa only [map_mul] using kronecker_after_specializeJ p

end Cox
