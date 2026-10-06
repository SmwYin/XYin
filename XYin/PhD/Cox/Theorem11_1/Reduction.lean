/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Algebra.CharP.Reduced
import XYin.PhD.Cox.KroneckerFrobenius

/-!
# Residue calculations in Cox Theorem 11.1

These declarations record the local algebra portion of the proof. They are not a proof of Theorem
11.1. The order and class-field prerequisites are tracked separately in
`.mathlib-quality/cox11-1/decomposition.md`.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace Cox

/-- Cox, proof of Theorem 11.1, pp. 238–239: Kronecker's congruence in characteristic `p`. -/
theorem modularPolynomial_evalEval_charP {R : Type*} [CommRing R]
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] [CharP R (p : ℕ)] (x y : R) :
    ((modularPolynomial p).map (mapRingHom (Int.castRingHom R))).evalEval y x =
      (x ^ (p : ℕ) - y) * (x - y ^ (p : ℕ)) := by
  have hfac : Int.castRingHom R =
      (ZMod.castHom (dvd_refl (p : ℕ)) R).comp (Int.castRingHom (ZMod (p : ℕ))) :=
    RingHom.ext_int _ _
  rw [hfac, ← Polynomial.mapRingHom_comp, ← Polynomial.map_map, theorem_11_18_v]
  simp [Polynomial.evalEval]

/-- Cox, proof of Theorem 11.1, p. 238, equation (11.30). -/
theorem pow_eq_of_modularPolynomial_diagonal_root {R : Type*} [CommRing R] [IsDomain R]
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] [CharP R (p : ℕ)] {x : R}
    (hx : ((modularPolynomial p).map (mapRingHom (Int.castRingHom R))).evalEval x x = 0) :
    x ^ (p : ℕ) = x := by
  rw [modularPolynomial_evalEval_charP] at hx
  have h : (x ^ (p : ℕ) - x) ^ 2 = 0 := by linear_combination -hx
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)

/-- Cox, proof of Theorem 11.1, p. 239, the deduction from (11.32) and (11.33). -/
theorem eq_of_modularPolynomial_root_of_pow_eq {R : Type*} [CommRing R] [IsDomain R]
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] [CharP R (p : ℕ)] {x y : R}
    (hxy : ((modularPolynomial p).map (mapRingHom (Int.castRingHom R))).evalEval y x = 0)
    (hy : y ^ (p : ℕ) = y) : x = y := by
  rw [modularPolynomial_evalEval_charP, hy] at hxy
  rcases mul_eq_zero.mp hxy with h | h
  · have h' : frobenius R p x = frobenius R p y := by
      rw [frobenius_def, frobenius_def, hy]
      exact sub_eq_zero.mp h
    exact frobenius_inj R p h'
  · exact sub_eq_zero.mp h

end Cox
