/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Arithmetic

/-!
# Algebraic integrality of singular moduli

This file formalizes Report Theorem 5.9.  A primitive negative-discriminant quadratic equation
for `τ` produces a primitive positive-determinant matrix fixing `τ`.  Reducing that matrix to a
Cox representative makes `j(τ)` a root of the integral diagonal modular polynomial, whose leading
coefficient is `±1` at the constructed nonsquare level.
-/

open Complex MatrixGroups UpperHalfPlane
open scoped Polynomial.Bivariate

noncomputable section

namespace Cox

/-- A normalized integral quadratic equation for a point of the upper half-plane. -/
structure PrimitiveQuadraticEquation (τ : ℍ) where
  /-- The quadratic coefficient. -/
  A : ℤ
  /-- The linear coefficient. -/
  B : ℤ
  /-- The constant coefficient. -/
  C : ℤ
  equation : (A : ℂ) * (τ : ℂ) ^ 2 + (B : ℂ) * τ + C = 0
  discriminant_neg : B ^ 2 - 4 * A * C < 0
  primitive : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1

/-- An upper-half-plane point is imaginary quadratic when it has a primitive integral quadratic
equation of negative discriminant. -/
def IsImaginaryQuadratic (τ : ℍ) : Prop :=
  Nonempty (PrimitiveQuadraticEquation τ)

/-- A singular modulus is an analytic `j`-value at an imaginary-quadratic point. -/
def IsSingularModulus (z : ℂ) : Prop :=
  ∃ τ : ℍ, IsImaginaryQuadratic τ ∧ z = j τ

namespace PrimitiveQuadraticEquation

variable {τ : ℍ} (q : PrimitiveQuadraticEquation τ)

/-- The integer matrix `Mₙ` used in the proof of Report Theorem 5.9. -/
def fixingMatrix (n : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![n, -q.C; q.A, n + q.B]

@[simp]
theorem fixingMatrix_det (n : ℤ) :
    (q.fixingMatrix n).det = n ^ 2 + q.B * n + q.A * q.C := by
  simp [fixingMatrix, Matrix.det_fin_two_of]
  ring

private lemma not_isSquare_of_between_sq_aux {k : ℤ} {N : ℕ} (hk : 0 ≤ k)
    (hlo : k ^ 2 < (N : ℤ)) (hhi : (N : ℤ) < (k + 1) ^ 2) :
    ¬ IsSquare N := by
  lift k to ℕ using hk
  rintro ⟨r, rfl⟩
  exact Nat.not_exists_sq' (by exact_mod_cast hlo) (by exact_mod_cast hhi) ⟨r, sq r⟩

/-- An explicit choice of `n` gives a positive nonsquare determinant in the family `Mₙ`: writing
`B = 2b + e` with `e ∈ {0, 1}` and `k = AC - b(b + e) > 0`, the determinant of `M_{k-b}` is
`k² + (e + 1)k`, strictly between `k²` and `(k + 1)²`. -/
theorem exists_positive_nonsquare_det :
    ∃ (n : ℤ) (N : ℕ+),
      (q.fixingMatrix n).det = (N : ℤ) ∧ ¬ IsSquare (N : ℕ) := by
  obtain ⟨b, e, hB, he0, he1⟩ : ∃ b e : ℤ, q.B = 2 * b + e ∧ 0 ≤ e ∧ e ≤ 1 :=
    ⟨q.B / 2, q.B % 2, by omega, by omega, by omega⟩
  set k := q.A * q.C - b * (b + e) with hk_def
  have hk : 0 < k := by
    have hd := q.discriminant_neg
    rw [hB] at hd
    nlinarith [sq_nonneg e]
  have hD : 0 < k ^ 2 + (e + 1) * k := by nlinarith
  refine ⟨k - b, ⟨(k ^ 2 + (e + 1) * k).toNat, Int.lt_toNat.mpr hD⟩, ?_,
    not_isSquare_of_between_sq_aux hk.le ?_ ?_⟩ <;>
    simp only [PNat.mk_coe, Int.toNat_of_nonneg hD.le]
  · rw [fixingMatrix_det, hB, hk_def]
    ring
  · nlinarith
  · nlinarith

/-- Every fixing matrix attached to a primitive quadratic equation is primitive. -/
theorem fixingMatrix_content_eq_one (n : ℤ) :
    Matrix.rankTwoContent (q.fixingMatrix n) = 1 := by
  rw [fixingMatrix, Matrix.rankTwoContent_fin_two_of, Int.natAbs_neg]
  calc
    _ = Nat.gcd (Int.gcd n (n + q.B)) (Nat.gcd q.A.natAbs q.C.natAbs) := by
      unfold Int.gcd
      ac_rfl
    _ = Nat.gcd n.natAbs (Nat.gcd (Nat.gcd q.A.natAbs q.B.natAbs) q.C.natAbs) := by
      rw [add_comm n q.B, Int.gcd_add_self_right]
      unfold Int.gcd
      ac_rfl
    _ = 1 := by rw [q.primitive]; simp

private lemma coxMatrix_act_eq_smul_aux {n : ℤ} {N : ℕ+} {γ : SL(2, ℤ)}
    {σ : CoxMatrix N} (hmat : γ.1 * q.fixingMatrix n = σ.mobiusMatrix) :
    σ.act τ = γ • τ := by
  refine σ.act_eq_smul_of_mul_eq hmat τ τ ?_
  have hA : (q.A : ℂ) ≠ 0 := by
    have hd := q.discriminant_neg
    refine Int.cast_ne_zero.2 fun hA ↦ ?_
    rw [hA] at hd
    nlinarith [sq_nonneg q.B]
  have hden : (q.A : ℂ) * τ + ((n + q.B : ℤ) : ℂ) ≠ 0 := fun h ↦ hA <| by
    simpa [τ.im_pos.ne'] using congrArg Complex.im h
  simp only [fixingMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [eq_div_iff hden]
  push_cast
  linear_combination q.equation

include q

/-- At a positive nonsquare level, one Cox transform has the same `j`-value as the fixed point. -/
theorem exists_nonsquare_coxMatrix_j_eq :
    ∃ N : ℕ+, ¬ IsSquare (N : ℕ) ∧
      ∃ σ : CoxMatrix N, j (σ.act τ) = j τ := by
  obtain ⟨n, N, hdet, hN⟩ := exists_positive_nonsquare_det q
  obtain ⟨γ, σ, hmat⟩ := exists_sl2_mul_eq_coxMatrix
    (q.fixingMatrix n) hdet (fixingMatrix_content_eq_one q n)
  refine ⟨N, hN, σ, ?_⟩
  rw [coxMatrix_act_eq_smul_aux q hmat, j_modularGroup_smul]

end PrimitiveQuadraticEquation

/-- The diagonal integral modular polynomial vanishes at an imaginary-quadratic `j`-value for
some nonsquare level. -/
theorem exists_nonsquare_modularPolynomialDiagonal_root {τ : ℍ}
    (hτ : IsImaginaryQuadratic τ) :
    ∃ N : ℕ+, ¬ IsSquare (N : ℕ) ∧
      (modularPolynomialDiagonal N).eval₂ (Int.castRingHom ℂ) (j τ) = 0 := by
  obtain ⟨q⟩ := hτ
  obtain ⟨N, hN, σ, hσ⟩ := q.exists_nonsquare_coxMatrix_j_eq
  refine ⟨N, hN, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, modularPolynomialDiagonal,
    ← Polynomial.map_mapRingHom_eval_map, Polynomial.map_X, Polynomial.Bivariate.eval_eval_X,
    modularPolynomial_map_complex]
  simpa [hσ] using modularPolynomialC_evalEval_j_act N σ τ

/-- Report Theorem 5.9: the `j`-value of an imaginary-quadratic point is integral over `ℤ`. -/
theorem isIntegral_j_of_isImaginaryQuadratic {τ : ℍ}
    (hτ : IsImaginaryQuadratic τ) : IsIntegral ℤ (j τ) := by
  obtain ⟨N, hN, hroot⟩ := exists_nonsquare_modularPolynomialDiagonal_root hτ
  obtain hlc | hlc := theorem_11_18_iv_leadingCoeff N hN
  · refine ⟨modularPolynomialDiagonal N, Polynomial.Monic.def.mpr hlc, ?_⟩
    simpa only [Polynomial.aeval_def] using hroot
  · refine ⟨-(modularPolynomialDiagonal N), ?_, ?_⟩
    · rw [Polynomial.Monic.def, Polynomial.leadingCoeff_neg, hlc, neg_neg]
    · have hroot' : (modularPolynomialDiagonal N).eval₂
          (algebraMap ℤ ℂ) (j τ) = 0 := by
        simpa using hroot
      rw [Polynomial.eval₂_neg, hroot', neg_zero]

/-- Every singular modulus is an algebraic integer. -/
theorem singularModulus_isIntegral {z : ℂ} (hz : IsSingularModulus z) :
    IsIntegral ℤ z := by
  obtain ⟨τ, hτ, rfl⟩ := hz
  exact isIntegral_j_of_isImaginaryQuadratic hτ

end Cox
