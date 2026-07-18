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
  intro hsq
  obtain ⟨r, hr⟩ := hsq.exists_sq
  have hr' : (N : ℤ) = (r : ℤ) ^ 2 := by
    exact_mod_cast hr
  have hkr : k < (r : ℤ) := by
    rw [hr'] at hlo
    exact (sq_lt_sq₀ hk (Int.natCast_nonneg r)).mp hlo
  have hrk : (r : ℤ) < k + 1 := by
    rw [hr'] at hhi
    exact (sq_lt_sq₀ (Int.natCast_nonneg r) (by omega)).mp hhi
  omega

private lemma exists_positive_nonsquare_det_of_even_aux {b : ℤ} (hB : q.B = 2 * b) :
    ∃ (n : ℤ) (N : ℕ+),
      (q.fixingMatrix n).det = (N : ℤ) ∧ ¬ IsSquare (N : ℕ) := by
  let k : ℤ := q.A * q.C - b ^ 2
  have hk : 0 < k := by
    have hd := q.discriminant_neg
    rw [hB] at hd
    dsimp [k]
    nlinarith
  let D : ℤ := k ^ 2 + k
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [sq_nonneg k]
  let N : ℕ+ := ⟨D.toNat, (Int.lt_toNat).mpr hD⟩
  have hN : (N : ℤ) = D := by
    change ((D.toNat : ℕ) : ℤ) = D
    exact Int.toNat_of_nonneg hD.le
  refine ⟨k - b, N, ?_, not_isSquare_of_between_sq_aux hk.le ?_ ?_⟩
  · rw [fixingMatrix_det, hN]
    dsimp [D, k]
    rw [hB]
    ring
  · rw [hN]
    dsimp [D]
    nlinarith
  · rw [hN]
    dsimp [D]
    nlinarith

private lemma exists_positive_nonsquare_det_of_odd_aux {b : ℤ} (hB : q.B = 2 * b + 1) :
    ∃ (n : ℤ) (N : ℕ+),
      (q.fixingMatrix n).det = (N : ℤ) ∧ ¬ IsSquare (N : ℕ) := by
  let k : ℤ := q.A * q.C - b * (b + 1)
  have hk : 0 < k := by
    have hd := q.discriminant_neg
    rw [hB] at hd
    dsimp [k]
    nlinarith
  let D : ℤ := k ^ 2 + 2 * k
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [sq_nonneg k]
  let N : ℕ+ := ⟨D.toNat, (Int.lt_toNat).mpr hD⟩
  have hN : (N : ℤ) = D := by
    change ((D.toNat : ℕ) : ℤ) = D
    exact Int.toNat_of_nonneg hD.le
  refine ⟨k - b, N, ?_, not_isSquare_of_between_sq_aux hk.le ?_ ?_⟩
  · rw [fixingMatrix_det, hN]
    dsimp [D, k]
    rw [hB]
    ring
  · rw [hN]
    dsimp [D]
    nlinarith
  · rw [hN]
    dsimp [D]
    nlinarith

/-- An explicit parity choice gives a positive nonsquare determinant in the family `Mₙ`. -/
theorem exists_positive_nonsquare_det :
    ∃ (n : ℤ) (N : ℕ+),
      (q.fixingMatrix n).det = (N : ℤ) ∧ ¬ IsSquare (N : ℕ) := by
  obtain ⟨b, hB | hB⟩ := Int.even_or_odd' q.B
  · exact exists_positive_nonsquare_det_of_even_aux q hB
  · exact exists_positive_nonsquare_det_of_odd_aux q hB

/-- Every fixing matrix attached to a primitive quadratic equation is primitive. -/
theorem fixingMatrix_content_eq_one (n : ℤ) :
    Matrix.rankTwoContent (q.fixingMatrix n) = 1 := by
  let k := Matrix.rankTwoContent (q.fixingMatrix n)
  have hkn : k ∣ n.natAbs := by
    dsimp [k, Matrix.rankTwoContent, fixingMatrix]
    exact (Nat.gcd_dvd_left _ _).trans
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
  have hkC : k ∣ q.C.natAbs := by
    dsimp [k, Matrix.rankTwoContent, fixingMatrix]
    simpa using (Nat.gcd_dvd_left _ _).trans
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right n.natAbs (-q.C).natAbs))
  have hkA : k ∣ q.A.natAbs := by
    dsimp [k, Matrix.rankTwoContent, fixingMatrix]
    exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hknB : k ∣ (n + q.B).natAbs := by
    dsimp [k, Matrix.rankTwoContent, fixingMatrix]
    exact Nat.gcd_dvd_right _ _
  have hkBInt : (k : ℤ) ∣ q.B := by
    have hknInt : (k : ℤ) ∣ n := Int.natCast_dvd.mpr hkn
    have hknBInt : (k : ℤ) ∣ n + q.B := Int.natCast_dvd.mpr hknB
    simpa using hknBInt.sub hknInt
  have hkB : k ∣ q.B.natAbs := Int.natCast_dvd.mp hkBInt
  apply Nat.eq_one_of_dvd_one
  rw [← q.primitive]
  exact Nat.dvd_gcd (Nat.dvd_gcd hkA hkB) hkC

private lemma coxMatrix_act_eq_smul_aux {n : ℤ} {N : ℕ+} {γ : SL(2, ℤ)}
    {σ : CoxMatrix N} (hmat : γ.1 * q.fixingMatrix n = σ.mobiusMatrix) :
    σ.act τ = γ • τ := by
  apply UpperHalfPlane.ext
  rw [CoxMatrix.coe_act, UpperHalfPlane.coe_specialLinearGroup_apply]
  have h00 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hmat 0) 0)
  have h01 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hmat 0) 1)
  have h10 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hmat 1) 0)
  have h11 := congrArg (fun x : ℤ ↦ (x : ℂ)) (congrFun (congrFun hmat 1) 1)
  simp only [fixingMatrix, CoxMatrix.mobiusMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h01 h10 h11
  push_cast at h00 h01 h10 h11
  have hden : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (γ 1 1 : ℤ)) ≠ 0 := by
    simpa [ModularGroup.denom_apply, algebraMap_int_eq] using
      UpperHalfPlane.denom_ne_zero γ τ
  have hσd : (σ.d : ℂ) ≠ 0 := by
    exact_mod_cast σ.d_pos.ne'
  have hden' : (τ : ℂ) * ((γ 1 0 : ℤ) : ℂ) + (γ 1 1 : ℤ) ≠ 0 := by
    simpa [mul_comm] using hden
  change
    ((σ.a : ℂ) * (τ : ℂ) + (σ.b : ℂ)) / (σ.d : ℂ) =
      ((((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) + (γ 0 1 : ℤ)) /
        (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + (γ 1 1 : ℤ)))
  field_simp [hden', hσd]
  rw [← h00, ← h01, ← h11]
  linear_combination
    ((((γ 0 1 : ℤ) : ℂ) * ((γ 1 0 : ℤ) : ℂ) -
        ((γ 0 0 : ℤ) : ℂ) * ((γ 1 1 : ℤ) : ℂ)) * q.equation) +
      ((((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) ^ 2 +
        ((γ 0 1 : ℤ) : ℂ) * (τ : ℂ)) * h10)

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
  rw [modularPolynomialDiagonal, BivariatePolynomial.diagonal_eval₂,
    Polynomial.eval₂_eval₂RingHom_apply]
  change (BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial N)).eval
    (j τ) (j τ) = 0
  rw [modularPolynomial_map_complex, ← BivariatePolynomial.specializeY_eval,
    modularPolynomialC_specializeY, coxPhiAtJ, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ σ)
  simp [hσ]

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
