/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.HermiteNormalForm.Content
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Reversing matrix coordinates for Cox's lattice convention

Cox writes periods in the order `[1, τ]`, while its fractional linear transformation uses
the coefficient of `τ` first. Transposing and reversing both index orders converts the
inclusion coordinates to the row matrix. This coordinate conversion has no role in the
construction of row Hermite normal form.
-/

namespace Matrix

variable {n : ℕ} {R : Type*}

/-- Transpose a matrix and reverse both finite index orders. -/
def antiTranspose (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Aᵀ.submatrix Fin.rev Fin.rev

@[simp]
theorem antiTranspose_apply (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    A.antiTranspose i j = A j.rev i.rev := rfl

theorem antiTranspose_eq_submatrix_transpose (A : Matrix (Fin n) (Fin n) R) :
    A.antiTranspose = (A.submatrix Fin.revPerm Fin.revPerm)ᵀ := rfl

@[simp]
theorem antiTranspose_antiTranspose (A : Matrix (Fin n) (Fin n) R) :
    A.antiTranspose.antiTranspose = A := by
  ext i j
  simp

theorem antiTranspose_mul [CommSemiring R] (A B : Matrix (Fin n) (Fin n) R) :
    (A * B).antiTranspose = B.antiTranspose * A.antiTranspose := by
  change (A * B)ᵀ.submatrix Fin.revPerm Fin.revPerm = _
  rw [transpose_mul]
  exact (submatrix_mul_equiv Bᵀ Aᵀ Fin.revPerm Fin.revPerm Fin.revPerm).symm

@[simp]
theorem det_antiTranspose [CommRing R] (A : Matrix (Fin n) (Fin n) R) :
    A.antiTranspose.det = A.det := by
  change (Aᵀ.submatrix Fin.revPerm Fin.revPerm).det = A.det
  simp

theorem content_antiTranspose (A : Matrix (Fin n) (Fin n) ℤ) :
    A.antiTranspose.content = A.content := by
  change (Aᵀ.submatrix Fin.revPerm Fin.revPerm).content = A.content
  rw [content_submatrix_equiv, content_transpose]

end Matrix

namespace Matrix.SpecialLinearGroup

variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]

theorem mul_coe_mul_coe_inv (A : Matrix n n R) (U : SpecialLinearGroup n R) :
    A * U.1 * (U⁻¹ : SpecialLinearGroup n R).1 = A := by
  simpa only [coe_mul, coe_one, Matrix.mul_one] using
    (Matrix.mul_assoc A U.1 (U⁻¹).1).trans
      (congrArg (fun V : SpecialLinearGroup n R ↦ A * V.1) (mul_inv_cancel U))

theorem coe_mul_coe_inv_mul (U : SpecialLinearGroup n R) (A : Matrix n n R) :
    U.1 * ((U⁻¹ : SpecialLinearGroup n R).1 * A) = A := by
  simpa only [coe_mul, coe_one, Matrix.one_mul] using
    (Matrix.mul_assoc U.1 (U⁻¹).1 A).symm.trans
      (congrArg (fun V : SpecialLinearGroup n R ↦ V.1 * A) (mul_inv_cancel U))

end Matrix.SpecialLinearGroup
