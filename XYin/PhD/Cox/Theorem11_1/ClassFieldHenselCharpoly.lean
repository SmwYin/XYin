/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Characteristic polynomials in Hensel factor lifting

Janusz II.3.5, printed p.83/PDF94: the root acts on R[X]/(f) with characteristic polynomial f, and
the characteristic polynomial multiplies over the two factors.
-/

noncomputable section
open Polynomial Algebra Matrix
namespace Cox.ClassFieldTheory

/-- The monic relation defining AdjoinRoot is the actual root minimal polynomial. -/
theorem minpoly_adjoinRoot_of_monic {R : Type*} [CommRing R]
    (f : R[X]) (hf : f.Monic) : minpoly R (AdjoinRoot.root f) = f := by
  cases subsingleton_or_nontrivial R
  · subsingleton
  refine (minpoly.unique' R (AdjoinRoot.root f) hf
    (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) fun q hq => ?_).symm
  rw [or_iff_not_imp_left]
  intro hq0 hroot
  have h := (AdjoinRoot.powerBasis' hf).dim_le_degree_of_root hq0 hroot
  rw [AdjoinRoot.powerBasis'_dim] at h
  exact lt_irrefl _ (h.trans_lt (hq.trans_eq (Polynomial.degree_eq_natDegree hf.ne_zero)))

/-- Multiplication by the actual adjoined root has the defining characteristic polynomial. -/
theorem charpoly_adjoinRoot_mul_root {R : Type*} [CommRing R]
    (f : R[X]) (hf : f.Monic) :
    letI := hf.free_adjoinRoot
    letI := hf.finite_adjoinRoot
    (Algebra.lmul R (AdjoinRoot f) (AdjoinRoot.root f)).charpoly = f := by
  letI := hf.free_adjoinRoot
  letI := hf.finite_adjoinRoot
  cases subsingleton_or_nontrivial R
  · subsingleton
  rw [← LinearMap.charpoly_toMatrix _ (AdjoinRoot.powerBasis' hf).basis,
    ← Algebra.leftMulMatrix_apply,
    show AdjoinRoot.root f = (AdjoinRoot.powerBasis' hf).gen from rfl, charpoly_leftMulMatrix,
    ← show AdjoinRoot.root f = (AdjoinRoot.powerBasis' hf).gen from rfl,
    minpoly_adjoinRoot_of_monic f hf]

/-- Multiplication on a product algebra has the product characteristic polynomial. -/
theorem charpoly_lmul_prod {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Free R A] [Module.Finite R A]
    [Module.Free R B] [Module.Finite R B] (a : A) (b : B) :
    (Algebra.lmul R (A × B) (a, b)).charpoly =
      (Algebra.lmul R A a).charpoly * (Algebra.lmul R B b).charpoly := by
  have h : Algebra.lmul R (A × B) (a, b) = (Algebra.lmul R A a).prodMap (Algebra.lmul R B b) := by
    ext x <;> simp
  rw [h, LinearMap.charpoly_prodMap]

end Cox.ClassFieldTheory
