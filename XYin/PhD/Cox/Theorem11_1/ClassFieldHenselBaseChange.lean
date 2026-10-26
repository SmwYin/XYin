/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldHenselCharpoly
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Residue and product comparisons for Hensel factor lifting

Janusz II.3.5, printed p.83/PDF94, compares the characteristic polynomials in isomorphic algebras,
reduces coefficients, and applies the coprime residue CRT.
-/

noncomputable section
open Polynomial
open scoped TensorProduct
namespace Cox.ClassFieldTheory

/-- The actual algebra isomorphism transports multiplication characteristic polynomials. -/
theorem charpoly_lmul_algEquiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Free R A] [Module.Finite R A]
    [Module.Free R B] [Module.Finite R B] (E : A ≃ₐ[R] B) (a : A) :
    (Algebra.lmul R B (E a)).charpoly = (Algebra.lmul R A a).charpoly := by
  have h : Algebra.lmul R B (E a) = E.toLinearEquiv.conj (Algebra.lmul R A a) := by
    ext b
    simp [LinearEquiv.conj_apply]
  rw [h, LinearEquiv.charpoly_conj]

/-- Reduction of a finite free algebra reduces the actual multiplication characteristic
polynomial. -/
theorem charpoly_lmul_quotient {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A] (I : Ideal R) (a : A) :
    let E := Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I
    letI := Module.Free.of_equiv E.symm.toLinearEquiv
    letI := Module.Finite.equiv E.symm.toLinearEquiv
    (Algebra.lmul (R ⧸ I) (A ⧸ I.map (algebraMap R A))
      (Ideal.Quotient.mk (I.map (algebraMap R A)) a)).charpoly =
        (Algebra.lmul R A a).charpoly.map (Ideal.Quotient.mk I) := by
  intro E
  letI := Module.Free.of_equiv E.symm.toLinearEquiv
  letI := Module.Finite.equiv E.symm.toLinearEquiv
  have h1 := charpoly_lmul_algEquiv E (Ideal.Quotient.mk (I.map (algebraMap R A)) a)
  have hE : E (Ideal.Quotient.mk (I.map (algebraMap R A)) a) = (1 : R ⧸ I) ⊗ₜ[R] a := rfl
  rw [← h1, hE, ← Algebra.baseChange_lmul, LinearMap.charpoly_baseChange]
  rfl

/-- Coprime factors give the actual product of AdjoinRoot algebras. -/
theorem exists_adjoinRoot_mul_algEquiv {R : Type*} [CommRing R]
    (g h : R[X]) (hcop : IsCoprime g h) :
    ∃ E : AdjoinRoot (g * h) ≃ₐ[R] (AdjoinRoot g) × (AdjoinRoot h),
      ∀ p : R[X], E (AdjoinRoot.mk (g * h) p) =
        (AdjoinRoot.mk g p, AdjoinRoot.mk h p) := by
  have hcop' : IsCoprime (Ideal.span {g}) (Ideal.span {h}) :=
    (Ideal.isCoprime_span_singleton_iff g h).mpr hcop
  have hmul : Ideal.span {g * h} = Ideal.span {g} * Ideal.span {h} :=
    (Ideal.span_singleton_mul_span_singleton g h).symm
  let E₀ : AdjoinRoot (g * h) ≃+* (AdjoinRoot g) × (AdjoinRoot h) :=
    (Ideal.quotEquivOfEq hmul).trans (Ideal.quotientMulEquivQuotientProd _ _ hcop')
  have hE₀ : ∀ p : R[X], E₀ (AdjoinRoot.mk (g * h) p) = (AdjoinRoot.mk g p, AdjoinRoot.mk h p) :=
    fun p => rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := E₀) fun r => ?_, hE₀⟩
  change E₀ (AdjoinRoot.mk (g * h) (C r)) = _
  rw [hE₀]
  rfl

end Cox.ClassFieldTheory
