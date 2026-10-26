/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompleteDVR
import XYin.PhD.Cox.Theorem11_1.ClassFieldHenselBaseChange

/-! # Hensel residue decomposition and its actual lifted factors

Source: Janusz II.3.5, printed p.83/PDF94.
-/

noncomputable section
open Polynomial
namespace Cox.ClassFieldTheory

/-- Lift the actual complementary residue idempotent through finite-free completeness. -/
theorem exists_idempotent_lift_product
    (R A B C : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Free R A] (I : Ideal R) [IsAdicComplete I R]
    [CommRing B] [CommRing C] [Algebra (R ⧸ I) B] [Algebra (R ⧸ I) C]
    (E : (A ⧸ I.map (algebraMap R A)) ≃ₐ[R ⧸ I] B × C) :
    ∃ e : A, IsIdempotentElem e ∧ E (Ideal.Quotient.mk _ e) = (0, 1) := by
  haveI : IsAdicComplete I A := adicComplete_of_finite_free I
  haveI : IsAdicComplete (I.map (algebraMap R A)) A :=
    (IsAdicComplete.map_algebraMap_iff (I := I) (M := A)).mpr inferInstance
  haveI : HenselianRing A (I.map (algebraMap R A)) := IsAdicComplete.henselianRing A _
  have hidem : IsIdempotentElem (E.symm (0, 1)) := by
    change E.symm (0, 1) * E.symm (0, 1) = E.symm (0, 1)
    rw [← map_mul]
    simp
  obtain ⟨a, ha, hmk⟩ := henselian_idempotent_lift (I.map (algebraMap R A)) (E.symm (0, 1)) hidem
  exact ⟨a, ha, by rw [hmk, AlgEquiv.apply_symm_apply]⟩

/-- The characteristic polynomial on an actual product decomposition is the product of the two
component characteristic polynomials. -/
theorem charpoly_lmul_eq_prod_of_algEquiv
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    [Module.Finite R A] [Module.Free R A]
    [Module.Finite R B] [Module.Free R B]
    [Module.Finite R C] [Module.Free R C]
    (E : A ≃ₐ[R] B × C) (x : A) :
    (Algebra.lmul R A x).charpoly =
      (Algebra.lmul R B (E x).1).charpoly * (Algebra.lmul R C (E x).2).charpoly := by
  rw [← charpoly_lmul_algEquiv E x]
  exact charpoly_lmul_prod (E x).1 (E x).2

end Cox.ClassFieldTheory
