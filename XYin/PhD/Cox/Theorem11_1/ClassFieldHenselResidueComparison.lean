/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldHenselBaseChange
import XYin.PhD.Cox.Theorem11_1.ClassFieldHenselResidueFactor
import XYin.PhD.Cox.Theorem11_1.ClassFieldHenselCharpoly

/-! # Comparing the two Hensel residue decompositions
Source: Janusz II.3.5, printed p.83/PDF94.
-/
noncomputable section
open Polynomial
namespace Cox.ClassFieldTheory

/-- The reduced quotient by the lifted idempotent is the specified first residue factor. -/
theorem exists_residue_factor_algEquiv
    (R A B C : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal R) [CommRing B] [CommRing C]
    [Algebra (R ⧸ I) B] [Algebra (R ⧸ I) C]
    (E : (A ⧸ I.map (algebraMap R A)) ≃ₐ[R ⧸ I] B × C)
    (e : A) (he : E (Ideal.Quotient.mk _ e) = (0, 1)) :
    ∃ F : ((A ⧸ Ideal.span {e}) ⧸
        I.map (algebraMap R (A ⧸ Ideal.span {e}))) ≃ₐ[R ⧸ I] B,
      ∀ a : A, F (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a)) =
        (E (Ideal.Quotient.mk _ a)).1 := by
  obtain ⟨E₁, hE₁⟩ := exists_residue_quotient_equiv R A I e
  obtain ⟨F, hF⟩ := exists_quotient_factor_algEquiv (R ⧸ I) (A ⧸ I.map (algebraMap R A)) B C E
    (Ideal.Quotient.mk _ e) he
  refine ⟨E₁.trans F, fun a => ?_⟩
  rw [AlgEquiv.trans_apply, hE₁, hF]

/-- Coefficient reduction of the root-multiplication characteristic polynomial gives the
specified monic residue polynomial. -/
theorem charpoly_lmul_map_eq_of_residue_root
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    (I : Ideal R) (g : (R ⧸ I)[X]) (hg : g.Monic)
    (E : (A ⧸ I.map (algebraMap R A)) ≃ₐ[R ⧸ I] AdjoinRoot g)
    (x : A) (hx : E (Ideal.Quotient.mk _ x) = AdjoinRoot.root g) :
    (Algebra.lmul R A x).charpoly.map (Ideal.Quotient.mk I) = g := by
  haveI := hg.free_adjoinRoot
  haveI := hg.finite_adjoinRoot
  have hq := charpoly_lmul_quotient (R := R) (A := A) I x
  simp only at hq
  rw [← hq]
  letI := Module.Free.of_equiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).symm.toLinearEquiv
  letI := Module.Finite.equiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).symm.toLinearEquiv
  rw [← charpoly_lmul_algEquiv E, hx]
  exact charpoly_adjoinRoot_mul_root g hg

end Cox.ClassFieldTheory
