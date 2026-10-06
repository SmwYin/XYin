/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldHenselBaseChange
import Mathlib.Algebra.Algebra.Tower

/-! # Hensel residue decomposition and its actual lifted factors

Source: Janusz II.3.5, printed p.83/PDF94.
-/

noncomputable section
open Polynomial
namespace Cox.ClassFieldTheory

/-- The actual residue CRT carries the quotient root to the two factor roots. -/
theorem exists_adjoinRoot_residue_mul_algEquiv
    {R : Type*} [CommRing R] (f : R[X]) (I : Ideal R)
    (g h : (R ⧸ I)[X]) (hfactor : f.map (Ideal.Quotient.mk I) = g * h)
    (hcop : IsCoprime g h) :
    ∃ E : (AdjoinRoot f ⧸ I.map (algebraMap R (AdjoinRoot f))) ≃ₐ[R ⧸ I]
        (AdjoinRoot g) × (AdjoinRoot h),
      E (Ideal.Quotient.mk _ (AdjoinRoot.root f)) =
        (AdjoinRoot.root g, AdjoinRoot.root h) := by
  obtain ⟨E3, hE3⟩ := exists_adjoinRoot_mul_algEquiv g h hcop
  let E1 : (AdjoinRoot f ⧸ I.map (algebraMap R (AdjoinRoot f))) ≃+*
      AdjoinRoot (f.map (Ideal.Quotient.mk I)) :=
    (AdjoinRoot.quotEquivQuotMap f I).toRingEquiv
  let E2 : AdjoinRoot (f.map (Ideal.Quotient.mk I)) ≃+* AdjoinRoot (g * h) :=
    (AdjoinRoot.algEquivOfEq (R ⧸ I) _ _ hfactor).toRingEquiv
  let E : (AdjoinRoot f ⧸ I.map (algebraMap R (AdjoinRoot f))) ≃+*
      (AdjoinRoot g) × (AdjoinRoot h) := E1.trans (E2.trans E3.toRingEquiv)
  have hEmk : ∀ p : R[X], E (Ideal.Quotient.mk _ (AdjoinRoot.mk f p)) =
      (AdjoinRoot.mk g (p.map (Ideal.Quotient.mk I)),
        AdjoinRoot.mk h (p.map (Ideal.Quotient.mk I))) := by
    intro p
    have h1 : E1 (Ideal.Quotient.mk (I.map (algebraMap R (AdjoinRoot f))) (AdjoinRoot.mk f p)) =
        AdjoinRoot.mk (f.map (Ideal.Quotient.mk I)) (p.map (Ideal.Quotient.mk I)) :=
      AdjoinRoot.quotEquivQuotMap_apply_mk f p I
    have h2 : E2 (AdjoinRoot.mk (f.map (Ideal.Quotient.mk I)) (p.map (Ideal.Quotient.mk I))) =
        AdjoinRoot.mk (g * h) (p.map (Ideal.Quotient.mk I)) := by
      change (AdjoinRoot.algEquivOfEq (R ⧸ I) _ _ hfactor).toAlgHom _ = _
      rw [show AdjoinRoot.mk (f.map (Ideal.Quotient.mk I)) (p.map (Ideal.Quotient.mk I)) =
          Polynomial.aeval (AdjoinRoot.root (f.map (Ideal.Quotient.mk I)))
            (p.map (Ideal.Quotient.mk I)) from (AdjoinRoot.aeval_eq _).symm,
        ← Polynomial.aeval_algHom_apply, AlgEquiv.coe_algHom,
        AdjoinRoot.algEquivOfEq_root, AdjoinRoot.aeval_eq]
    calc E (Ideal.Quotient.mk _ (AdjoinRoot.mk f p))
        = E3 (E2 (E1 (Ideal.Quotient.mk _ (AdjoinRoot.mk f p)))) := rfl
      _ = E3 (AdjoinRoot.mk (g * h) (p.map (Ideal.Quotient.mk I))) := by rw [h1, h2]
      _ = _ := hE3 _
  refine ⟨AlgEquiv.ofRingEquiv (f := E) fun x => ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have := hEmk (C r)
    simp only [Polynomial.map_C, AdjoinRoot.mk_C] at this
    exact this
  · have := hEmk X
    simpa using this

end Cox.ClassFieldTheory
