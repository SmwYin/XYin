/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldDiagonalHerbrand

/-! # The diagonal exact-sequence quotient

The actual inclusion and quotient projection give q(P)=q(D)q(P/D).
Since q(D)=1/|G| in Janusz's convention, the quotient is |G| times q(P).
-/

noncomputable section
namespace Cox.ClassFieldTheory
open Cox.CyclicCohomology

/-- The actual diagonal quotient has group order times the permutation-module quotient. -/
theorem herbrandQuotient_diagonal_quotient (G X : Type*) [Group G] [Fintype G]
    [Fintype X] [Nonempty X] [MulAction G X]
    (g : G) (hg : ∀ γ, γ ∈ Subgroup.zpowers g) :
    herbrandQuotient ((Representation.ofMulAction ℤ G X).quotient
      (Submodule.span ℤ {diagonalVector ℤ X}) (diagonal_span_stable ℤ G X)) g =
        (Nat.card G : ℚ) * herbrandQuotient (Representation.ofMulAction ℤ G X) g := by
  have hA : FiniteHerbrand (Representation.ofMulAction ℤ G X) g :=
    finiteHerbrand_of_moduleFinite _ g hg
  have hS : FiniteHerbrand ((Representation.ofMulAction ℤ G X).subrepresentation
      (Submodule.span ℤ {diagonalVector ℤ X}) (diagonal_span_stable ℤ G X)) g :=
    finiteHerbrand_of_moduleFinite _ g hg
  haveI : Module.Finite ℤ ((X →₀ ℤ) ⧸ Submodule.span ℤ {diagonalVector ℤ X}) :=
    Module.Finite.quotient ℤ _
  have hQ : FiniteHerbrand ((Representation.ofMulAction ℤ G X).quotient
      (Submodule.span ℤ {diagonalVector ℤ X}) (diagonal_span_stable ℤ G X)) g :=
    finiteHerbrand_of_moduleFinite _ g hg
  have h := herbrandQuotient_mul _ g _ _
    (submoduleIntertwining _ _ (diagonal_span_stable ℤ G X))
    (quotientIntertwining _ _ (diagonal_span_stable ℤ G X))
    (submoduleIntertwining_injective _ _ _) (quotientIntertwining_surjective _ _ _)
    (submodule_sequence_exact _ _ _) hg hS hA hQ
  rw [herbrandQuotient_diagonal_span G X g hg] at h
  have hG : (Nat.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [h, ← mul_assoc, mul_inv_cancel₀ hG, one_mul]
  -- The two sides differ only in the (defeq) integer-module instance on the quotient.
  rfl

end Cox.ClassFieldTheory
