/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnitDiagonal
import XYin.PhD.Cox.Theorem11_1.ClassFieldCohomology
import Mathlib.RepresentationTheory.Equiv
import Mathlib.Algebra.Module.PUnit

/-! # The diagonal line in the global-unit sequence

The nonzero all-ones line carries the trivial action. Native scalar-to-span and
singleton-permutation equivalences give its Herbrand quotient as the reciprocal
of the group order, in Janusz's H¹/H⁰_Tate convention.
-/

noncomputable section
namespace Cox.ClassFieldTheory
open Cox.CyclicCohomology

/-- A nonempty coordinate set makes the all-ones diagonal vector nonzero. -/
theorem diagonalVector_ne_zero (R X : Type*) [Semiring R] [Nontrivial R]
    [Fintype X] [Nonempty X] : diagonalVector R X ≠ 0 := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx := diagonalVector_apply R X x
  rw [h, Finsupp.zero_apply] at hx
  exact zero_ne_one hx

/-- Every permutation fixes the actual all-ones diagonal vector. -/
theorem diagonalVector_fixed (R G X : Type*) [Semiring R] [Group G]
    [Fintype X] [MulAction G X] (g : G) :
    (Representation.ofMulAction R G X) g (diagonalVector R X) = diagonalVector R X := by
  ext x
  rw [Representation.ofMulAction_apply, diagonalVector_apply, diagonalVector_apply]

/-- The native scalar-to-span map intertwines the trivial action with the diagonal action. -/
theorem toDiagonalSpan_equivariant (R G X : Type*) [Ring R] [IsDomain R] [Group G]
    [Fintype X] [Nonempty X] [MulAction G X] (g : G) (r : R) :
    let e := LinearEquiv.toSpanNonzeroSingleton R (X →₀ R) (diagonalVector R X)
      (diagonalVector_ne_zero R X)
    e ((Representation.trivial R G R) g r) =
      ((Representation.ofMulAction R G X).subrepresentation
        (Submodule.span R {diagonalVector R X}) (diagonal_span_stable R G X)) g (e r) := by
  intro e
  apply Subtype.ext
  simp [e, diagonalVector_fixed]

/-- The trivial integer representation has Janusz quotient equal to the reciprocal group order. -/
theorem herbrandQuotient_trivial_int (G : Type*) [Group G] [Fintype G]
    (g : G) (hg : ∀ γ, γ ∈ Subgroup.zpowers g) :
    herbrandQuotient (Representation.trivial ℤ G ℤ) g = (Nat.card G : ℚ)⁻¹ := by
  let E := Representation.ofMulActionSubsingletonEquivTrivial ℤ G PUnit.{1}
  haveI : MulAction.IsPretransitive G PUnit.{1} := ⟨fun _ _ ↦ ⟨1, Subsingleton.elim _ _⟩⟩
  have hstab : MulAction.stabilizer G PUnit.unit = ⊤ := by
    ext γ
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_top]
  rw [← herbrandQuotient_congr g (Representation.ofMulAction ℤ G PUnit.{1})
      (Representation.trivial ℤ G ℤ) E.toLinearEquiv.toAddEquiv
      (fun γ x ↦ E.toIntertwiningMap.isIntertwining _ _ γ x),
    herbrandQuotient_permutation g PUnit.{1} PUnit.unit hg, hstab, Subgroup.card_top]

/-- The actual diagonal span has the same reciprocal Herbrand quotient as the trivial line. -/
theorem herbrandQuotient_diagonal_span (G X : Type*) [Group G] [Fintype G]
    [Fintype X] [Nonempty X] [MulAction G X]
    (g : G) (hg : ∀ γ, γ ∈ Subgroup.zpowers g) :
    herbrandQuotient ((Representation.ofMulAction ℤ G X).subrepresentation
      (Submodule.span ℤ {diagonalVector ℤ X}) (diagonal_span_stable ℤ G X)) g =
        (Nat.card G : ℚ)⁻¹ := by
  let e := LinearEquiv.toSpanNonzeroSingleton ℤ (X →₀ ℤ) (diagonalVector ℤ X)
    (diagonalVector_ne_zero ℤ X)
  rw [← herbrandQuotient_congr g (Representation.trivial ℤ G ℤ) _ e.toAddEquiv
      (fun γ r ↦ toDiagonalSpan_equivariant ℤ G X γ r),
    herbrandQuotient_trivial_int G g hg]

end Cox.ClassFieldTheory
