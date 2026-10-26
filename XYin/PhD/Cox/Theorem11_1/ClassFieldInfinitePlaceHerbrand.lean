/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldHerbrandPermutation
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # The infinite-place permutation quotient

Over a totally complex base the pinned forward unramified-stabilizer theorem
makes every actual place stabilizer trivial. The finite orbit product is then one.
No Galois or number-field hypothesis is needed by these three adapters.
-/

open NumberField
noncomputable section
namespace Cox.ClassFieldTheory
open Cox.CyclicCohomology

/-- Every infinite place is unramified over a totally complex base field. -/
theorem infinitePlace_isUnramified_of_totallyComplex
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsTotallyComplex K]
    (w : InfinitePlace L) : w.IsUnramified K := by
  rw [InfinitePlace.isUnramified_iff]
  exact Or.inr (IsTotallyComplex.isComplex _)

/-- The actual automorphism stabilizer of an infinite place over a totally complex base
is trivial. -/
theorem infinitePlace_stabilizer_eq_bot_of_totallyComplex
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsTotallyComplex K]
    (w : InfinitePlace L) : MulAction.stabilizer (L ≃ₐ[K] L) w = ⊥ := by
  exact (infinitePlace_isUnramified_of_totallyComplex K L w).stabilizer_eq_bot

/-- All orbit factors are one for the actual infinite-place permutation module. -/
theorem infinitePlace_permutation_herbrandQuotient
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsTotallyComplex K]
    [Fintype (L ≃ₐ[K] L)] [Finite (InfinitePlace L)]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    herbrandQuotient (Representation.ofMulAction ℤ (L ≃ₐ[K] L) (InfinitePlace L)) σ = 1 := by
  classical
  haveI : Fintype (InfinitePlace L) := Fintype.ofFinite _
  rw [herbrandQuotient_permutation_orbits (L ≃ₐ[K] L) (InfinitePlace L) σ hσ]
  simp [infinitePlace_stabilizer_eq_bot_of_totallyComplex K L]

end Cox.ClassFieldTheory
