/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnitLatticeCohomology

/-! # The actual unit lattice as a diagonal quotient

The existing exponent-map quotient equivalence is transported to the actual
submodule of global units. Its representative map and equivariance refer to one
shared equivalence. No Herbrand quotient is computed here.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise
noncomputable section
namespace Cox.ClassFieldTheory

/-- The actual exponent-map range consists of global units. -/
theorem unitExponentMap_range_le_globalUnitSubmodule (L : Type*) [Field L] [NumberField L]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker) :
    LinearMap.range (unitExponentMap L u) ≤ globalUnitSubmodule L := by
  rw [unitExponentMap, Finsupp.range_linearCombination, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact (u w).2

/-- One diagonal-quotient equivalence has the specified representative map and inherited action. -/
theorem exists_unitDiagonalLatticeEquiv (K L : Type*) [Field K] [Field L]
    [NumberField L] [Algebra K L]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker)
    (hu : ∀ (σ : L ≃ₐ[K] L) w, σ • (u w : Lˣ) = (u (σ • w) : Lˣ))
    (hrel : ∀ a : InfinitePlace L → ℤ,
      (∏ w, u w ^ a w) = 1 ↔ ∃ n : ℤ, ∀ w, a w = n) :
    ∃ E : ((InfinitePlace L →₀ ℤ) ⧸
        Submodule.span ℤ {diagonalVector ℤ (InfinitePlace L)}) ≃ₗ[ℤ]
          unitLatticeSubmodule L u,
      (∀ f, ((E (Submodule.Quotient.mk f) : globalUnitSubmodule L) : Additive Lˣ) =
        unitExponentMap L u f) ∧
      ∀ (σ : L ≃ₐ[K] L) q,
        E (((Representation.ofMulAction ℤ (L ≃ₐ[K] L) (InfinitePlace L)).quotient
          (Submodule.span ℤ {diagonalVector ℤ (InfinitePlace L)})
          (diagonal_span_stable ℤ (L ≃ₐ[K] L) (InfinitePlace L))) σ q) =
            ((globalUnitRepresentation K L).subrepresentation (unitLatticeSubmodule L u)
              (unitLatticeSubmodule_stable K L u hu)) σ (E q) := by
  obtain ⟨E, hE, hσ⟩ := exists_unitDiagonalQuotientEquiv K L u hu hrel
  refine ⟨E.trans (Submodule.comapSubtypeEquivOfLe
    (unitExponentMap_range_le_globalUnitSubmodule L u)).symm, fun f => hE f, fun σ q => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hσ σ q

end Cox.ClassFieldTheory
