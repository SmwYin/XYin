/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldDiagonalQuotient
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnitDiagonalLattice
import XYin.PhD.Cox.Theorem11_1.ClassFieldInfinitePlaceHerbrand

/-! # Janusz's global unit Herbrand quotient

Transport the diagonal quotient through the actual exponent-map equivalence,
then use the finite index of the selected unit lattice. Total complexity removes
the infinite-place stabilizer factors; Galois identifies group order with degree.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise
noncomputable section
namespace Cox.ClassFieldTheory
open Cox.CyclicCohomology

/-- The actual unit lattice inherits the diagonal quotient calculation without a Galois
or finite-index hypothesis. -/
theorem unitLattice_herbrandQuotient_eq_card_mul_permutation
    (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L]
    [Fintype (L ≃ₐ[K] L)]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker)
    (hu : ∀ (τ : L ≃ₐ[K] L) w, τ • (u w : Lˣ) = (u (τ • w) : Lˣ))
    (hrel : ∀ a : InfinitePlace L → ℤ,
      (∏ w, u w ^ a w) = 1 ↔ ∃ n : ℤ, ∀ w, a w = n)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    herbrandQuotient ((globalUnitRepresentation K L).subrepresentation
      (unitLatticeSubmodule L u) (unitLatticeSubmodule_stable K L u hu)) σ =
        (Nat.card (L ≃ₐ[K] L) : ℚ) *
          herbrandQuotient
            (Representation.ofMulAction ℤ (L ≃ₐ[K] L) (InfinitePlace L)) σ := by
  obtain ⟨E, -, hE⟩ := exists_unitDiagonalLatticeEquiv K L u hu hrel
  exact (herbrandQuotient_congr σ _ _ E.toAddEquiv hE).symm.trans
    (herbrandQuotient_diagonal_quotient (L ≃ₐ[K] L) (InfinitePlace L) σ hσ)

/-- Janusz V.2.4: the actual global-unit quotient is the extension degree over a totally
complex base. -/
theorem globalUnit_herbrandQuotient
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [hGalois : IsGalois K L] [IsTotallyComplex K]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    herbrandQuotient (globalUnitRepresentation K L) σ = (Module.finrank K L : ℚ) := by
  obtain ⟨u, hu, hrel, hidx⟩ := exists_equivariant_unit_lattice K L
  have hU := globalUnit_finiteHerbrand K L σ hσ
  rw [← unitLattice_herbrandQuotient_eq K L u hu hidx σ hσ hU,
    unitLattice_herbrandQuotient_eq_card_mul_permutation K L u hu hrel σ hσ,
    infinitePlace_permutation_herbrandQuotient K L σ hσ, mul_one]
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  rw [IsGalois.card_aut_eq_finrank]

end Cox.ClassFieldTheory
