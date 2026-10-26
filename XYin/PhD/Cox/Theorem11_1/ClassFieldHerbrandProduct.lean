/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCohomology
import Mathlib.LinearAlgebra.Prod

/-! # Binary products of cyclic Tate modules

Janusz V.1.3 applies to the native split sequence `0 → A → A × B → B → 0`.
The maps below wrap the existing inclusion and projection linear maps.
-/

noncomputable section

namespace Cox.CyclicCohomology

section Maps

variable {G A B : Type*} [Monoid G] [AddCommGroup A] [AddCommGroup B]
variable (ρ : Representation ℤ G A) (τ : Representation ℤ G B)

/-- The native inclusion of the first factor intertwines the product action. -/
def prodInlIntertwining : ρ.IntertwiningMap (ρ.prod τ) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (LinearMap.inl ℤ A B)
    (by intro γ x; change (ρ γ x, 0) = (ρ γ x, τ γ 0); rw [map_zero])

/-- The native projection onto the second factor intertwines the product action. -/
def prodSndIntertwining : (ρ.prod τ).IntertwiningMap τ :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (LinearMap.snd ℤ A B)
    (by intro γ x; rfl)

end Maps

section Products

variable {G A B : Type*} [Group G] [AddCommGroup A] [AddCommGroup B]
variable (ρ : Representation ℤ G A) (τ : Representation ℤ G B)
variable [Fintype G] (g : G)

/-- The split sequence transfers finiteness of the two Tate groups to the product. -/
theorem finiteHerbrand_prod (hA : FiniteHerbrand ρ g) (hB : FiniteHerbrand τ g) :
    FiniteHerbrand (ρ.prod τ) g := by
  exact finiteHerbrand_of_first_last ρ (ρ.prod τ) τ g (prodInlIntertwining ρ τ)
    (prodSndIntertwining ρ τ) LinearMap.inl_injective LinearMap.snd_surjective
    (LinearMap.range_inl ℤ A B) hA hB

/-- Janusz V.1.3 specialized to the split sequence for a binary product. -/
theorem herbrandQuotient_prod (hg : ∀ γ, γ ∈ Subgroup.zpowers g)
    (hA : FiniteHerbrand ρ g) (hB : FiniteHerbrand τ g) :
    herbrandQuotient (ρ.prod τ) g = herbrandQuotient ρ g * herbrandQuotient τ g := by
  exact herbrandQuotient_mul ρ g (ρ.prod τ) τ (prodInlIntertwining ρ τ)
    (prodSndIntertwining ρ τ) LinearMap.inl_injective LinearMap.snd_surjective
    (LinearMap.range_inl ℤ A B) hg hA (finiteHerbrand_prod ρ τ g hA hB) hB

end Products

end Cox.CyclicCohomology
