/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Restriction and uniqueness of residue congruences

These generic adapters realize the two steps in Janusz III.3.1, printed 104: restrict the same
residue-power congruence to the lower field, then compare its automorphism using trivial inertia.
-/
open NumberField
noncomputable section
namespace Cox.ClassFieldTheory

/-- Janusz III.3.1, printed 104: a residue-power congruence contracts along normal restriction. -/
theorem residue_pow_congruence_restrict
    (K L F : Type*) [Field K] [Field L] [Field F]
    [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F] [Normal K L]
    (σ : F ≃ₐ[K] F) (P : Ideal (𝓞 F)) (N : ℕ)
    (hσ : ∀ x : 𝓞 F, RingOfIntegers.mapRingHom σ.toRingHom x - x ^ N ∈ P) :
    ∀ x : 𝓞 L,
      RingOfIntegers.mapRingHom (σ.restrictNormal L).toRingHom x - x ^ N ∈
        P.under (𝓞 L) := by
  intro x
  have h := hσ (algebraMap (𝓞 L) (𝓞 F) x)
  rw [Ideal.under_def, Ideal.mem_comap, map_sub, map_pow]
  convert h using 2
  apply RingOfIntegers.ext
  exact σ.restrictNormal_commutes L (x : L)

/-- Janusz III.3.1, printed 104: trivial inertia makes residue action determine
the group element. -/
theorem eq_of_sub_mem_of_inertia_eq_bot
    {G M : Type*} [Group G] [AddGroup M] [MulAction G M]
    (I : AddSubgroup M) (hI : I.inertia G = ⊥) (σ τ : G)
    (hστ : ∀ x : M, σ • x - τ • x ∈ I) : σ = τ := by
  rw [← mul_inv_eq_one, ← Subgroup.mem_bot, ← hI]
  refine AddSubgroup.mem_inertia.mpr fun x => ?_
  have h := hστ (τ⁻¹ • x)
  rwa [smul_inv_smul, ← mul_smul] at h

end Cox.ClassFieldTheory
