/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArithmetic
import XYin.PhD.Cox.Theorem11_1.ClassFieldRayCountingDefs

/-! # Changing the modulus of a norm/ray quotient

Janusz V.4.3 and V.6.1 use the actual inclusion of prime-to-modulus ideals.
Its induced quotient map is surjective by ray-principal approximation.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Ray principal ideals for a more divisible modulus remain ray principal ideals. -/
theorem raySubgroup_restrictModulus (m n : Ideal (𝓞 K)) (hmn : m ≤ n) :
    (raySubgroup K m).map (Subgroup.inclusion (coprimeIdeals_mono K hmn)) ≤
      raySubgroup K n := by
  rintro _ ⟨x, hx, rfl⟩
  change ((Subgroup.inclusion (coprimeIdeals_mono K hmn) x : coprimeIdeals K n) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ Subgroup.closure (rayGenerators K n)
  rw [Subgroup.coe_inclusion]
  exact Subgroup.closure_mono (rayGenerators_mono K hmn) hx

/-- Norm images restrict along a more divisible modulus. -/
theorem normImage_restrictModulus (F : Type*) [Field F] [NumberField F] [Algebra K F]
    [Module.Finite (𝓞 K) (𝓞 F)] (m n : Ideal (𝓞 K)) (hmn : m ≤ n) :
    (normImage K m F).map (Subgroup.inclusion (coprimeIdeals_mono K hmn)) ≤
      normImage K n F := by
  rw [Subgroup.map_le_iff_le_comap, normImage]
  refine (Subgroup.closure_le _).mpr ?_
  rintro u ⟨A, hA0, hAm, hu⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  apply Subgroup.subset_closure
  refine ⟨A, hA0, ?_, ?_⟩
  · exact top_unique (hAm ▸ sup_le_sup_left (Ideal.map_mono hmn) A)
  · rw [Subgroup.coe_inclusion]
    exact hu

variable (L : Type*) [Field L] [NumberField L] [Algebra K L]

/-- Both norm and ray generators are respected by the actual good-ideal inclusion. -/
theorem normRaySubgroup_restrictModulus (m n : Ideal (𝓞 K)) (hmn : m ≤ n) :
    (normRaySubgroup K m L).map (Subgroup.inclusion (coprimeIdeals_mono K hmn)) ≤
      normRaySubgroup K n L := by
  rw [normRaySubgroup, normRaySubgroup, Subgroup.map_sup]
  exact sup_le_sup (normImage_restrictModulus K L m n hmn) (raySubgroup_restrictModulus K m n hmn)

/-- Ray-principal correction lifts every class to the more divisible modulus. -/
theorem normRayQuotient_restrict_surjective (m n : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (hmn : m ≤ n) :
    Function.Surjective (QuotientGroup.map (normRaySubgroup K m L)
      (normRaySubgroup K n L) (Subgroup.inclusion (coprimeIdeals_mono K hmn))
        (Subgroup.map_le_iff_le_comap.mp (normRaySubgroup_restrictModulus K L m n hmn))) := by
  intro y
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨a, ha, hmem⟩ := exists_ray_principal_correction K m n hm hmn u
  refine ⟨((⟨_, hmem⟩ : coprimeIdeals K m) : coprimeIdeals K m ⧸ normRaySubgroup K m L), ?_⟩
  rw [QuotientGroup.map_mk, QuotientGroup.eq]
  apply Subgroup.mem_sup_right
  change (((Subgroup.inclusion (coprimeIdeals_mono K hmn) ⟨_, hmem⟩)⁻¹ * u :
    coprimeIdeals K n) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ Subgroup.closure (rayGenerators K n)
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, mul_inv_rev, inv_inv,
    inv_mul_cancel_right]
  obtain ⟨y, hy, hya⟩ := principal_mem_ray_of_mem_rayElements K n a ha
  rw [← hya]
  exact hy

-- The unused hypothesis is kept: the planned signature includes it.
set_option linter.unusedVariables false in
/-- Restricting to a more divisible modulus can only increase the norm/ray quotient index. -/
theorem normRaySubgroup_index_mono (m n : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hn : n ≠ ⊥)
    (hmn : m ≤ n) : (normRaySubgroup K n L).index ≤ (normRaySubgroup K m L).index := by
  haveI := finiteIndex_of_raySubgroup_le K m hm (normRaySubgroup K m L) le_sup_right
  exact Nat.card_le_card_of_surjective _ (normRayQuotient_restrict_surjective K L m n hm hmn)

end Cox.ClassFieldTheory
