/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldRayGroups
import Mathlib.Order.ModularLattice

/-! # Removing a prime from a congruence modulus

Janusz V.6.1–6.2, printed166–168/PDF177–179, supply the pure congruence-group
criterion used by V.11.3, printed186/PDF197. No class field or local norm theorem is assumed.
-/

open NumberField
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [hNK : NumberField K]
include hNK

/-- Equivalent congruence groups at ordered moduli have the actual ordered restriction. -/
theorem congruenceEquivalent_ambient_restriction (H J : CongruenceSubgroup K)
    (hm : H.modulus ≤ J.modulus) (hHJ : CongruenceEquivalent K H J) :
    H.ambient = J.ambient ⊓ coprimeIdeals K H.modulus := by
  obtain ⟨G, hG, hH, hJ⟩ := exists_congruence_gcd K H J hHJ
  rw [sup_eq_right.mpr hm] at hG
  have hGJ : G.ambient ⊓ coprimeIdeals K J.modulus = G.ambient := by
    rw [← hG]
    exact inf_eq_left.mpr G.ambient_le_coprimeIdeals
  rw [hJ, hGJ]
  exact hH

/-- Adjoin the smaller-modulus ray subgroup inside its actual good-ideal carrier. -/
theorem exists_congruence_sup_ray (H : CongruenceSubgroup K) (m : Ideal (𝓞 K))
    (hm : H.modulus ≤ m) :
    ∃ J : CongruenceSubgroup K, J.modulus = m ∧
      J.ambient = H.ambient ⊔ Subgroup.closure (rayGenerators K m) := by
  set A := H.ambient ⊔ Subgroup.closure (rayGenerators K m) with hA
  have hAm : A ≤ coprimeIdeals K m := sup_le
    (H.ambient_le_coprimeIdeals.trans (coprimeIdeals_mono K hm))
    ((Subgroup.closure_le _).mpr (rayGenerators_mem_coprimeIdeals K m))
  have hm0 : m ≠ ⊥ := fun h => H.modulus_ne_bot (eq_bot_iff.mpr (h ▸ hm))
  refine ⟨{ modulus := m
            modulus_ne_bot := hm0
            subgroup := A.comap (coprimeIdeals K m).subtype
            contains_ray := Subgroup.comap_mono le_sup_right }, rfl, ?_⟩
  change (A.comap (coprimeIdeals K m).subtype).map (coprimeIdeals K m).subtype = A
  rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.mpr hAm]

/-- The source modulus-deletion criterion is a restricted ray-principal containment. -/
theorem exists_equivalent_at_modulus_iff_ray_restriction (H : CongruenceSubgroup K)
    (m : Ideal (𝓞 K)) (hm : H.modulus ≤ m) :
    (∃ J : CongruenceSubgroup K, CongruenceEquivalent K H J ∧ J.modulus = m) ↔
      Subgroup.closure (rayGenerators K m) ⊓ coprimeIdeals K H.modulus ≤ H.ambient := by
  constructor
  · rintro ⟨J, hHJ, rfl⟩
    rw [congruenceEquivalent_ambient_restriction K H J hm hHJ]
    exact inf_le_inf_right _ J.closure_rayGenerators_le_ambient
  · intro h
    obtain ⟨J, hJm, hJ⟩ := exists_congruence_sup_ray K H m hm
    refine ⟨J, ⟨H.modulus, H.modulus_ne_bot, le_rfl, by rw [hJm]; exact hm, ?_⟩, hJm⟩
    rw [hJ, inf_eq_left.mpr H.ambient_le_coprimeIdeals]
    apply le_antisymm
    · exact le_inf le_sup_left H.ambient_le_coprimeIdeals
    · rintro x ⟨hxs, hxI⟩
      obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hxs
      have hcI : c ∈ coprimeIdeals K H.modulus := by
        have h' := (coprimeIdeals K H.modulus).mul_mem
          ((coprimeIdeals K H.modulus).inv_mem (H.ambient_le_coprimeIdeals ha)) hxI
        rwa [inv_mul_cancel_left] at h'
      exact H.ambient.mul_mem ha (h ⟨hc, hcI⟩)

end Cox.ClassFieldTheory
