/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCongruenceDeletion
import XYin.PhD.Cox.Theorem11_1.ClassFieldConductorModuli
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalRayUnits
import XYin.PhD.Cox.Theorem11_1.ClassFieldDescent

/-! # Conductor support from the actual ray character

Janusz V.6.1–6.2 and V.11.3 remove a prime from a defining congruence modulus.
V.12.1 transfers the resulting ray-kernel condition to completed units. The
initial modulus remains admissible; no Artin map at the conductor is assumed.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [hNK : NumberField K]
include hNK

/-- Refine a nonzero modulus so that the selected prime occurs to a positive power. -/
theorem exists_primePower_complement_refinement (v : HeightOneSpectrum (𝓞 K))
    (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    ∃ (a : ℕ) (m : Ideal (𝓞 K)),
      0 < a ∧ m ≠ ⊥ ∧ v.asIdeal ⊔ m = ⊤ ∧ v.asIdeal ^ a * m ≤ n := by
  classical
  have hfin := Ideal.finite_factors hn
  have hnot : v ∉ hfin.toFinset.erase v := by simp
  have hsupp : ∀ w : HeightOneSpectrum (𝓞 K), n ≤ w.asIdeal →
      w ∈ insert v (hfin.toFinset.erase v) := by
    intro w hw
    by_cases hwv : w = v
    · rw [hwv]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hwv, hfin.mem_toFinset.mpr (Ideal.dvd_iff_le.mpr hw)⟩)
  obtain ⟨t₀, ht₀⟩ := exists_supportModulus_le K n hn _ hsupp
  have ht : 0 < max 1 t₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨max 1 t₀, supportModulus K (hfin.toFinset.erase v) (max 1 t₀), ht,
    supportModulus_ne_bot K _ _, ?_, ?_⟩
  · by_contra h
    have hmax := v.isPrime.isMaximal v.ne_bot
    have hle : supportModulus K (hfin.toFinset.erase v) (max 1 t₀) ≤ v.asIdeal :=
      le_sup_right.trans (hmax.eq_of_le h le_sup_left).symm.le
    exact hnot ((supportModulus_le_prime_iff K _ _ ht v).mp hle)
  · have h := ht₀ (max 1 t₀) (le_max_right _ _)
    rw [supportModulus, Finset.prod_insert hnot] at h
    exact h

-- The unused hypothesis is kept: the planned signature includes it.
set_option linter.unusedVariables false in
/-- Removing the selected prime from one defining modulus detects conductor support. -/
theorem conductor_not_le_iff_equivalent_at_primeComplement
    (H J : CongruenceSubgroup K) (hHJ : CongruenceEquivalent K H J)
    (v : HeightOneSpectrum (𝓞 K)) (m : Ideal (𝓞 K))
    (a : ℕ) (ha : 0 < a) (hcop : v.asIdeal ⊔ m = ⊤)
    (hmod : J.modulus = v.asIdeal ^ a * m) :
    (¬idealGroupConductor K H ≤ v.asIdeal) ↔
      ∃ C : CongruenceSubgroup K,
        CongruenceEquivalent K J C ∧ C.modulus = m := by
  have hm0 : m ≠ ⊥ := by
    rintro rfl
    apply J.modulus_ne_bot
    rw [hmod, Ideal.mul_bot]
  rw [conductor_not_le_iff_exists_equivalent_modulus]
  constructor
  · rintro ⟨C', hHC', hC'v⟩
    have hJC' : CongruenceEquivalent K J C' := (congruenceEquivalent_equivalence K).trans
      ((congruenceEquivalent_equivalence K).symm hHJ) hHC'
    have hvC' : v.asIdeal ⊔ C'.modulus = ⊤ := by
      by_contra h
      have hmax := v.isPrime.isMaximal v.ne_bot
      exact hC'v (le_sup_right.trans (hmax.eq_of_le h le_sup_left).symm.le)
    obtain ⟨G, hG, hJG, -⟩ := exists_congruence_gcd K J C' hJC'
    have hGm : G.modulus = m ⊔ C'.modulus := by
      rw [hG, hmod, Ideal.mul_sup_eq_of_coprime_left (Ideal.pow_sup_eq_top hvC')]
    have hmG : m ≤ G.modulus := hGm ▸ le_sup_left
    have hJGeq : CongruenceEquivalent K J G := by
      refine ⟨J.modulus, J.modulus_ne_bot, le_rfl, hG ▸ le_sup_left, ?_⟩
      rw [inf_eq_left.mpr J.ambient_le_coprimeIdeals]
      exact hJG
    exact ⟨restrictCongruence K G m hm0 hmG, (congruenceEquivalent_equivalence K).trans hJGeq
      (restrictCongruence_equivalent K G m hm0 hmG), rfl⟩
  · rintro ⟨C, hJC, hCm⟩
    refine ⟨C, (congruenceEquivalent_equivalence K).trans hHJ hJC, fun hle => ?_⟩
    rw [hCm] at hle
    rw [sup_eq_left.mpr hle] at hcop
    exact v.isPrime.ne_top hcop

/-- Erasing modulus factors acts identically on the actual principal image of V(1,m). -/
theorem rayUnitSubgroup_le_erasedPrincipal_ker_iff
    (v : HeightOneSpectrum (𝓞 K)) (m : Ideal (𝓞 K))
    (a : ℕ) (ha : 0 < a) (A : Type*) [Group A]
    (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* A) :
    rayUnitSubgroup K v m ≤
      ((φ.comp (eraseModulusFactors K (v.asIdeal ^ a * m))).comp
        ((toPrincipalIdeal (𝓞 K) K).comp (rayElements K m).subtype)).ker ↔
      Subgroup.closure (rayGenerators K m) ⊓
          coprimeIdeals K (v.asIdeal ^ a * m) ≤
        φ.ker.map (coprimeIdeals K (v.asIdeal ^ a * m)).subtype := by
  have hP := principal_map_rayUnitSubgroup K v m a ha
  constructor
  · intro h y hy
    rw [← hP] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxN := (mem_rayUnitSubgroup_iff_principal_coprime K v m a ha x).mp hx
    have h1 := h hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply] at h1
    refine ⟨⟨_, hxN⟩, ?_, rfl⟩
    have he := eraseModulusFactors_coprime K (v.asIdeal ^ a * m) ⟨_, hxN⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, ← he]
    exact h1
  · intro h x hx
    have hxN := (mem_rayUnitSubgroup_iff_principal_coprime K v m a ha x).mp hx
    have hy : ((toPrincipalIdeal (𝓞 K) K).comp (rayElements K m).subtype) x ∈
        Subgroup.closure (rayGenerators K m) ⊓ coprimeIdeals K (v.asIdeal ^ a * m) := by
      rw [← hP]
      exact ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hkx⟩ := h hy
    have he := eraseModulusFactors_coprime K (v.asIdeal ^ a * m) ⟨_, hxN⟩
    have hek : eraseModulusFactors K (v.asIdeal ^ a * m)
        (((toPrincipalIdeal (𝓞 K) K).comp (rayElements K m).subtype) x) = k :=
      he.trans (Subtype.ext hkx.symm)
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, hek]
    exact hk

/-- Actual agreement with a ray character identifies the depth-zero conductor condition. -/
theorem conductor_not_le_iff_localCharacter_units
    (H J : CongruenceSubgroup K) (hHJ : CongruenceEquivalent K H J)
    (v : HeightOneSpectrum (𝓞 K)) (m : Ideal (𝓞 K))
    (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤)
    (a : ℕ) (ha : 0 < a) (hmod : J.modulus = v.asIdeal ^ a * m)
    (A : Type*) [Group A] (φ : coprimeIdeals K (v.asIdeal ^ a * m) →* A)
    (hker : φ.ker.map (coprimeIdeals K (v.asIdeal ^ a * m)).subtype = J.ambient)
    (θ : (v.adicCompletion K)ˣ →* A)
    (hcomp : θ.comp ((completionUnitMap K v).comp (rayElements K m).subtype) =
      (φ.comp (eraseModulusFactors K (v.asIdeal ^ a * m))).comp
        ((toPrincipalIdeal (𝓞 K) K).comp (rayElements K m).subtype))
    (b : ℕ) (hb : localFieldUnitFiltration K v b ≤ θ.ker) :
    (¬idealGroupConductor K H ≤ v.asIdeal) ↔
      localFieldUnitFiltration K v 0 ≤ θ.ker := by
  have hJm : J.modulus ≤ m := by
    rw [hmod]
    exact Ideal.mul_le_left
  rw [conductor_not_le_iff_equivalent_at_primeComplement K H J hHJ v m a ha hcop hmod,
    exists_equivalent_at_modulus_iff_ray_restriction K J m hJm, hmod, ← hker,
    ← rayUnitSubgroup_le_erasedPrincipal_ker_iff K v m a ha A φ]
  exact rayUnitSubgroup_le_ker_iff_local_units_le_ker K v m hm hcop A θ _ hcomp b hb

end Cox.ClassFieldTheory
