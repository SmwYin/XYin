/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldGlobalLocalUnits
import XYin.PhD.Cox.Theorem11_1.ClassFieldRayNormApproximation
import XYin.PhD.Cox.Theorem11_1.ClassFieldRayGroups

/-! # The depth-zero ray subgroup

Janusz V.11.3 (printed p. 186, PDF p. 197) defines V(1,m) on the global ray elements
that are units at the selected finite prime. V.12.1 (printed p. 187, PDF p. 198)
compares this subgroup with the completed units.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [hNK : NumberField K]
include hNK

/-- The principal prime count vanishes precisely at global elements that are local units. -/
theorem principal_count_eq_zero_iff_global_unit (v : HeightOneSpectrum (𝓞 K)) (u : Kˣ) :
    FractionalIdeal.count K v (toPrincipalIdeal (𝓞 K) K u) = 0 ↔
      u ∈ globalValuationUnitGroup K v := by
  rw [mem_globalValuationUnitGroup_iff, completionUnitMap_apply, FinitePlace.embedding_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', valuation_eq_exp_neg_principal_count,
    WithZero.exp_eq_one, neg_eq_zero]

/-- Positive prime-power multiplication adds exactly the distinguished prime to the support. -/
theorem coprimeIdeals_primePower_mul (v : HeightOneSpectrum (𝓞 K))
    (m : Ideal (𝓞 K)) (a : ℕ) (ha : 0 < a) :
    coprimeIdeals K (v.asIdeal ^ a * m) =
      coprimeIdeals K v.asIdeal ⊓ coprimeIdeals K m := by
  have key : ∀ p : HeightOneSpectrum (𝓞 K),
      v.asIdeal ^ a * m ≤ p.asIdeal ↔ v.asIdeal ≤ p.asIdeal ∨ m ≤ p.asIdeal := by
    intro p
    haveI := p.isPrime
    rw [Ideal.IsPrime.mul_le p.isPrime, Ideal.IsPrime.pow_le_iff ha.ne']
  ext u
  rw [Subgroup.mem_inf, mem_coprimeIdeals_iff_count_eq_zero, mem_coprimeIdeals_iff_count_eq_zero,
    mem_coprimeIdeals_iff_count_eq_zero]
  constructor
  · intro h
    exact ⟨fun p hp => h p ((key p).mpr (Or.inl hp)), fun p hp => h p ((key p).mpr (Or.inr hp))⟩
  · rintro ⟨h1, h2⟩ p hp
    rcases (key p).mp hp with hp | hp
    · exact h1 p hp
    · exact h2 p hp

/-- A principal ideal avoids a height-one prime exactly when its generator is a local unit. -/
theorem principal_mem_coprime_prime_iff_global_unit (v : HeightOneSpectrum (𝓞 K))
    (u : Kˣ) :
    toPrincipalIdeal (𝓞 K) K u ∈ coprimeIdeals K v.asIdeal ↔
      u ∈ globalValuationUnitGroup K v := by
  rw [mem_coprimeIdeals_iff_count_eq_zero, ← principal_count_eq_zero_iff_global_unit]
  constructor
  · intro h
    exact h v le_rfl
  · intro h q hq
    have hqv : q = v :=
      HeightOneSpectrum.ext (v.isMaximal.eq_of_le q.isPrime.ne_top hq).symm
    rw [hqv]
    exact h

/-- The source V(1,m), on the actual carrier of ray elements modulo m. -/
def rayUnitSubgroup (v : HeightOneSpectrum (𝓞 K)) (m : Ideal (𝓞 K)) :
    Subgroup (rayElements K m) :=
  (globalValuationUnitGroup K v).comap (rayElements K m).subtype

/-- A ray element lies in V(1,m) exactly when its principal ideal avoids the full modulus. -/
theorem mem_rayUnitSubgroup_iff_principal_coprime (v : HeightOneSpectrum (𝓞 K))
    (m : Ideal (𝓞 K)) (a : ℕ) (ha : 0 < a) (x : rayElements K m) :
    x ∈ rayUnitSubgroup K v m ↔
      toPrincipalIdeal (𝓞 K) K (x : Kˣ) ∈ coprimeIdeals K (v.asIdeal ^ a * m) := by
  rw [coprimeIdeals_primePower_mul K v m a ha, Subgroup.mem_inf,
    principal_mem_coprime_prime_iff_global_unit]
  constructor
  · intro hx
    exact ⟨hx, principal_mem_coprime_of_mem_rayElements K m x x.2⟩
  · intro hx
    exact hx.1

/-- Normalize the existing ray-principal image to its ambient fractional-ideal carrier. -/
theorem principalRayMap_range (m : Ideal (𝓞 K)) :
    ((toPrincipalIdeal (𝓞 K) K).comp (rayElements K m).subtype).range =
      Subgroup.closure (rayGenerators K m) := by
  ext y
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (principal_mem_ray_of_mem_rayElements K m x x.2)
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← hzx]
    exact hz
  · intro hy
    obtain ⟨α, hα, hαy⟩ := exists_rayElement_of_mem_closure K m hy
    exact ⟨⟨α, hα⟩, hαy⟩

/-- The image of V(1,m) is the ray-principal subgroup restricted to the full good-ideal carrier. -/
theorem principal_map_rayUnitSubgroup (v : HeightOneSpectrum (𝓞 K))
    (m : Ideal (𝓞 K)) (a : ℕ) (ha : 0 < a) :
    (rayUnitSubgroup K v m).map
        ((toPrincipalIdeal (𝓞 K) K).comp (rayElements K m).subtype) =
      Subgroup.closure (rayGenerators K m) ⊓ coprimeIdeals K (v.asIdeal ^ a * m) := by
  have hU : rayUnitSubgroup K v m = (coprimeIdeals K (v.asIdeal ^ a * m)).comap
      ((toPrincipalIdeal (𝓞 K) K).comp (rayElements K m).subtype) := by
    ext x
    exact mem_rayUnitSubgroup_iff_principal_coprime K v m a ha x
  rw [hU, Subgroup.map_comap_eq, principalRayMap_range]

/-- Ray-preserving approximation detects whether a local character kills all local units. -/
theorem rayUnitSubgroup_le_ker_iff_local_units_le_ker (v : HeightOneSpectrum (𝓞 K))
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤)
    (A : Type*) [Group A] (θ : (v.adicCompletion K)ˣ →* A)
    (g : rayElements K m →* A)
    (hcomp : θ.comp ((completionUnitMap K v).comp (rayElements K m).subtype) = g)
    (b : ℕ) (hb : localFieldUnitFiltration K v b ≤ θ.ker) :
    rayUnitSubgroup K v m ≤ g.ker ↔ localFieldUnitFiltration K v 0 ≤ θ.ker := by
  constructor
  · intro h β hβ
    obtain ⟨γ, hγ⟩ := exists_ray_preserving_localApprox K v m hm hcop β b
    have hγV : γ ∈ rayUnitSubgroup K v m := by
      have h0 := Subgroup.mul_mem _ (localFieldUnitFiltration_le_zero K v b hγ) hβ
      rwa [inv_mul_cancel_right] at h0
    have hgγ : g γ = 1 := h hγV
    have hθγ : θ (completionUnitMap K v (γ : Kˣ)) = 1 := (DFunLike.congr_fun hcomp γ).trans hgγ
    have hθe := hb hγ
    rw [MonoidHom.mem_ker, map_mul, hθγ, one_mul, map_inv, inv_eq_one] at hθe
    exact hθe
  · intro h x hx
    have hx' : completionUnitMap K v (x : Kˣ) ∈ localFieldUnitFiltration K v 0 := hx
    rw [MonoidHom.mem_ker, ← hcomp]
    exact h hx'

end Cox.ClassFieldTheory
