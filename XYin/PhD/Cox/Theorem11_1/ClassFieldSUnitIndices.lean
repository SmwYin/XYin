/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldSUnits
import Mathlib.Algebra.Group.Subgroup.Order

/-! # The index calculation in Janusz V.9.10–9.11

These are the actual power, S-unit and ray groups in the book's calculation.
Natural-number products avoid division and retain the zero-for-infinite convention.
-/
open NumberField IsDedekindDomain NumberField.InfinitePlace
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- The actual supported ideal group has zero prime count outside the given support. -/
theorem mem_supportedIdeals_iff_count_eq_zero (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    I ∈ Cox.ClassFieldTheory.supportedIdeals K S ↔
      ∀ v ∉ S, FractionalIdeal.count K v I = 0 := by
  classical
  constructor
  · intro h v hv
    exact count_eq_zero_of_mem_supportedIdeals K S ⟨I, h⟩ v hv
  · intro h
    obtain ⟨J, hJ⟩ := supportedIdealExponentMap_surjective K S
      (Multiplicative.ofAdd (fun v : S ↦ FractionalIdeal.count K v.val I))
    have he : J.val = I := by
      apply Units.ext
      rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K J.val.ne_zero,
        ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero]
      apply finprod_congr
      intro v
      congr 1
      by_cases hv : v ∈ S
      · exact congrArg (fun f : Multiplicative (S → ℤ) ↦ f.toAdd ⟨v, hv⟩) hJ
      · rw [count_eq_zero_of_mem_supportedIdeals K S J v hv, h v hv]
    exact he ▸ J.property

/-- For a positive exponent, a field unit is an S-unit exactly when its power is. -/
theorem pow_mem_sUnits_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : 0 < n) (u : Kˣ) : u ^ n ∈ sUnits K S ↔ u ∈ sUnits K S := by
  constructor
  · intro h
    apply (mem_supportedIdeals_iff_count_eq_zero K S _).mpr
    intro v hv
    have hz := (mem_supportedIdeals_iff_count_eq_zero K S _).mp h v hv
    rw [map_pow] at hz
    change FractionalIdeal.count K v
      ((toPrincipalIdeal (𝓞 K) K u : FractionalIdeal (𝓞 K)⁰ K) ^ n) = 0 at hz
    rw [FractionalIdeal.count_pow] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hn.ne')
  · exact fun h ↦ (sUnits K S).pow_mem h n

/-- A power-saturated subgroup has the same powers internally and by ambient restriction. -/
theorem powers_subgroupOf_of_saturated {G : Type*} [CommGroup G]
    (U : Subgroup G) (n : ℕ) (hU : ∀ x : G, x ^ n ∈ U → x ∈ U) :
    ((powMonoidHom n : G →* G).range).subgroupOf U =
      (powMonoidHom n : U →* U).range := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    have hy' : y ^ n = (x : G) := hy
    have hyU : y ∈ U := hU y (hy'.symm ▸ x.property)
    exact ⟨⟨y, hyU⟩, Subtype.ext hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y.val, congrArg Subtype.val hy⟩

/-- Janusz V.9.10: index multiplication for joins and intersections, without division. -/
theorem relIndex_sup_inf {G : Type*} [CommGroup G] (A B C : Subgroup G) (hBA : B ≤ A) :
    B.relIndex A = (B ⊔ C).relIndex (A ⊔ C) * (B ⊓ C).relIndex (A ⊓ C) := by
  have h1 : B.relIndex ((B ⊔ C) ⊓ A) = (B ⊓ C).relIndex (A ⊓ C) := by
    rw [sup_inf_assoc_of_le C hBA, sup_comm B (C ⊓ A),
      Subgroup.relIndex_sup_right, inf_comm C A]
    have he : B.subgroupOf (A ⊓ C) = (B ⊓ C).subgroupOf (A ⊓ C) := by
      apply Subgroup.ext
      intro x
      exact ⟨fun h ↦ ⟨h, x.2.2⟩, fun h ↦ h.1⟩
    exact congrArg Subgroup.index he
  have h2 : ((B ⊔ C) ⊓ A).relIndex A = (B ⊔ C).relIndex (A ⊔ C) := by
    have he : ((B ⊔ C) ⊓ A).subgroupOf A = (B ⊔ C).subgroupOf A := by
      apply Subgroup.ext
      intro x
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, x.2⟩⟩
    change (((B ⊔ C) ⊓ A).subgroupOf A).index = _
    rw [he]
    have h := Subgroup.relIndex_sup_right A (B ⊔ C)
    simpa only [← sup_assoc, sup_of_le_left hBA] using h.symm
  rw [← Subgroup.relIndex_mul_relIndex B ((B ⊔ C) ⊓ A) A
    (le_inf le_sup_left hBA) inf_le_right, h1, h2, mul_comm]

/-- The V.9.10 substitution A = B ∨ U, with the exact intersection carrier. -/
theorem relIndex_join_intersection {G : Type*} [CommGroup G] (B U C : Subgroup G) :
    B.relIndex (B ⊔ U) = (B ⊔ C).relIndex (B ⊔ U ⊔ C) *
      B.relIndex ((B ⊔ U) ⊓ C) := by
  have h := relIndex_sup_inf (B ⊔ U) B C le_sup_left
  have hc : (B ⊓ C).subgroupOf ((B ⊔ U) ⊓ C) =
      B.subgroupOf ((B ⊔ U) ⊓ C) := by
    ext x
    exact ⟨fun hx ↦ hx.1, fun hx ↦ ⟨hx, x.2.2⟩⟩
  simpa only [Subgroup.relIndex, hc] using h

/-- The source index calculation with denominators cleared. -/
theorem index_join_mul_relIndex {G : Type*} [CommGroup G] (B U C : Subgroup G) :
    (B ⊔ U ⊔ C).index * B.relIndex (B ⊔ U) =
      B.relIndex ((B ⊔ U) ⊓ C) * (B ⊔ C).index := by
  rw [relIndex_join_intersection B U C,
    ← Subgroup.relIndex_mul_index (show B ⊔ C ≤ B ⊔ U ⊔ C from
      sup_le (le_trans le_sup_left le_sup_left) le_sup_right)]
  ac_rfl

/-- The relative index of ambient powers in powers times S-units. -/
theorem nthPowers_relIndex_sUnits (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    (nthPowers K n).relIndex (nthPowers K n ⊔ sUnits K S) =
      n ^ (S.card + nrRealPlaces K + nrComplexPlaces K) := by
  rw [Subgroup.relIndex_sup_left]
  change ((powMonoidHom n : Kˣ →* Kˣ).range.subgroupOf (sUnits K S)).index = _
  rw [powers_subgroupOf_of_saturated (sUnits K S) n
    (fun u hu ↦ (pow_mem_sUnits_iff K S n hn u).mp hu)]
  exact sUnits_power_index K S n hn ζ hζ

/-- The actual power, S-unit and ray groups satisfy the source index identity. -/
theorem power_ray_sUnit_index_identity (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (m : Ideal (𝓞 K)) :
    (nthPowers K n ⊔ sUnits K S ⊔ rayElements K m).index *
        n ^ (S.card + nrRealPlaces K + nrComplexPlaces K) =
      ((nthPowers K n).subgroupOf ((sUnits K S ⊔ nthPowers K n) ⊓ rayElements K m)).index *
        powerCongruenceIndex K n m := by
  have h := index_join_mul_relIndex (nthPowers K n) (sUnits K S) (rayElements K m)
  rw [nthPowers_relIndex_sUnits K S n hn ζ hζ] at h
  have he : (nthPowers K n).relIndex
      ((nthPowers K n ⊔ sUnits K S) ⊓ rayElements K m) =
      (nthPowers K n).relIndex ((sUnits K S ⊔ nthPowers K n) ⊓ rayElements K m) := by
    rw [sup_comm (nthPowers K n) (sUnits K S)]
  rw [he] at h
  exact h

end Cox.ClassFieldTheory
