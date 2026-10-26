/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalSeries

/-! # Principal units and division on deep ideals

These elementary adapters express the units and ideal coordinates in
Janusz V.3.5–3.6, printed151/PDF162, using the actual reduction kernel.
-/
open NumberField IsDedekindDomain
noncomputable section
namespace Cox.ClassFieldTheory

/-- The reduction kernel is the congruence condition on the underlying unit. -/
theorem mem_unitReduction_ker_iff {R : Type*} [CommRing R]
    (I : Ideal R) (u : Rˣ) :
    u ∈ (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker ↔ (u : R) - 1 ∈ I := by
  rw [MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
    ← map_one (Ideal.Quotient.mk I)]
  exact Ideal.Quotient.eq

/-- Adding a maximal-ideal element to one gives a unit in any commutative local ring. -/
theorem isUnit_one_add_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) : IsUnit (1 + x) := by
  have h : -x ∈ nonunits R :=
    (IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.maximalIdeal R).neg_mem hx)
  simpa [sub_neg_eq_add] using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-x) h

variable (K : Type*) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

/-- The local principal-unit group has the source's literal one-plus-ideal coordinates. -/
theorem mem_localUnitFiltration_iff (t : ℕ) (u : (v.adicCompletionIntegers K)ˣ) :
    u ∈ localUnitFiltration K v t ↔
      (u : v.adicCompletionIntegers K) - 1 ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t := by
  rw [localUnitFiltration]
  exact mem_unitReduction_ker_iff _ u

/-- Increasing depth decreases the principal-unit subgroup, including depth zero. -/
theorem localUnitFiltration_antitone : Antitone (localUnitFiltration K v) := by
  intro s t hst u hu
  rw [mem_localUnitFiltration_iff] at hu ⊢
  exact Ideal.pow_le_pow_right hst hu

namespace LocalCyclic

/-- Division by a fixed scalar maps sufficiently deep ideals into any prescribed ideal. -/
theorem exists_div_mem_deep_ideal (a : v.adicCompletion K) (s : ℕ) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ x : v.adicCompletionIntegers K,
      x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
        ∃ z : v.adicCompletionIntegers K,
          z ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ s ∧
            (z : v.adicCompletion K) = (x : v.adicCompletion K) / a := by
  by_cases ha : a = 0
  · refine ⟨0, ?_⟩
    intro t ht x hx
    refine ⟨0, Ideal.zero_mem _, ?_⟩
    simp [ha]
  · obtain ⟨π, hπ⟩ := exists_completed_uniformizer K v
    have hπ0 : (π : v.adicCompletion K) ≠ 0 := by
      intro hzero
      have hvzero : Valued.v (π : v.adicCompletion K) = 0 := by simp [hzero]
      exact WithZero.exp_ne_zero (hπ.symm.trans hvzero)
    have hπmem : π ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
      rw [completed_maximalIdeal_eq_span K v π hπ]
      exact Ideal.mem_span_singleton_self π
    have hπs := Ideal.pow_mem_pow hπmem s
    have haNorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hπNorm : 0 < ‖(π : v.adicCompletion K)‖ := norm_pos_iff.mpr hπ0
    obtain ⟨t₀, ht₀⟩ := exists_ideal_depth_norm_lt K v
      (‖a‖ * ‖(π : v.adicCompletion K)‖ ^ s) (mul_pos haNorm (pow_pos hπNorm s))
    refine ⟨t₀, ?_⟩
    intro t ht x hx
    apply exists_integer_mem_ideal_of_norm_le K v s (π ^ s) hπs
      ((x : v.adicCompletion K) / a)
    have hdiv : ‖(x : v.adicCompletion K)‖ / ‖a‖ < ‖(π : v.adicCompletion K)‖ ^ s := by
      apply (div_lt_iff₀ haNorm).mpr
      simpa [mul_comm] using ht₀ t ht x hx
    change ‖(x : v.adicCompletion K) / a‖ ≤ ‖(π : v.adicCompletion K) ^ s‖
    simpa only [norm_div, norm_pow] using hdiv.le

end LocalCyclic
end Cox.ClassFieldTheory
