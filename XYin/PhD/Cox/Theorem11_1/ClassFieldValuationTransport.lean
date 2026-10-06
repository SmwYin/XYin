/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Transport of normalized prime valuations

Janusz III.1.1 and V.3.4: conjugating a prime conjugates its valuation.
-/
open NumberField IsDedekindDomain
open scoped WithZero
noncomputable section
namespace Cox.ClassFieldTheory
variable (L : Type*) [Field L] [NumberField L]
variable (σ : L ≃+* L) (u w : HeightOneSpectrum (𝓞 L))
variable (hσ : Ideal.map (RingOfIntegers.mapRingEquiv σ).toRingHom u.asIdeal = w.asIdeal)

include hσ

-- `[NumberField L]` comes from the section `variable`; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Conjugation carries membership in every power of the source prime to the target prime. -/
theorem primeTransport_mem_pow_iff (a : 𝓞 L) (n : ℕ) :
    RingOfIntegers.mapRingEquiv σ a ∈ w.asIdeal ^ n ↔ a ∈ u.asIdeal ^ n := by
  rw [← hσ, ← Ideal.map_pow]
  constructor
  · intro h
    obtain ⟨b, hb, hba⟩ := (Ideal.mem_map_iff_of_surjective _
      (RingOfIntegers.mapRingEquiv σ).surjective).mp h
    have hab : b = a := (RingOfIntegers.mapRingEquiv σ).injective hba
    rwa [← hab]
  · intro h
    exact Ideal.mem_map_of_mem _ h

/-- The normalized integer valuations agree under the same prime conjugation. -/
theorem primeTransport_intValuation (a : 𝓞 L) :
    w.intValuation (RingOfIntegers.mapRingEquiv σ a) = u.intValuation a := by
  by_cases ha : a = 0
  · simp [ha]
  have ha' : RingOfIntegers.mapRingEquiv σ a ≠ 0 :=
    (map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv σ).injective).mpr ha
  apply le_antisymm
  · rw [u.intValuation_if_neg ha, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      primeTransport_mem_pow_iff L σ u w hσ, ← HeightOneSpectrum.intValuation_le_pow_iff_mem,
      u.intValuation_if_neg ha]
  · rw [w.intValuation_if_neg ha', HeightOneSpectrum.intValuation_le_pow_iff_mem,
      ← primeTransport_mem_pow_iff L σ u w hσ, ← HeightOneSpectrum.intValuation_le_pow_iff_mem,
      w.intValuation_if_neg ha']

/-- Janusz V.3.4: conjugation of a global element transports its prime valuation. -/
theorem primeTransport_valuation (x : L) :
    w.valuation L (σ x) = u.valuation L x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have hσa : σ (algebraMap (𝓞 L) L a) =
      algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv σ a) := rfl
  have hσb : σ (algebraMap (𝓞 L) L b) =
      algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv σ b) := rfl
  rw [map_div₀, hσa, hσb, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, primeTransport_intValuation L σ u w hσ,
    primeTransport_intValuation L σ u w hσ]

end Cox.ClassFieldTheory
