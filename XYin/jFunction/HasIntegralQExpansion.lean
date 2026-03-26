import Mathlib.NumberTheory.ModularForms.QExpansion
import XYin.jFunction.IntegralPowerSeries

open Complex ModularFormClass UpperHalfPlane MatrixGroups Real IntegralPowerSeries

def HasIntegralQExpansion (h : ℝ) (f : ℍ → ℂ) : Prop := ∃ n : ℕ,
  IsIntegralPowerSeries (qExpansion h ((fun z ↦ cexp (2 * π * Complex.I * z) ^ n : ℍ → ℂ) * f))

lemma HasIntegralQExpansion_ofPowerSeries {h : ℝ} {f : ℍ → ℂ}
    (hf : IsIntegralPowerSeries (qExpansion h f)) : HasIntegralQExpansion h f := by
  use 0
  have hmul : ((fun _ : ℍ ↦ (1 : ℂ)) * f) = f := by funext z; simp
  simp [pow_zero, hmul, hf]

lemma IsIntegralPowerSeries_X_pow (n : ℕ) :
    IsIntegralPowerSeries ((PowerSeries.X : PowerSeries ℂ) ^ n) := by
  rw [int_iff]
  intro m
  by_cases hmn : m = n
  · refine ⟨1, ?_⟩
    simp [hmn]
  · refine ⟨0, ?_⟩
    simp [PowerSeries.coeff_X_pow, hmn]

lemma IsIntegralPowerSeries.shift {f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f) (n : ℕ) :
    IsIntegralPowerSeries (((PowerSeries.X : PowerSeries ℂ) ^ n) * f) := by
  exact IntegralPowerSeriesSubring.mul_mem (IsIntegralPowerSeries_X_pow n) hf

lemma HasIntegralQExpansion.sum {h : ℝ} {f : ℍ → ℂ} {g : ℍ → ℂ}
    (hf : HasIntegralQExpansion h f) (hg : HasIntegralQExpansion h g) :
    HasIntegralQExpansion h (f + g) := by
  sorry
