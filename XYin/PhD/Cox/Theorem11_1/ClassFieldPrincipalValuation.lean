/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! # Principal ideal exponents and adic valuation
Native count and valuation adapters for the local-unit step of Janusz V.9.3.
-/

noncomputable section
open IsDedekindDomain WithZero
open scoped nonZeroDivisors
namespace Cox.ClassFieldTheory

/-- The prime count of a principal fraction is the numerator count minus the denominator count. -/
theorem count_spanSingleton_mk'
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (a : R) (ha : a ≠ 0) (b : R⁰) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' K a b)) =
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ) -
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(b : R)})).factors : ℤ) := by
  have hmk : IsLocalization.mk' K a b = algebraMap R K a / algebraMap R K b :=
    IsFractionRing.mk'_eq_div b
  have hbK : algebraMap R K (b : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have haK : algebraMap R K a ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective R K)]
  have hI : FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' K a b) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff, hmk]
    exact div_ne_zero haK hbK
  have h_aJ : FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' K a b) =
      FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) (b : R))⁻¹ *
        ↑(Ideal.span {a} : Ideal R) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      hmk, div_eq_inv_mul]
  rw [FractionalIdeal.count_well_defined K v hI h_aJ]

/-- The multiplicative adic valuation is the exponential of the negative principal-ideal prime
count. -/
theorem valuation_eq_exp_neg_count_spanSingleton
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp
      (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)) := by
  obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq R⁰ x
  have ha : a ≠ 0 := by
    rintro rfl
    exact hx (IsLocalization.mk'_zero b)
  have hb : (b : R) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  rw [count_spanSingleton_mk' v a ha b, HeightOneSpectrum.valuation_of_mk',
    v.intValuation_if_neg ha, v.intValuation_if_neg hb, ← WithZero.exp_sub]
  congr 1
  ring

end Cox.ClassFieldTheory
