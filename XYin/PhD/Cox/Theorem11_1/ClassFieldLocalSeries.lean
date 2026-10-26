/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArithmetic
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionResidue
import XYin.PhD.Cox.Theorem11_1.ClassFieldSeriesBounds

/-! # Local convergence and preservation of deep ideals

Janusz V.3.5, printed151/PDF162. The actual source series are connected to
formal-series evaluation, and norm estimates retain the same ideal depth.
-/
open NumberField IsDedekindDomain Filter
open scoped Topology WithZero
noncomputable section
namespace Cox.ClassFieldTheory.LocalCyclic
variable (K : Type*) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

/-- The source logarithm series evaluated at x=u-1, before taking any sum. -/
def logTerm (x : v.adicCompletion K) (n : ℕ) : v.adicCompletion K :=
  (-1 : v.adicCompletion K) ^ n * x ^ (n + 1) / (n + 1 : ℕ)

/-- The source exponential series, before taking any sum. -/
def expTerm (x : v.adicCompletion K) (n : ℕ) : v.adicCompletion K :=
  x ^ n / (n.factorial : v.adicCompletion K)

/-- The local logarithm value, using exactly the source series in x=u-1. -/
def logValue (x : v.adicCompletion K) : v.adicCompletion K := ∑' n, logTerm K v x n

/-- The local exponential value, using exactly the source series. -/
def expValue (x : v.adicCompletion K) : v.adicCompletion K := ∑' n, expTerm K v x n

/-- The residue characteristic supplies a prime with strictly small completed norm. -/
theorem exists_prime_norm_lt_one :
    ∃ p : ℕ, p.Prime ∧ ‖(p : v.adicCompletion K)‖ < 1 := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨p, hchar⟩ := CharP.exists (𝓞 K ⧸ v.asIdeal)
  haveI := hchar
  have hp : p.Prime := (CharP.char_is_prime_or_zero (𝓞 K ⧸ v.asIdeal) p).resolve_right
    (CharP.char_ne_zero_of_finite (𝓞 K ⧸ v.asIdeal) p)
  have hmem : (p : 𝓞 K) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (𝓞 K ⧸ v.asIdeal) p
  refine ⟨p, hp, ?_⟩
  have h := (FinitePlace.norm_lt_one_iff_mem (K := K) v (p : 𝓞 K)).mpr hmem
  simpa using h

/-- Maximal-ideal membership is precisely strict smallness of the completed norm. -/
theorem mem_completed_maximalIdeal_iff_norm_lt_one (x : v.adicCompletionIntegers K) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔
      ‖(x : v.adicCompletion K)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have hx1 : Valued.v (x : v.adicCompletion K) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp x.2
  exact ⟨fun h => lt_of_le_of_ne hx1 h, fun h => ne_of_lt h⟩

/-- A normalized uniformizer expresses each ideal power as an actual closed norm ball. -/
theorem mem_completed_ideal_pow_iff_norm_le (π : v.adicCompletionIntegers K)
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (x : v.adicCompletionIntegers K) (t : ℕ) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t ↔
      ‖(x : v.adicCompletion K)‖ ≤ ‖(π : v.adicCompletion K)‖ ^ t := by
  rw [completed_mem_maximalIdeal_pow_iff K v x t, ← norm_pow, Valued.toNormedField.norm_le_iff,
    map_pow, hπ, ← WithZero.exp_nsmul]
  simp

/-- Every positive norm ball contains all sufficiently deep completed ideal powers. -/
theorem exists_ideal_depth_norm_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ x : v.adicCompletionIntegers K,
      x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
        ‖(x : v.adicCompletion K)‖ < ε := by
  obtain ⟨π, hπ⟩ := exists_completed_uniformizer K v
  have hπ1 : ‖(π : v.adicCompletion K)‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  obtain ⟨t₀, ht₀⟩ := exists_pow_lt_of_lt_one hε hπ1
  refine ⟨t₀, fun t ht x hx => ?_⟩
  rw [mem_completed_ideal_pow_iff_norm_le K v π hπ] at hx
  exact lt_of_le_of_lt hx (lt_of_le_of_lt (pow_le_pow_of_le_one (norm_nonneg _) hπ1.le ht) ht₀)

/-- An element no larger than an element of an ideal belongs to that same ideal. -/
theorem exists_integer_mem_ideal_of_norm_le (t : ℕ)
    (x : v.adicCompletionIntegers K)
    (hx : x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t)
    (y : v.adicCompletion K) (hy : ‖y‖ ≤ ‖(x : v.adicCompletion K)‖) :
    ∃ z : v.adicCompletionIntegers K,
      z ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t ∧
        (z : v.adicCompletion K) = y := by
  have hvx := (completed_mem_maximalIdeal_pow_iff K v x t).mp hx
  have hvy : Valued.v y ≤ Valued.v (x : v.adicCompletion K) :=
    Valued.toNormedField.norm_le_iff.mp hy
  have hy1 : Valued.v y ≤ 1 :=
    hvy.trans ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp x.2)
  refine ⟨⟨y, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hy1⟩, ?_, rfl⟩
  exact (completed_mem_maximalIdeal_pow_iff K v _ t).mpr (hvy.trans hvx)

/-- Removing the zero constant coefficient identifies the actual logarithm series. -/
theorem logValue_eq_powerSeries_value (x : v.adicCompletion K)
    (hx : Summable (logTerm K v x)) :
    logValue K v x = Cox.ClassFieldConvergentSeries.value
      (PowerSeries.log (v.adicCompletion K)) x := by
  have hterm : ∀ n, Cox.ClassFieldConvergentSeries.term (PowerSeries.log (v.adicCompletion K)) x
      (n + 1) = logTerm K v x n := by
    intro n
    simp only [Cox.ClassFieldConvergentSeries.term, PowerSeries.coeff_log, logTerm,
      Nat.add_one_ne_zero, if_false, map_div₀, map_pow, map_neg, map_one, map_natCast]
    ring
  have hsum : Summable (Cox.ClassFieldConvergentSeries.term
      (PowerSeries.log (v.adicCompletion K)) x) := by
    rw [← summable_nat_add_iff 1]
    simpa only [hterm] using hx
  rw [logValue, Cox.ClassFieldConvergentSeries.value, hsum.tsum_eq_zero_add]
  have h0 : Cox.ClassFieldConvergentSeries.term (PowerSeries.log (v.adicCompletion K)) x 0 = 0 := by
    simp [Cox.ClassFieldConvergentSeries.term]
  rw [h0, zero_add]
  exact tsum_congr fun n => (hterm n).symm

/-- The formal exponential coefficients give exactly the source's evaluated terms. -/
theorem expValue_eq_powerSeries_value (x : v.adicCompletion K) :
    expValue K v x = Cox.ClassFieldConvergentSeries.value
      (PowerSeries.exp (v.adicCompletion K)) x := by
  rw [expValue, Cox.ClassFieldConvergentSeries.value]
  congr 1
  funext n
  rw [expTerm, Cox.ClassFieldConvergentSeries.term, PowerSeries.coeff_exp, map_div₀, map_one,
    map_natCast, one_div, div_eq_mul_inv, mul_comm]

/-- Separate the exponential constant before bounding its positive-degree tail. -/
theorem expValue_sub_one_eq_tsum_succ (x : v.adicCompletion K)
    (hx : Summable (expTerm K v x)) :
    expValue K v x - 1 = ∑' n, expTerm K v x (n + 1) := by
  rw [expValue, hx.tsum_eq_zero_add]
  simp [expTerm]

/-- On the geometric convergence ball, the logarithm does not increase the input norm. -/
theorem logValue_norm_le (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : v.adicCompletion K)‖ < 1) (x : v.adicCompletion K)
    (hx : ‖(p : v.adicCompletion K)‖⁻¹ * ‖x‖ < 1) :
    ‖logValue K v x‖ ≤ ‖x‖ := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have hpx : ‖(p : v.adicCompletion K)‖⁻¹ * ‖x‖ ≤ 1 := hx.le
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg x) fun n => ?_
  calc ‖logTerm K v x n‖ ≤ ‖x‖ * (‖(p : v.adicCompletion K)‖⁻¹ * ‖x‖) ^ n :=
        Cox.ClassFieldSeriesBounds.log_term_norm_le (v.adicCompletion K) p hp x n
    _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) hpx)
        (norm_nonneg _)
    _ = ‖x‖ := mul_one _

/-- The nonconstant exponential tail likewise does not increase the input norm. -/
theorem expValue_sub_one_norm_le (p : ℕ) [Fact p.Prime]
    (hp : ‖(p : v.adicCompletion K)‖ < 1) (x : v.adicCompletion K)
    (hx : ‖(p : v.adicCompletion K)‖⁻¹ * ‖x‖ < 1) :
    ‖expValue K v x - 1‖ ≤ ‖x‖ := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have hsum : Summable (expTerm K v x) :=
    Cox.ClassFieldSeriesBounds.exp_summable_of_norm_lt (v.adicCompletion K) p hp x hx
  have hpx : ‖(p : v.adicCompletion K)‖⁻¹ * ‖x‖ ≤ 1 := hx.le
  rw [expValue_sub_one_eq_tsum_succ K v x hsum]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg x) fun n => ?_
  calc ‖expTerm K v x (n + 1)‖ ≤ ‖x‖ * (‖(p : v.adicCompletion K)‖⁻¹ * ‖x‖) ^ n :=
        Cox.ClassFieldSeriesBounds.exp_term_succ_norm_le (v.adicCompletion K) p hp x n
    _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) hpx)
        (norm_nonneg _)
    _ = ‖x‖ := mul_one _

/-- The logarithm converges on the maximal ideal, since the linear valuation growth
of xⁿ dominates the valuation of n. -/
theorem log_summable (x : v.adicCompletionIntegers K)
    (hx : x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    Summable (logTerm K v (x : v.adicCompletion K)) := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  obtain ⟨p, hp, hp1⟩ := exists_prime_norm_lt_one K v
  haveI : Fact p.Prime := ⟨hp⟩
  exact Cox.ClassFieldSeriesBounds.log_summable_of_norm_lt_one (v.adicCompletion K) p hp1 _
    ((mem_completed_maximalIdeal_iff_norm_lt_one K v x).mp hx)

/-- The factorial valuation bound gives a positive depth on which the exponential converges. -/
theorem exists_exp_summable :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ x : v.adicCompletionIntegers K,
      x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
        Summable (expTerm K v (x : v.adicCompletion K)) := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  obtain ⟨p, hp, hp1⟩ := exists_prime_norm_lt_one K v
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < ‖(p : v.adicCompletion K)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  obtain ⟨t₀, ht₀⟩ := exists_ideal_depth_norm_lt K v _ hp0
  refine ⟨t₀, fun t ht x hx => ?_⟩
  have hxp := ht₀ t ht x hx
  exact Cox.ClassFieldSeriesBounds.exp_summable_of_norm_lt (v.adicCompletion K) p hp1 _
    ((inv_mul_lt_one₀ hp0).mpr hxp)

/-- On a sufficiently deep ideal, every higher logarithm term stays in that ideal. -/
theorem exists_log_preserves_filtration :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ x : v.adicCompletionIntegers K,
      x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
        ∃ y : v.adicCompletionIntegers K,
          y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t ∧
            (y : v.adicCompletion K) = logValue K v (x : v.adicCompletion K) := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  obtain ⟨p, hp, hp1⟩ := exists_prime_norm_lt_one K v
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < ‖(p : v.adicCompletion K)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  obtain ⟨t₀, ht₀⟩ := exists_ideal_depth_norm_lt K v _ hp0
  refine ⟨t₀, fun t ht x hx => ?_⟩
  have hxp := ht₀ t ht x hx
  exact exists_integer_mem_ideal_of_norm_le K v t x hx _
    (logValue_norm_le K v p hp1 _ ((inv_mul_lt_one₀ hp0).mpr hxp))

/-- Subtracting the constant term of the deep exponential keeps the same ideal depth. -/
theorem exists_exp_preserves_filtration :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ x : v.adicCompletionIntegers K,
      x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
        ∃ y : v.adicCompletionIntegers K,
          y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t ∧
            (y : v.adicCompletion K) = expValue K v (x : v.adicCompletion K) - 1 := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  obtain ⟨p, hp, hp1⟩ := exists_prime_norm_lt_one K v
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < ‖(p : v.adicCompletion K)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  obtain ⟨t₀, ht₀⟩ := exists_ideal_depth_norm_lt K v _ hp0
  refine ⟨t₀, fun t ht x hx => ?_⟩
  have hxp := ht₀ t ht x hx
  exact exists_integer_mem_ideal_of_norm_le K v t x hx _
    (expValue_sub_one_norm_le K v p hp1 _ ((inv_mul_lt_one₀ hp0).mpr hxp))

end Cox.ClassFieldTheory.LocalCyclic
