/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.Euclidean

/-!
# `ℚ(√-6)` Unique factorization

This file develops the unique factorization part of the `ℚ(√-6)` number field example.
-/

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors QuadraticAlgebra

namespace NumberField.SqrtNegSix

/-- The two essentially different factorisations of `6` in `ℤ[√-6]`: `6 = 2 · 3` and
`6 = -θ²` (i.e. `6 = -√-6 · √-6`). -/
theorem six_eq_neg_theta_sq : (6 : 𝓞 K) = -(thetaInt * thetaInt) := by
  rw [← sq, thetaInt_sq]
  ring

private theorem intNorm_two : Algebra.norm ℤ (2 : 𝓞 K) = 4 := by
  have h := intNorm_eq_normForm 2 0
  have heq : (2 : 𝓞 K) = (2 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt := by
    simp
  rw [← heq] at h
  exact h

private theorem intNorm_three : Algebra.norm ℤ (3 : 𝓞 K) = 9 := by
  have h := intNorm_eq_normForm 3 0
  have heq : (3 : 𝓞 K) = (3 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt := by
    simp
  rw [← heq] at h
  exact h

private theorem intNorm_thetaInt : Algebra.norm ℤ thetaInt = 6 := by
  have h := intNorm_eq_normForm 0 1
  have heq : thetaInt = (0 : ℤ) • (1 : 𝓞 K) + (1 : ℤ) • thetaInt := by
    simp
  rw [← heq] at h
  exact h

/-- `2` is irreducible in `ℤ[√-6]` (no element has norm `2`). -/
theorem irreducible_two : Irreducible (2 : 𝓞 K) := by
  refine ⟨?_, ?_⟩
  · intro hunit
    have hunitnorm := (isUnit_iff_intNorm_eq_one (2 : 𝓞 K)).mp hunit
    rw [intNorm_two] at hunitnorm
    norm_num at hunitnorm
  · intro a b hmul
    by_cases ha : IsUnit a
    · exact Or.inl ha
    by_cases hb : IsUnit b
    · exact Or.inr hb
    exfalso
    have hmulN : Algebra.norm ℤ a * Algebra.norm ℤ b = 4 := by
      rw [← map_mul, ← hmul, intNorm_two]
    let A : ℤ := Algebra.norm ℤ a
    let B : ℤ := Algebra.norm ℤ b
    have hAB : A * B = 4 := by simpa [A, B] using hmulN
    have hA_nonneg : 0 ≤ A := by simpa [A] using intNorm_nonneg a
    have hB_nonneg : 0 ≤ B := by simpa [B] using intNorm_nonneg b
    have hA_ne1 : A ≠ 1 := by
      intro hA1
      exact ha ((isUnit_iff_intNorm_eq_one a).mpr (by simpa [A] using hA1))
    have hB_ne1 : B ≠ 1 := by
      intro hB1
      exact hb ((isUnit_iff_intNorm_eq_one b).mpr (by simpa [B] using hB1))
    have hA_ne2 : A ≠ 2 := by
      intro hA2
      exact intNorm_ne_two a (by simpa [A] using hA2)
    have hB_pos : 0 < B := by nlinarith
    have hA_le : A ≤ 4 := by nlinarith
    interval_cases A
    · omega
    · exact hA_ne1 rfl
    · exact hA_ne2 rfl
    · omega
    · have hB1 : B = 1 := by nlinarith
      exact hB_ne1 hB1

/-- `3` is irreducible in `ℤ[√-6]` (no element has norm `3`). -/
theorem irreducible_three : Irreducible (3 : 𝓞 K) := by
  refine ⟨?_, ?_⟩
  · intro hunit
    have hunitnorm := (isUnit_iff_intNorm_eq_one (3 : 𝓞 K)).mp hunit
    rw [intNorm_three] at hunitnorm
    norm_num at hunitnorm
  · intro a b hmul
    by_cases ha : IsUnit a
    · exact Or.inl ha
    by_cases hb : IsUnit b
    · exact Or.inr hb
    exfalso
    have hmulN : Algebra.norm ℤ a * Algebra.norm ℤ b = 9 := by
      rw [← map_mul, ← hmul, intNorm_three]
    let A : ℤ := Algebra.norm ℤ a
    let B : ℤ := Algebra.norm ℤ b
    have hAB : A * B = 9 := by simpa [A, B] using hmulN
    have hA_nonneg : 0 ≤ A := by simpa [A] using intNorm_nonneg a
    have hB_nonneg : 0 ≤ B := by simpa [B] using intNorm_nonneg b
    have hA_ne1 : A ≠ 1 := by
      intro hA1
      exact ha ((isUnit_iff_intNorm_eq_one a).mpr (by simpa [A] using hA1))
    have hB_ne1 : B ≠ 1 := by
      intro hB1
      exact hb ((isUnit_iff_intNorm_eq_one b).mpr (by simpa [B] using hB1))
    have hA_ne3 : A ≠ 3 := by
      intro hA3
      exact intNorm_ne_three a (by simpa [A] using hA3)
    have hB_pos : 0 < B := by nlinarith
    have hA_le : A ≤ 9 := by nlinarith
    interval_cases A
    · omega
    · exact hA_ne1 rfl
    · omega
    · exact hA_ne3 rfl
    · omega
    · omega
    · omega
    · omega
    · omega
    · have hB1 : B = 1 := by nlinarith
      exact hB_ne1 hB1

/-- `θ = √-6` is irreducible in `ℤ[√-6]` (its norm `6` only factors as `2 · 3`, and neither
norm is attained). -/
theorem irreducible_theta : Irreducible thetaInt := by
  refine ⟨?_, ?_⟩
  · intro hunit
    have hunitnorm := (isUnit_iff_intNorm_eq_one thetaInt).mp hunit
    rw [intNorm_thetaInt] at hunitnorm
    norm_num at hunitnorm
  · intro a b hmul
    by_cases ha : IsUnit a
    · exact Or.inl ha
    by_cases hb : IsUnit b
    · exact Or.inr hb
    exfalso
    have hmulN : Algebra.norm ℤ a * Algebra.norm ℤ b = 6 := by
      rw [← map_mul, ← hmul, intNorm_thetaInt]
    let A : ℤ := Algebra.norm ℤ a
    let B : ℤ := Algebra.norm ℤ b
    have hAB : A * B = 6 := by simpa [A, B] using hmulN
    have hA_nonneg : 0 ≤ A := by simpa [A] using intNorm_nonneg a
    have hB_nonneg : 0 ≤ B := by simpa [B] using intNorm_nonneg b
    have hA_ne1 : A ≠ 1 := by
      intro hA1
      exact ha ((isUnit_iff_intNorm_eq_one a).mpr (by simpa [A] using hA1))
    have hB_ne1 : B ≠ 1 := by
      intro hB1
      exact hb ((isUnit_iff_intNorm_eq_one b).mpr (by simpa [B] using hB1))
    have hA_ne2 : A ≠ 2 := by
      intro hA2
      exact intNorm_ne_two a (by simpa [A] using hA2)
    have hA_ne3 : A ≠ 3 := by
      intro hA3
      exact intNorm_ne_three a (by simpa [A] using hA3)
    have hB_pos : 0 < B := by nlinarith
    have hA_le : A ≤ 6 := by nlinarith
    interval_cases A
    · omega
    · exact hA_ne1 rfl
    · exact hA_ne2 rfl
    · exact hA_ne3 rfl
    · omega
    · omega
    · have hB1 : B = 1 := by nlinarith
      exact hB_ne1 hB1

/-- `2` is irreducible but not prime: it divides `θ · θ = -6` without dividing `θ`. Hence
`ℤ[√-6]` is not a unique factorisation domain. -/
theorem two_not_prime : ¬ Prime (2 : 𝓞 K) := by
  intro hprime
  have hnot_dvd : ¬ (2 : 𝓞 K) ∣ thetaInt := by
    rintro ⟨a, ha⟩
    have hmem : thetaInt ∈ Ideal.span ({(2 : 𝓞 K)} : Set (𝓞 K)) := by
      exact Ideal.mem_span_singleton.mpr ⟨a, by rw [ha]⟩
    have heq : primeAboveTwo = Ideal.span ({(2 : 𝓞 K)} : Set (𝓞 K)) := by
      apply le_antisymm
      · rw [primeAboveTwo, Ideal.span_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact Ideal.mem_span_singleton_self _
        · exact hmem
      · rw [primeAboveTwo]
        apply Ideal.span_mono
        intro z hz
        simp only [Set.mem_singleton_iff] at hz
        simp [hz]
    have hnorm := congrArg Ideal.absNorm heq
    have hspan : Ideal.absNorm (Ideal.span ({(2 : 𝓞 K)} : Set (𝓞 K))) = 4 := by
      have h := intNorm_eq_normForm 2 0
      have heq2 : (2 : 𝓞 K) = (2 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt := by
        simp
      rw [Ideal.absNorm_span_singleton, heq2, h]
      rfl
    rw [absNorm_primeAboveTwo, hspan] at hnorm
    norm_num at hnorm
  have hdiv : (2 : 𝓞 K) ∣ thetaInt * thetaInt := by
    refine ⟨(-3 : 𝓞 K), ?_⟩
    rw [show thetaInt * thetaInt = thetaInt ^ 2 by ring, thetaInt_sq]
    ring
  rcases hprime.dvd_or_dvd hdiv with h | h
  · exact hnot_dvd h
  · exact hnot_dvd h

/-- `ℤ[√-6]` is not a unique factorisation monoid (equivalently, class number `> 1`). -/
theorem not_uniqueFactorizationMonoid : ¬ UniqueFactorizationMonoid (𝓞 K) := by
  intro hufd
  have hpid : IsPrincipalIdealRing (𝓞 K) := by
    exact IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid (𝓞 K)
  exact not_isPrincipalIdealRing hpid


end NumberField.SqrtNegSix
