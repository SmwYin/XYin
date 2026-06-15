/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.PrimeSplitting

/-!
# `ℚ(∛3)` ClassGroup

Fractional ideals, ideal representatives, class number, PID/UFD consequences, and class group
structure.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Fractional Ideals
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

abbrev cubeRootThreeFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.spanSingleton (𝓞 K)⁰ cubeRootThree

abbrev ramifiedPrimeFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  (Ideal.span {thetaInt} : FractionalIdeal (𝓞 K)⁰ K)

theorem cubeRootThree_mem_fractionalIdeal :
    cubeRootThree ∈ cubeRootThreeFractionalIdeal := by
  sorry

theorem cubeRootThreeFractionalIdeal_absNorm :
    FractionalIdeal.absNorm cubeRootThreeFractionalIdeal = |Algebra.norm ℚ cubeRootThree| := by
  sorry

theorem ramifiedPrimeFractionalIdeal_ne_zero :
    ramifiedPrimeFractionalIdeal ≠ 0 := by
  sorry

end NumberField.CubeRootThree


/-!
## Class Group
-/

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CubeRootThree

/-- Numerical bounds for `√243 = 9√3 ≈ 15.588`, used in the Minkowski-bound computation. -/
theorem sqrt_243_bounds : (15.58 : ℝ) < Real.sqrt 243 ∧ Real.sqrt 243 < 15.59 := by
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 243 by norm_num)
  have hnn := Real.sqrt_nonneg 243
  constructor
  · nlinarith [hsq, hnn]
  · nlinarith [hsq, hnn]

/-- The class number of `ℚ(∛3)` is `1`. The Minkowski bound is
`(4/π) · (3!/3³) · √243 ≈ 4.41`, and the primes `2` and `3` below it are products of principal
primes (`N(θ - 1) = 2`, `(3) = (θ)³`), cf. section 5. -/
theorem classNumber_eq_one : NumberField.classNumber K = 1 := by
  rw [NumberField.classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hp hprime P hPmem _
  have hPprime : P.IsPrime := hPmem.1
  have hpmem : ((p : ℕ) : 𝓞 K) ∈ P := by
    have hover := hPmem.2.over
    have hmem : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ P := by
      rw [← hover]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.under, Ideal.mem_comap] at hmem
    simpa [algebraMap_int_eq] using hmem
  have hple : p ≤ 4 := by
    have h2 := (Finset.mem_Icc.mp hp).2
    have h5 : ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        (((Module.finrank ℚ K).factorial : ℝ) /
          ((Module.finrank ℚ K : ℝ)) ^ (Module.finrank ℚ K) *
            Real.sqrt (|NumberField.discr K| : ℝ))⌋₊ < 5 := by
      rw [Nat.floor_lt (by positivity)]
      rw [nrComplexPlaces_eq_one, degree_eq_three, numberField_discr_eq]
      have hx : (4 / Real.pi) ^ 1 * (((Nat.factorial 3 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) ^ (3 : ℕ) *
          Real.sqrt (|(-243 : ℤ)| : ℝ)) = 8 * Real.sqrt 243 / (9 * Real.pi) := by
        rw [pow_one]
        norm_num [Nat.factorial]
        ring
      rw [hx, div_lt_iff₀ (by positivity)]
      have hπ1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
      have hs2 : Real.sqrt 243 < 15.59 := sqrt_243_bounds.2
      push_cast
      nlinarith
    omega
  have hpge := (Finset.mem_Icc.mp hp).1
  interval_cases p
  · exact absurd hprime (by norm_num)
  · rcases eq_of_two_mem P hPprime (by exact_mod_cast hpmem) with h | h <;> rw [h]
    · exact ⟨⟨thetaInt - 1, rfl⟩⟩
    · exact ⟨⟨thetaInt ^ 2 + thetaInt + 1, rfl⟩⟩
  · rw [eq_span_theta_of_three_mem P hPprime (by exact_mod_cast hpmem)]
    exact ⟨⟨thetaInt, rfl⟩⟩
  · exact absurd hprime (by norm_num)

/-- The ring of integers `ℤ[θ]` is a principal ideal domain — the ring-theoretic content of
class number one. -/
theorem isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 K) := by
  rw [← NumberField.classNumber_eq_one_iff]
  exact classNumber_eq_one

/-- The ring of integers `ℤ[θ]` is a unique factorization monoid. -/
theorem uniqueFactorizationMonoid : UniqueFactorizationMonoid (𝓞 K) := by
  haveI : IsPrincipalIdealRing (𝓞 K) := isPrincipalIdealRing
  infer_instance

/-- The class group of `𝓞 K` is trivial. -/
theorem classGroupStructure : Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1)) := by
  have h1 : Nat.card (ClassGroup (𝓞 K)) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup (𝓞 K)) := (Nat.card_eq_one_iff_unique.mp h1).1
  haveI : Unique (ClassGroup (𝓞 K)) := uniqueOfSubsingleton 1
  exact ⟨MulEquiv.ofUnique⟩

/-- The unit ideal as the concrete representative of the unique ideal class. -/
abbrev unitIdealRepresentative : (Ideal (𝓞 K))⁰ := ⟨(⊤ : Ideal (𝓞 K)), by simp⟩

/-- Every ideal class is represented by the unit ideal. -/
theorem classGroupRepresentative (C : ClassGroup (𝓞 K)) :
    C = ClassGroup.mk0 unitIdealRepresentative := by
  have h1 : Nat.card (ClassGroup (𝓞 K)) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup (𝓞 K)) := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Subsingleton.elim _ _


end NumberField.CubeRootThree
