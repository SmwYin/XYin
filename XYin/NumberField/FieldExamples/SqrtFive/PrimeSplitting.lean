/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import Mathlib.Algebra.Polynomial.SpecificDegree
import XYin.NumberField.FieldExamples.SqrtFive.RingOfIntegers
import XYin.NumberField.FieldExamples.Common

/-!
# `ℚ(√5)` PrimeSplitting

Prime splitting, Kummer-Dedekind computations, ramification, and different-related statements.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Prime Splitting
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open NumberField.FieldExamples

namespace NumberField.SqrtFive
/-- `√5 = 2φ - 1` as an element of `𝓞 K`. -/
noncomputable def sqrtFiveIntO : 𝓞 K := 2 * goldenIntO - 1

/-- `5` is (totally) ramified: `(5) = (√5)²` as ideals of `𝓞 K`, directly from
`(2φ - 1)² = 5`. It is the unique ramified prime, matching the discriminant `5`. -/
theorem span_five_eq :
    Ideal.span {(5 : 𝓞 K)} = Ideal.span {sqrtFiveIntO} ^ 2 := by
  rw [Ideal.span_singleton_pow,
    show sqrtFiveIntO ^ 2 = (5 : 𝓞 K) from by
      apply Subtype.ext
      change (2 * goldenRoot - 1) ^ 2 = (5 : K)
      exact sqrtFiveRoot_sq]

/-- The prime `(√5)` above `5` has norm `5` (residue degree `f = 1`). -/
theorem absNorm_span_sqrtFiveIntO : Ideal.absNorm (Ideal.span {sqrtFiveIntO}) = 5 := by
  have hsqrt : sqrtFiveIntO = (-1 : ℤ) • (1 : 𝓞 K) + (2 : ℤ) • goldenIntO := by
    simp only [sqrtFiveIntO, zsmul_eq_mul]
    push_cast
    ring
  have h := intNorm_eq_normForm (-1) 2
  rw [← hsqrt] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- `(√5)` is a prime ideal — the unique prime of `𝓞 K` above `5`. -/
theorem isPrime_span_sqrtFiveIntO : (Ideal.span {sqrtFiveIntO}).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_span_sqrtFiveIntO]
  exact (by norm_num : Nat.Prime 5)

/-- The ramified prime `(√5)` lies over `(5)`. -/
theorem liesOver_span_sqrtFiveIntO :
    (Ideal.span {sqrtFiveIntO}).LiesOver (Ideal.span {(5 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_sqrtFiveIntO.ne_top
    (show Prime (5 : ℤ) by norm_num)]
  change (5 : 𝓞 K) ∈ Ideal.span {sqrtFiveIntO}
  rw [← show sqrtFiveIntO ^ 2 = (5 : 𝓞 K) from by
    apply Subtype.ext
    change (2 * goldenRoot - 1) ^ 2 = (5 : K)
    exact sqrtFiveRoot_sq]
  simpa [pow_two] using
    Ideal.mul_mem_right sqrtFiveIntO (Ideal.span {sqrtFiveIntO})
      (Ideal.mem_span_singleton_self sqrtFiveIntO)

/-- The ramified prime `(√5)` has inertia degree `1` over `5`. -/
theorem inertiaDeg_span_sqrtFiveIntO :
    (Ideal.span {(5 : ℤ)}).inertiaDeg (Ideal.span {sqrtFiveIntO}) = 1 := by
  haveI : (Ideal.span {sqrtFiveIntO}).LiesOver (Ideal.span {(5 : ℤ)}) :=
    liesOver_span_sqrtFiveIntO
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {sqrtFiveIntO})
    (p := 5) (by norm_num : Nat.Prime 5)
  rw [absNorm_span_sqrtFiveIntO] at h
  exact ((Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 5)).mp h.symm).2

/-- The ramified prime `(√5)` has ramification index `2` over `5`. -/
theorem ramificationIdx_span_sqrtFiveIntO :
    (Ideal.span {(5 : ℤ)}).ramificationIdx (Ideal.span {sqrtFiveIntO}) = 2 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(5 : 𝓞 K)} ≤ Ideal.span {sqrtFiveIntO} ^ 2
    rw [span_five_eq]
  · intro hle3
    have hdvd : Ideal.absNorm (Ideal.span {sqrtFiveIntO} ^ 3) ∣
        Ideal.absNorm (Ideal.span {((5 : ℤ) : 𝓞 K)}) := by
      simpa [Ideal.map_span, Set.image_singleton] using Ideal.absNorm_dvd_absNorm_of_le hle3
    have hnorm5 : Ideal.absNorm (Ideal.span {((5 : ℤ) : 𝓞 K)}) = 25 := by
      change Ideal.absNorm (Ideal.span {(5 : 𝓞 K)}) = 25
      have h := intNorm_eq_normForm 5 0
      have h5 : (5 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • goldenIntO =
          (5 : 𝓞 K) := by simp
      rw [h5] at h
      norm_num at h
      rw [Ideal.absNorm_span_singleton, h]
      rfl
    have hnorm3 : Ideal.absNorm (Ideal.span {sqrtFiveIntO} ^ 3) = 125 := by
      rw [map_pow, absNorm_span_sqrtFiveIntO]
      norm_num
    rw [hnorm3, hnorm5] at hdvd
    norm_num at hdvd

private theorem absNorm_ne_two (P : Ideal (𝓞 K)) : Ideal.absNorm P ≠ 2 := by
  intro hcard
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcard
  haveI : Finite ((𝓞 K) ⧸ P) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card ((𝓞 K) ⧸ P) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) (by norm_num) hcard'
  obtain ⟨t, ht⟩ := e.surjective (Ideal.Quotient.mk P goldenIntO)
  have ht2 : t ^ 2 = t + 1 := by
    apply e.injective
    rw [map_pow, ht, map_add, ht, map_one, ← map_pow (Ideal.Quotient.mk P),
      goldenIntO_sq, map_add, map_one]
  clear ht
  revert t
  decide

private theorem absNorm_ne_three (P : Ideal (𝓞 K)) : Ideal.absNorm P ≠ 3 := by
  intro hcard
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcard
  haveI : Finite ((𝓞 K) ⧸ P) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card ((𝓞 K) ⧸ P) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) (by norm_num) hcard'
  obtain ⟨t, ht⟩ := e.surjective (Ideal.Quotient.mk P goldenIntO)
  have ht2 : t ^ 2 = t + 1 := by
    apply e.injective
    rw [map_pow, ht, map_add, ht, map_one, ← map_pow (Ideal.Quotient.mk P),
      goldenIntO_sq, map_add, map_one]
  clear ht
  revert t
  decide

/-- `2` is inert in `ℚ(√5)`: `X² - X - 1` is irreducible mod `2`, so `(2)` is itself prime
(of norm `4`). -/
theorem isPrime_span_two : (Ideal.span {(2 : 𝓞 K)}).IsPrime := by
  have habs4 : Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) = 4 := by
    have h := intNorm_eq_normForm 2 0
    have h2 : (2 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • goldenIntO = 2 := by
      simp
    rw [h2] at h
    norm_num at h
    rw [Ideal.absNorm_span_singleton, h]
    rfl
  have htop : Ideal.span {(2 : 𝓞 K)} ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at habs4
    norm_num at habs4
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ htop
  have hdvd : Ideal.absNorm M ∣ 4 := habs4 ▸ Ideal.absNorm_dvd_absNorm_of_le hMle
  have hM1 : Ideal.absNorm M ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hMmax.ne_top
  have hM2 : Ideal.absNorm M ≠ 2 := absNorm_ne_two M
  have hM4 : Ideal.absNorm M = 4 := by
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Ideal.absNorm M ∣ 2 ^ 2 from hdvd)
    interval_cases k
    · rw [pow_zero] at hkeq
      exact absurd hkeq hM1
    · rw [pow_one] at hkeq
      exact absurd hkeq hM2
    · rw [hkeq]
      norm_num
  have heq := eq_of_le_of_absNorm_eq hMle habs4 hM4 (by norm_num)
  rw [heq]
  exact hMmax.isPrime

/-- The inert prime `(2)` has norm `4` (residue degree `f = 2`). -/
theorem absNorm_span_two : Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) = 4 := by
  have h := intNorm_eq_normForm 2 0
  have h2 : (2 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • goldenIntO = 2 := by
    simp
  rw [h2] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- The inert prime `(2)` lies over `(2)`. -/
theorem liesOver_span_two :
    (Ideal.span {(2 : 𝓞 K)}).LiesOver (Ideal.span {(2 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_two.ne_top
    (show Prime (2 : ℤ) by norm_num)]
  change (2 : 𝓞 K) ∈ Ideal.span {(2 : 𝓞 K)}
  exact Ideal.mem_span_singleton_self _

/-- The inert prime `(2)` has inertia degree `2`. -/
theorem inertiaDeg_span_two :
    (Ideal.span {(2 : ℤ)}).inertiaDeg (Ideal.span {(2 : 𝓞 K)}) = 2 := by
  haveI : (Ideal.span {(2 : 𝓞 K)}).LiesOver (Ideal.span {(2 : ℤ)}) :=
    liesOver_span_two
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {(2 : 𝓞 K)})
    (p := 2) Nat.prime_two
  rw [absNorm_span_two] at h
  change 2 ^ 2 = 2 ^ (Ideal.span {(2 : ℤ)}).inertiaDeg
    (Ideal.span {(2 : 𝓞 K)}) at h
  exact Nat.pow_right_injective Nat.prime_two.one_lt h.symm

/-- `3` is inert in `ℚ(√5)`: `5` is not a square mod `3`, so `(3)` is itself prime (of norm
`9`). -/
theorem isPrime_span_three : (Ideal.span {(3 : 𝓞 K)}).IsPrime := by
  have habs9 : Ideal.absNorm (Ideal.span {(3 : 𝓞 K)}) = 9 := by
    have h := intNorm_eq_normForm 3 0
    have h3 : (3 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • goldenIntO = 3 := by
      simp
    rw [h3] at h
    norm_num at h
    rw [Ideal.absNorm_span_singleton, h]
    rfl
  have htop : Ideal.span {(3 : 𝓞 K)} ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at habs9
    norm_num at habs9
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ htop
  have hdvd : Ideal.absNorm M ∣ 9 := habs9 ▸ Ideal.absNorm_dvd_absNorm_of_le hMle
  have hM1 : Ideal.absNorm M ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hMmax.ne_top
  have hM3 : Ideal.absNorm M ≠ 3 := absNorm_ne_three M
  have hM9 : Ideal.absNorm M = 9 := by
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Ideal.absNorm M ∣ 3 ^ 2 from hdvd)
    interval_cases k
    · rw [pow_zero] at hkeq
      exact absurd hkeq hM1
    · rw [pow_one] at hkeq
      exact absurd hkeq hM3
    · rw [hkeq]
      norm_num
  have heq := eq_of_le_of_absNorm_eq hMle habs9 hM9 (by norm_num)
  rw [heq]
  exact hMmax.isPrime

/-- The inert prime `(3)` has norm `9`. -/
theorem absNorm_span_three : Ideal.absNorm (Ideal.span {(3 : 𝓞 K)}) = 9 := by
  have h := intNorm_eq_normForm 3 0
  have h3 : (3 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • goldenIntO =
      (3 : 𝓞 K) := by simp
  rw [h3] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- The inert prime `(3)` lies over `(3)`. -/
theorem liesOver_span_three :
    (Ideal.span {(3 : 𝓞 K)}).LiesOver (Ideal.span {(3 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_three.ne_top
    (show Prime (3 : ℤ) by norm_num)]
  change (3 : 𝓞 K) ∈ Ideal.span {(3 : 𝓞 K)}
  exact Ideal.mem_span_singleton_self _

/-- The inert prime `(3)` has inertia degree `2`. -/
theorem inertiaDeg_span_three :
    (Ideal.span {(3 : ℤ)}).inertiaDeg (Ideal.span {(3 : 𝓞 K)}) = 2 := by
  haveI : (Ideal.span {(3 : 𝓞 K)}).LiesOver (Ideal.span {(3 : ℤ)}) :=
    liesOver_span_three
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {(3 : 𝓞 K)})
    (p := 3) Nat.prime_three
  rw [absNorm_span_three] at h
  change 3 ^ 2 = 3 ^ (Ideal.span {(3 : ℤ)}).inertiaDeg
    (Ideal.span {(3 : 𝓞 K)}) at h
  exact Nat.pow_right_injective Nat.prime_three.one_lt h.symm

/-- The elementary identity `11 = (3 + φ)(4 - φ)` in `𝓞 K`. -/
theorem eleven_eq_mul : (11 : 𝓞 K) = (3 + goldenIntO) * (4 - goldenIntO) := by
  apply Subtype.ext
  change (11 : K) = (3 + goldenRoot) * (4 - goldenRoot)
  rw [show (3 + goldenRoot) * (4 - goldenRoot) = 12 + goldenRoot - goldenRoot ^ 2 by ring]
  rw [goldenRoot_sq]
  ring

/-- `11 ≡ 1 (mod 5)` splits: `11 = (3 + φ)(4 - φ)` and `(11)` is a product of two distinct
primes of norm `11`. -/
theorem span_eleven_eq :
    Ideal.span {(11 : 𝓞 K)} =
      Ideal.span {3 + goldenIntO} * Ideal.span {4 - goldenIntO} := by
  rw [Ideal.span_singleton_mul_span_singleton, ← eleven_eq_mul]

/-- The prime `(3 + φ)` above `11` has norm `11` (residue degree `f = 1`). -/
theorem absNorm_span_three_add_golden :
    Ideal.absNorm (Ideal.span {3 + goldenIntO}) = 11 := by
  have h := intNorm_eq_normForm 3 1
  have h3 : (3 : ℤ) • (1 : 𝓞 K) + (1 : ℤ) • goldenIntO = 3 + goldenIntO := by
    simp
  rw [h3] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- `(3 + φ)` is a prime ideal — one of the two primes of `𝓞 K` above `11`. -/
theorem isPrime_span_three_add_golden : (Ideal.span {3 + goldenIntO}).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_span_three_add_golden]
  exact (by norm_num : Nat.Prime 11)

/-- The prime `(4 - φ)` above `11` has norm `11` (residue degree `f = 1`). -/
theorem absNorm_span_four_sub_golden :
    Ideal.absNorm (Ideal.span {4 - goldenIntO}) = 11 := by
  have h := intNorm_eq_normForm 4 (-1)
  have h4 : (4 : ℤ) • (1 : 𝓞 K) + (-1 : ℤ) • goldenIntO = 4 - goldenIntO := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [h4] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- `(4 - φ)` is a prime ideal — the conjugate prime above `11`. -/
theorem isPrime_span_four_sub_golden : (Ideal.span {4 - goldenIntO}).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_span_four_sub_golden]
  exact (by norm_num : Nat.Prime 11)

/-- The split prime `(3 + φ)` lies over `(11)`. -/
theorem liesOver_span_three_add_golden :
    (Ideal.span {3 + goldenIntO}).LiesOver (Ideal.span {(11 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_three_add_golden.ne_top
    (show Prime (11 : ℤ) by norm_num)]
  change (11 : 𝓞 K) ∈ Ideal.span {3 + goldenIntO}
  rw [eleven_eq_mul]
  exact Ideal.mul_mem_right (4 - goldenIntO) (Ideal.span {3 + goldenIntO})
    (Ideal.mem_span_singleton_self (3 + goldenIntO))

/-- The split prime `(4 - φ)` lies over `(11)`. -/
theorem liesOver_span_four_sub_golden :
    (Ideal.span {4 - goldenIntO}).LiesOver (Ideal.span {(11 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_four_sub_golden.ne_top
    (show Prime (11 : ℤ) by norm_num)]
  change (11 : 𝓞 K) ∈ Ideal.span {4 - goldenIntO}
  rw [show (11 : 𝓞 K) = (4 - goldenIntO) * (3 + goldenIntO) from by
    rw [eleven_eq_mul]
    ring]
  exact Ideal.mul_mem_right (3 + goldenIntO) (Ideal.span {4 - goldenIntO})
    (Ideal.mem_span_singleton_self (4 - goldenIntO))

/-- The split prime `(3 + φ)` has inertia degree `1` over `11`. -/
theorem inertiaDeg_span_three_add_golden :
    (Ideal.span {(11 : ℤ)}).inertiaDeg (Ideal.span {3 + goldenIntO}) = 1 := by
  haveI : (Ideal.span {3 + goldenIntO}).LiesOver (Ideal.span {(11 : ℤ)}) :=
    liesOver_span_three_add_golden
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {3 + goldenIntO})
    (p := 11) (by norm_num : Nat.Prime 11)
  rw [absNorm_span_three_add_golden] at h
  exact ((Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 11)).mp h.symm).2

/-- The split prime `(4 - φ)` has inertia degree `1` over `11`. -/
theorem inertiaDeg_span_four_sub_golden :
    (Ideal.span {(11 : ℤ)}).inertiaDeg (Ideal.span {4 - goldenIntO}) = 1 := by
  haveI : (Ideal.span {4 - goldenIntO}).LiesOver (Ideal.span {(11 : ℤ)}) :=
    liesOver_span_four_sub_golden
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {4 - goldenIntO})
    (p := 11) (by norm_num : Nat.Prime 11)
  rw [absNorm_span_four_sub_golden] at h
  exact ((Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 11)).mp h.symm).2

/-- The two principal primes above `11` are distinct. -/
theorem primesAboveEleven_ne :
    Ideal.span ({3 + goldenIntO} : Set (𝓞 K)) ≠ Ideal.span {4 - goldenIntO} := by
  intro h
  have h4 : (4 : 𝓞 K) - goldenIntO ∈
      Ideal.span ({3 + goldenIntO} : Set (𝓞 K)) := by
    rw [h]
    exact Ideal.mem_span_singleton_self _
  have hs : sqrtFiveIntO ∈ Ideal.span ({3 + goldenIntO} : Set (𝓞 K)) := by
    rw [show sqrtFiveIntO = (3 + goldenIntO) - ((4 : 𝓞 K) - goldenIntO) from by
      simp only [sqrtFiveIntO]
      ring]
    exact Ideal.sub_mem _ (Ideal.mem_span_singleton_self _) h4
  have h5 : (5 : 𝓞 K) ∈ Ideal.span ({3 + goldenIntO} : Set (𝓞 K)) := by
    rw [show (5 : 𝓞 K) = sqrtFiveIntO * sqrtFiveIntO from by
      apply Subtype.ext
      change (5 : K) = (2 * goldenRoot - 1) * (2 * goldenRoot - 1)
      rw [← pow_two, sqrtFiveRoot_sq]]
    exact Ideal.mul_mem_right _ _ hs
  have h11 : (11 : 𝓞 K) ∈ Ideal.span ({3 + goldenIntO} : Set (𝓞 K)) := by
    rw [eleven_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h1 : (1 : 𝓞 K) ∈ Ideal.span ({3 + goldenIntO} : Set (𝓞 K)) := by
    rw [show (1 : 𝓞 K) = 11 - 2 * 5 from by norm_num]
    exact Ideal.sub_mem _ h11 (Ideal.mul_mem_left _ _ h5)
  have htop : Ideal.span ({3 + goldenIntO} : Set (𝓞 K)) = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr h1
  have habs := absNorm_span_three_add_golden
  rw [htop, Ideal.absNorm_top] at habs
  norm_num at habs

private theorem absNorm_span_natCast (p : ℕ) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 2 := by
  rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, degree_eq_two]

private theorem concreteIntegralBasis_zero_eq_one :
    concreteIntegralBasis 0 = (1 : 𝓞 K) := by
  apply Subtype.ext
  exact concreteIntegralBasis_basis_zero

private theorem concreteIntegralBasis_one_eq_goldenIntO :
    concreteIntegralBasis 1 = goldenIntO := by
  apply Subtype.ext
  exact concreteIntegralBasis_basis_one

private theorem li_one_golden : LinearIndependent ℤ ![(1 : 𝓞 K), goldenIntO] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_two] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  have hsum : ∑ i : Fin 2, g i • concreteIntegralBasis i = 0 := by
    rw [Fin.sum_univ_two, concreteIntegralBasis_zero_eq_one,
      concreteIntegralBasis_one_eq_goldenIntO]
    exact hg
  exact Fintype.linearIndependent_iff.mp concreteIntegralBasis.linearIndependent g hsum

private theorem exists_o5_coords (z : 𝓞 K) :
    ∃ A B : ℤ, z = A • (1 : 𝓞 K) + B • goldenIntO := by
  let A : ℤ := concreteIntegralBasis.repr z 0
  let B : ℤ := concreteIntegralBasis.repr z 1
  refine ⟨A, B, ?_⟩
  have hsum := concreteIntegralBasis.sum_repr z
  rw [Fin.sum_univ_two, concreteIntegralBasis_zero_eq_one,
    concreteIntegralBasis_one_eq_goldenIntO] at hsum
  simpa [A, B] using hsum.symm

/-- An element `A + B·φ` with `B = ±1` is never divisible by a rational prime `p ≥ 2`. -/
private theorem unit_golden_coeff_not_mem (p : ℕ) (hp : 2 ≤ p) (A B : ℤ)
    (hB : B = 1 ∨ B = -1) :
    ((A : ℤ) : 𝓞 K) + ((B : ℤ) : 𝓞 K) * goldenIntO ∉
      Ideal.span {((p : ℕ) : 𝓞 K)} := by
  intro hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨A', m, hzdec⟩ := exists_o5_coords z
  rw [hzdec] at hz
  have hsum : ∑ i : Fin 2,
      (![A - p * A', B - p * m] i) • (![(1 : 𝓞 K), goldenIntO] i) = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zsmul_eq_mul] at hz ⊢
    push_cast at hz ⊢
    linear_combination hz
  have hcoeff := Fintype.linearIndependent_iff.mp li_one_golden _ hsum 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hcoeff
  rcases hB with rfl | rfl
  · have h1 : (p : ℤ) ∣ 1 := ⟨m, by linarith [hcoeff]⟩
    have := Int.le_of_dvd one_pos h1
    omega
  · have h1 : (p : ℤ) ∣ 1 := ⟨-m, by linarith [hcoeff]⟩
    have := Int.le_of_dvd one_pos h1
    omega

/-- The splitting law at ramified primes: a rational prime `p` ramifies in `ℚ(√5)` iff
`p = 5`, i.e. iff `p` divides the discriminant `5`. -/
theorem ramified_iff_eq_five (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧
      Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔ p = 5 := by
  constructor
  · rintro ⟨P, hP, hle2⟩
    haveI : P.IsPrime := hP
    have hple : Ideal.span {((p : ℕ) : 𝓞 K)} ≤ P :=
      hle2.trans (Ideal.pow_le_self (by norm_num))
    have hpmemP : ((p : ℕ) : 𝓞 K) ∈ P := hple (Ideal.mem_span_singleton_self _)
    have hpne : ((p : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hPbot : P ≠ ⊥ := by
      intro h
      rw [h] at hpmemP
      exact hpne (Ideal.mem_bot.mp hpmemP)
    have habsp : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 2 :=
      absNorm_span_natCast p
    have habsPp2 : Ideal.absNorm P ∣ p ^ 2 :=
      habsp ▸ Ideal.absNorm_dvd_absNorm_of_le hple
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow hp).mp habsPp2
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hkeq
      exact hP.ne_top (Ideal.absNorm_eq_one_iff.mp hkeq)
    have hle2' : Ideal.map (algebraMap ℤ (𝓞 K))
        (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 2 := by
      simpa [Ideal.map_span, Set.image_singleton] using hle2
    have hno3 : ¬ Ideal.map (algebraMap ℤ (𝓞 K))
        (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 3 :=
      not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow hp habsp hkeq hk0
    have hunram : ¬ Algebra.IsUnramifiedAt ℤ P :=
      not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ hp hpmemP hPbot hle2'
        hno3
    have hPdiff : P ∣ differentIdeal ℤ (𝓞 K) := dvd_differentIdeal_iff.mpr hunram
    have habsP5 : Ideal.absNorm P ∣ 5 := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPdiff)
      rw [NumberField.absNorm_differentIdeal (K := K), numberField_discr_eq] at h
      simpa using h
    have hpdvd : p ∣ 5 := (hkeq ▸ dvd_pow_self p hk0).trans habsP5
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpdvd
  · rintro rfl
    refine ⟨Ideal.span {sqrtFiveIntO}, isPrime_span_sqrtFiveIntO, ?_⟩
    have hcast : ((5 : ℕ) : 𝓞 K) = (5 : 𝓞 K) := by norm_num
    rw [hcast, span_five_eq]

/-- The inert prime `(2)` is unramified: it has ramification index `1`. -/
theorem ramificationIdx_span_two :
    (Ideal.span {(2 : ℤ)}).ramificationIdx (Ideal.span {(2 : 𝓞 K)}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    simp
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧
        Ideal.span {(2 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {(2 : 𝓞 K)}, isPrime_span_two, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h25 := (ramified_iff_eq_five 2 Nat.prime_two).mp hram
    norm_num at h25

/-- The inert prime `(3)` is unramified: it has ramification index `1`. -/
theorem ramificationIdx_span_three :
    (Ideal.span {(3 : ℤ)}).ramificationIdx (Ideal.span {(3 : 𝓞 K)}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    simp
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧
        Ideal.span {(3 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {(3 : 𝓞 K)}, isPrime_span_three, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h35 := (ramified_iff_eq_five 3 Nat.prime_three).mp hram
    norm_num at h35

/-- Each split prime over `11` is unramified: `(3 + φ)` has ramification index `1`. -/
theorem ramificationIdx_span_three_add_golden :
    (Ideal.span {(11 : ℤ)}).ramificationIdx (Ideal.span {3 + goldenIntO}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    change Ideal.span {(11 : 𝓞 K)} ≤ Ideal.span {3 + goldenIntO}
    rw [span_eleven_eq]
    exact Ideal.mul_le_right
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧
        Ideal.span {(11 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {3 + goldenIntO}, isPrime_span_three_add_golden, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h115 := (ramified_iff_eq_five 11 (by norm_num)).mp hram
    norm_num at h115

/-- Each split prime over `11` is unramified: `(4 - φ)` has ramification index `1`. -/
theorem ramificationIdx_span_four_sub_golden :
    (Ideal.span {(11 : ℤ)}).ramificationIdx (Ideal.span {4 - goldenIntO}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    change Ideal.span {(11 : 𝓞 K)} ≤ Ideal.span {4 - goldenIntO}
    rw [span_eleven_eq]
    exact Ideal.mul_le_left
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧
        Ideal.span {(11 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {4 - goldenIntO}, isPrime_span_four_sub_golden, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h115 := (ramified_iff_eq_five 11 (by norm_num)).mp hram
    norm_num at h115

private theorem golden_sub_mem_span_natCast_of_one_mem_span_pair (p : ℕ) (c c' k₁ k₂ : ℤ)
    (hprod : (goldenIntO - (c : 𝓞 K)) *
        (goldenIntO - (c' : 𝓞 K)) =
      ((p : ℕ) : 𝓞 K) *
        ((k₁ : 𝓞 K) * goldenIntO + (k₂ : 𝓞 K)))
    (h1 : (1 : 𝓞 K) ∈
      Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c : 𝓞 K)}) :
    goldenIntO - (c' : 𝓞 K) ∈ Ideal.span {((p : ℕ) : 𝓞 K)} := by
  rw [Ideal.mem_span_pair] at h1
  obtain ⟨α, β, hαβ⟩ := h1
  rw [Ideal.mem_span_singleton]
  refine ⟨α * (goldenIntO - (c' : 𝓞 K)) +
    β * ((k₁ : 𝓞 K) * goldenIntO + (k₂ : 𝓞 K)), ?_⟩
  calc goldenIntO - (c' : 𝓞 K)
      = (α * ((p : ℕ) : 𝓞 K) + β * (goldenIntO - (c : 𝓞 K))) *
        (goldenIntO - (c' : 𝓞 K)) := by
        rw [hαβ, one_mul]
    _ = ((p : ℕ) : 𝓞 K) *
        (α * (goldenIntO - (c' : 𝓞 K)) +
          β * ((k₁ : 𝓞 K) * goldenIntO + (k₂ : 𝓞 K))) := by
        linear_combination β * hprod

private theorem absNorm_span_prime_golden_sub_of_mul (p : ℕ) (hp : p.Prime)
    (c c' k₁ k₂ : ℤ)
    (hprod : (goldenIntO - (c : 𝓞 K)) *
        (goldenIntO - (c' : 𝓞 K)) =
      ((p : ℕ) : 𝓞 K) *
        ((k₁ : 𝓞 K) * goldenIntO + (k₂ : 𝓞 K))) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K),
      goldenIntO - (c : 𝓞 K)}) = p := by
  let P : Ideal (𝓞 K) :=
    Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c : 𝓞 K)}
  change Ideal.absNorm P = p
  have hp_memP : ((p : ℕ) : 𝓞 K) ∈ P := Ideal.subset_span (Set.mem_insert _ _)
  have hgc_memP : goldenIntO - (c : 𝓞 K) ∈ P :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hPle : Ideal.span {((p : ℕ) : 𝓞 K)} ≤ P :=
    (Ideal.span_singleton_le_iff_mem _).mpr hp_memP
  have hPnot1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    intro htop
    have h1 : (1 : 𝓞 K) ∈ P := htop ▸ Submodule.mem_top
    change (1 : 𝓞 K) ∈
      Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c : 𝓞 K)} at h1
    have hgc' : goldenIntO - (c' : 𝓞 K) ∈
        Ideal.span {((p : ℕ) : 𝓞 K)} :=
      golden_sub_mem_span_natCast_of_one_mem_span_pair p c c' k₁ k₂ hprod h1
    refine unit_golden_coeff_not_mem p hp.two_le (-c') 1 (Or.inl rfl) ?_
    rw [show ((-c' : ℤ) : 𝓞 K) +
        ((1 : ℤ) : 𝓞 K) * goldenIntO =
      goldenIntO - (c' : 𝓞 K) by
      push_cast
      ring]
    exact hgc'
  have hPnotsq : Ideal.absNorm P ≠ p ^ 2 := by
    intro hNP
    have heq := eq_of_le_of_absNorm_eq hPle (absNorm_span_natCast p) hNP
      (pow_ne_zero 2 hp.pos.ne')
    refine unit_golden_coeff_not_mem p hp.two_le (-c) 1 (Or.inl rfl) ?_
    rw [show ((-c : ℤ) : 𝓞 K) +
        ((1 : ℤ) : 𝓞 K) * goldenIntO =
      goldenIntO - (c : 𝓞 K) by
      push_cast
      ring]
    rw [heq]
    exact hgc_memP
  exact eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq hp
    ((absNorm_span_natCast p) ▸ Ideal.absNorm_dvd_absNorm_of_le hPle) hPnot1 hPnotsq

private theorem exists_golden_root_of_absNorm_eq_prime (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 K)) (hNP : Ideal.absNorm P = p) :
    ∃ t : ZMod p, t ^ 2 = t + 1 := by
  have hcard : Nat.card ((𝓞 K) ⧸ P) = p := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hNP
    exact hNP
  haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero
    (by rw [hcard]; exact hp.pos.ne')
  haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card ((𝓞 K) ⧸ P) = p := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) hp hcard'
  obtain ⟨t, ht⟩ := e.surjective (Ideal.Quotient.mk P goldenIntO)
  have ht2 : t ^ 2 = t + 1 := by
    apply e.injective
    rw [map_pow, ht, map_add, ht, map_one, ← map_pow (Ideal.Quotient.mk P),
      goldenIntO_sq, map_add, map_one]
  exact ⟨t, ht2⟩

private theorem isSquare_five_of_absNorm_eq_prime (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 K)) (hNP : Ideal.absNorm P = p) :
    IsSquare ((5 : ℕ) : ZMod p) := by
  obtain ⟨t, ht2⟩ := exists_golden_root_of_absNorm_eq_prime p hp P hNP
  refine ⟨2 * t - 1, ?_⟩
  push_cast
  linear_combination -4 * ht2

private theorem pm_one_mod_five_of_splits (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) → p % 5 = 1 ∨ p % 5 = 4 := by
  have hnsq2 : ¬ IsSquare ((2 : ℕ) : ZMod 5) := by decide
  have hnsq3 : ¬ IsSquare ((3 : ℕ) : ZMod 5) := by decide
  rintro ⟨P, Q, hPprime, hQprime, hPQne, hspan⟩
  have hmul : Ideal.absNorm P * Ideal.absNorm Q = p ^ 2 := by
    rw [← _root_.map_mul Ideal.absNorm, ← hspan, absNorm_span_natCast]
  have hP1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hPprime.ne_top
  have hQ1 : Ideal.absNorm Q ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hQprime.ne_top
  have hNP : Ideal.absNorm P = p :=
    left_eq_prime_of_mul_eq_prime_sq_of_ne_one hp hmul hP1 hQ1
  by_cases hp2 : p = 2
  · exfalso
    subst hp2
    obtain ⟨t, ht⟩ := exists_golden_root_of_absNorm_eq_prime 2 Nat.prime_two P hNP
    revert t
    decide
  have hsq5 : IsSquare ((5 : ℕ) : ZMod p) :=
    isSquare_five_of_absNorm_eq_prime p hp P hNP
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hsqp : IsSquare ((p : ℕ) : ZMod 5) :=
    (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p)
      (by norm_num) hp2).mpr hsq5
  have hcast : ((p : ℕ) : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) :=
    (ZMod.natCast_mod p 5).symm
  rw [hcast] at hsqp
  have hne0 : p % 5 ≠ 0 := by
    intro h0
    exact hp5 (((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm)
  have hcases : p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
    omega
  rcases hcases with h | h | h | h | h
  · exact absurd h hne0
  · exact Or.inl h
  · rw [h] at hsqp
    exact absurd hsqp hnsq2
  · rw [h] at hsqp
    exact absurd hsqp hnsq3
  · exact Or.inr h

private theorem exists_golden_root_of_pm_one_mod_five (p : ℕ) (hp : p.Prime) :
    p % 5 = 1 ∨ p % 5 = 4 → ∃ t : ZMod p, t ^ 2 = t + 1 := by
  have hsq1 : IsSquare ((1 : ℕ) : ZMod 5) := by decide
  have hsq4 : IsSquare ((4 : ℕ) : ZMod 5) := by decide
  intro hmod
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have hsqp : IsSquare ((p : ℕ) : ZMod 5) := by
    rw [(ZMod.natCast_mod p 5).symm]
    rcases hmod with h | h
    · rw [h]
      exact hsq1
    · rw [h]
      exact hsq4
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hsq5 : IsSquare ((5 : ℕ) : ZMod p) :=
    (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p)
      (by norm_num) hp2).mp hsqp
  obtain ⟨s, hs⟩ := hsq5
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h0)))
  set t : ZMod p := (1 + s) / 2 with htdef
  refine ⟨t, ?_⟩
  have h2t : (2 : ZMod p) * t = 1 + s := by
    rw [htdef, mul_comm, div_mul_cancel₀ _ h2ne]
  have hmul4 : (4 : ZMod p) * (t ^ 2 - t - 1) = 0 := by
    have hs' : ((5 : ℕ) : ZMod p) = s * s := hs
    push_cast at hs'
    linear_combination (2 * t - 1 + s) * h2t - hs'
  have h4ne : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero h2ne h2ne
  have hz : t ^ 2 - t - 1 = 0 := by
    rcases mul_eq_zero.mp hmul4 with h | h
    · exact absurd h h4ne
    · exact h
  linear_combination hz

private theorem golden_root_ne_one_sub_of_prime_ne_five (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5)
    {t : ZMod p} (ht2 : t ^ 2 = t + 1) : t ≠ 1 - t := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro h0
  have h2t1 : (2 : ZMod p) * t = 1 := by linear_combination h0
  have h4t2 : (4 : ZMod p) * t ^ 2 = 1 := by
    calc (4 : ZMod p) * t ^ 2 = (2 * t) * (2 * t) := by ring
      _ = 1 := by rw [h2t1]; ring
  have h4t2' : (4 : ZMod p) * t ^ 2 = 6 := by
    rw [ht2]
    linear_combination 2 * h2t1
  have h50 : ((5 : ℕ) : ZMod p) = 0 := by
    have h61 : (6 : ZMod p) = 1 := by rw [← h4t2', h4t2]
    linear_combination h61
  exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
    ((ZMod.natCast_eq_zero_iff 5 p).mp h50))

private theorem span_prime_golden_sub_ne_of_root (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5)
    (t : ZMod p) (ht2 : t ^ 2 = t + 1) (c c' : ℤ)
    (hct : ((c : ℤ) : ZMod p) = t) (hc't : ((c' : ℤ) : ZMod p) = 1 - t)
    (hNP : Ideal.absNorm
      (Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c : 𝓞 K)}) = p) :
    Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c : 𝓞 K)} ≠
      Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c' : 𝓞 K)} := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  let P := Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c : 𝓞 K)}
  let Q := Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c' : 𝓞 K)}
  change P ≠ Q
  change Ideal.absNorm P = p at hNP
  have hp_memP : ((p : ℕ) : 𝓞 K) ∈ P := Ideal.subset_span (Set.mem_insert _ _)
  have hgc_memP : goldenIntO - (c : 𝓞 K) ∈ P :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hgc'_memQ : goldenIntO - (c' : 𝓞 K) ∈ Q :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have htne : t ≠ 1 - t := golden_root_ne_one_sub_of_prime_ne_five p hp hp5 ht2
  intro heq
  have hcc' : ((c - c' : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    rw [hct, hc't]
    intro h0
    exact htne (by linear_combination h0)
  obtain ⟨m, k₃, hk₃⟩ := exists_int_inverse_mod_prime p (c - c') hcc'
  have hk₃K : ((m : ℕ) : 𝓞 K) *
        ((c : 𝓞 K) - (c' : 𝓞 K)) - 1 =
      ((p : ℕ) : 𝓞 K) * (k₃ : 𝓞 K) := by
    have h := congrArg (fun n : ℤ => ((n : ℤ) : 𝓞 K)) hk₃
    push_cast at h
    exact h
  have h1 : (1 : 𝓞 K) ∈ P := by
    have hgc'P : goldenIntO - (c' : 𝓞 K) ∈ P := by
      rw [heq]
      exact hgc'_memQ
    have hid : (1 : 𝓞 K) = ((m : ℕ) : 𝓞 K) *
        ((goldenIntO - (c' : 𝓞 K)) - (goldenIntO - (c : 𝓞 K))) -
        (k₃ : 𝓞 K) * ((p : ℕ) : 𝓞 K) := by
      linear_combination -hk₃K
    rw [hid]
    exact Submodule.sub_mem _
      (Ideal.mul_mem_left _ _ (Submodule.sub_mem _ hgc'P hgc_memP))
      (Ideal.mul_mem_left _ _ hp_memP)
  rw [(Ideal.eq_top_iff_one P).mpr h1, Ideal.absNorm_top] at hNP
  have h2le := hp.two_le
  omega

private theorem span_natCast_eq_mul_span_golden_sub_of_mul (p : ℕ) (hp : p.Prime)
    (c c' k₁ k₂ : ℤ)
    (hprod : (goldenIntO - (c : 𝓞 K)) *
        (goldenIntO - (c' : 𝓞 K)) =
      ((p : ℕ) : 𝓞 K) *
        ((k₁ : 𝓞 K) * goldenIntO + (k₂ : 𝓞 K)))
    (hNP : Ideal.absNorm
      (Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c : 𝓞 K)}) = p)
    (hNQ : Ideal.absNorm
      (Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c' : 𝓞 K)}) = p) :
    Ideal.span {((p : ℕ) : 𝓞 K)} =
      Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c : 𝓞 K)} *
        Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c' : 𝓞 K)} := by
  let P := Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c : 𝓞 K)}
  let Q := Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c' : 𝓞 K)}
  change Ideal.span {((p : ℕ) : 𝓞 K)} = P * Q
  change Ideal.absNorm P = p at hNP
  change Ideal.absNorm Q = p at hNQ
  have hle1 : P * Q ≤ Ideal.span {((p : ℕ) : 𝓞 K)} := by
    rw [Ideal.mul_le]
    intro r1 hr1 r2 hr2
    change r1 ∈ Ideal.span {((p : ℕ) : 𝓞 K),
      goldenIntO - (c : 𝓞 K)} at hr1
    change r2 ∈ Ideal.span {((p : ℕ) : 𝓞 K),
      goldenIntO - (c' : 𝓞 K)} at hr2
    rw [Ideal.mem_span_pair] at hr1
    rw [Ideal.mem_span_pair] at hr2
    obtain ⟨x1, y1, h1⟩ := hr1
    obtain ⟨x2, y2, h2⟩ := hr2
    rw [Ideal.mem_span_singleton]
    refine ⟨x1 * x2 * ((p : ℕ) : 𝓞 K) +
      x1 * y2 * (goldenIntO - (c' : 𝓞 K)) +
      y1 * x2 * (goldenIntO - (c : 𝓞 K)) +
      y1 * y2 * ((k₁ : 𝓞 K) * goldenIntO + (k₂ : 𝓞 K)), ?_⟩
    rw [← h1, ← h2]
    linear_combination (y1 * y2) * hprod
  have hNPQ : Ideal.absNorm (P * Q) = p ^ 2 := by
    rw [_root_.map_mul, hNP, hNQ]
    ring
  exact (eq_of_le_of_absNorm_eq hle1 hNPQ (absNorm_span_natCast p)
    (pow_ne_zero 2 hp.pos.ne')).symm

private theorem exists_golden_split_data (p : ℕ) [Fact p.Prime] (t : ZMod p)
    (ht2 : t ^ 2 = t + 1) :
    ∃ c c' k₁ k₂ : ℤ,
      ((c : ℤ) : ZMod p) = t ∧ ((c' : ℤ) : ZMod p) = 1 - t ∧
        (goldenIntO - (c : 𝓞 K)) * (goldenIntO - (c' : 𝓞 K)) =
          ((p : ℕ) : 𝓞 K) *
            ((k₁ : 𝓞 K) * goldenIntO + (k₂ : 𝓞 K)) := by
  set c : ℤ := (t.val : ℤ) with hcdef
  set c' : ℤ := ((1 - t).val : ℤ) with hc'def
  have hct : ((c : ℤ) : ZMod p) = t := by
    rw [hcdef]
    exact_mod_cast ZMod.natCast_rightInverse t
  have hc't : ((c' : ℤ) : ZMod p) = 1 - t := by
    rw [hc'def]
    exact_mod_cast ZMod.natCast_rightInverse (1 - t)
  have hdvd1 : (p : ℤ) ∣ 1 - c - c' := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hct, hc't]
    ring
  have hdvd2 : (p : ℤ) ∣ 1 + c * c' := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hct, hc't]
    linear_combination -ht2
  obtain ⟨k₁, hk₁⟩ := hdvd1
  obtain ⟨k₂, hk₂⟩ := hdvd2
  have hk₁K : (1 : 𝓞 K) - (c : 𝓞 K) - (c' : 𝓞 K) =
      ((p : ℕ) : 𝓞 K) * (k₁ : 𝓞 K) := by
    have h := congrArg (fun n : ℤ => ((n : ℤ) : 𝓞 K)) hk₁
    push_cast at h
    exact h
  have hk₂K : (1 : 𝓞 K) + (c : 𝓞 K) * (c' : 𝓞 K) =
      ((p : ℕ) : 𝓞 K) * (k₂ : 𝓞 K) := by
    have h := congrArg (fun n : ℤ => ((n : ℤ) : 𝓞 K)) hk₂
    push_cast at h
    exact h
  refine ⟨c, c', k₁, k₂, hct, hc't, ?_⟩
  linear_combination goldenIntO_sq + goldenIntO * hk₁K + hk₂K

private theorem splits_of_pm_one_mod_five (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    p % 5 = 1 ∨ p % 5 = 4 →
      ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
        Ideal.span {(p : 𝓞 K)} = P * Q := by
  intro hmod
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨t, ht2⟩ := exists_golden_root_of_pm_one_mod_five p hp hmod
  obtain ⟨c, c', k₁, k₂, hct, hc't, hprod⟩ := exists_golden_split_data p t ht2
  set P := Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c : 𝓞 K)}
    with hPdef
  set Q := Ideal.span {((p : ℕ) : 𝓞 K), goldenIntO - (c' : 𝓞 K)}
    with hQdef
  have hp_memP : ((p : ℕ) : 𝓞 K) ∈ P := Ideal.subset_span (Set.mem_insert _ _)
  have hgc_memP : goldenIntO - (c : 𝓞 K) ∈ P :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hp_memQ : ((p : ℕ) : 𝓞 K) ∈ Q := Ideal.subset_span (Set.mem_insert _ _)
  have hgc'_memQ : goldenIntO - (c' : 𝓞 K) ∈ Q :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hPle : Ideal.span {((p : ℕ) : 𝓞 K)} ≤ P :=
    (Ideal.span_singleton_le_iff_mem _).mpr hp_memP
  have hQle : Ideal.span {((p : ℕ) : 𝓞 K)} ≤ Q :=
    (Ideal.span_singleton_le_iff_mem _).mpr hp_memQ
  have hNP : Ideal.absNorm P = p :=
    absNorm_span_prime_golden_sub_of_mul p hp c c' k₁ k₂ hprod
  have hNQ : Ideal.absNorm Q = p :=
    absNorm_span_prime_golden_sub_of_mul p hp c' c k₁ k₂ (by
      rw [mul_comm]
      exact hprod)
  have hPprime : P.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hNP]
    exact hp
  have hQprime : Q.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hNQ]
    exact hp
  have hPQne : P ≠ Q := by
    simpa [hPdef, hQdef] using span_prime_golden_sub_ne_of_root p hp hp5 t ht2 c c' hct
      hc't hNP
  have hPQ : Ideal.span {((p : ℕ) : 𝓞 K)} = P * Q := by
    simpa [hPdef, hQdef] using
      span_natCast_eq_mul_span_golden_sub_of_mul p hp c c' k₁ k₂ hprod hNP hNQ
  exact ⟨P, Q, hPprime, hQprime, hPQne, hPQ⟩

/-- The quadratic splitting law for `ℚ(√5)`: a rational prime `p ≠ 5` splits into two
distinct primes iff `p ≡ ±1 (mod 5)` (i.e. iff `5` is a quadratic residue mod `p`, by
quadratic reciprocity), and is inert otherwise. -/
theorem splits_iff_pm_one_mod_five (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) ↔ p % 5 = 1 ∨ p % 5 = 4 := by
  constructor
  · exact pm_one_mod_five_of_splits p hp hp5
  · exact splits_of_pm_one_mod_five p hp hp5

end NumberField.SqrtFive

/-!
## Kummer-Dedekind
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open Polynomial

namespace NumberField.SqrtFive

/-- The reduction of the integral generator polynomial `X^2 - X - 1` modulo `p`. -/
abbrev goldenPolynomialMod (p : ℕ) : (ZMod p)[X] :=
  X ^ 2 - X - C (1 : ZMod p)

private theorem goldenPolynomialMod_isRoot_iff (p : ℕ) (t : ZMod p) :
    (goldenPolynomialMod p).IsRoot t ↔ t ^ 2 = t + 1 := by
  rw [Polynomial.IsRoot.def]
  simp only [goldenPolynomialMod, eval_sub, eval_pow, eval_X, map_one, eval_one]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

private theorem goldenPolynomialMod_natDegree (p : ℕ) [Fact p.Prime] :
    (goldenPolynomialMod p).natDegree = 2 := by
  simpa [goldenPolynomialMod, mul_comm] using
    (Polynomial.natDegree_quadratic (a := (1 : ZMod p)) (b := (-1 : ZMod p))
      (c := (-1 : ZMod p)) (by norm_num : (1 : ZMod p) ≠ 0))

private theorem goldenPolynomialMod_roots_eq_zero_iff_no_root (p : ℕ) [Fact p.Prime] :
    (goldenPolynomialMod p).roots = 0 ↔ ¬ ∃ t : ZMod p, t ^ 2 = t + 1 := by
  have hdeg2 : 2 ≤ (goldenPolynomialMod p).natDegree := by
    rw [goldenPolynomialMod_natDegree]
  have hp0 : goldenPolynomialMod p ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hdeg2
    omega
  constructor
  · intro hroots
    rintro ⟨t, ht⟩
    have htroot : (goldenPolynomialMod p).IsRoot t :=
      (goldenPolynomialMod_isRoot_iff p t).mpr ht
    have htmem : t ∈ (goldenPolynomialMod p).roots := (Polynomial.mem_roots hp0).mpr htroot
    simp [hroots] at htmem
  · intro hnoroot
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro t htmem
    apply hnoroot
    refine ⟨t, ?_⟩
    exact (goldenPolynomialMod_isRoot_iff p t).mp ((Polynomial.mem_roots hp0).mp htmem)

private theorem goldenPolynomialMod_no_root_iff_two_or_three_mod_five
    (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    (¬ ∃ t : ZMod p, t ^ 2 = t + 1) ↔ p % 5 = 2 ∨ p % 5 = 3 := by
  have hnsq2 : ¬ IsSquare ((2 : ℕ) : ZMod 5) := by decide
  have hnsq3 : ¬ IsSquare ((3 : ℕ) : ZMod 5) := by decide
  constructor
  · intro hnoroot
    have hne0 : p % 5 ≠ 0 := by
      intro h0
      exact hp5 (((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm)
    have hcases : p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
      omega
    rcases hcases with h | h | h | h | h
    · exact absurd h hne0
    · exfalso
      exact hnoroot (exists_golden_root_of_pm_one_mod_five p hp (Or.inl h))
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      exact hnoroot (exists_golden_root_of_pm_one_mod_five p hp (Or.inr h))
  · intro hmod
    rintro ⟨t, ht2⟩
    by_cases hp2 : p = 2
    · subst p
      revert t
      decide
    · have hsq5 : IsSquare ((5 : ℕ) : ZMod p) := by
        refine ⟨2 * t - 1, ?_⟩
        push_cast
        linear_combination -4 * ht2
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      have hsqp : IsSquare ((p : ℕ) : ZMod 5) :=
        (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p)
          (by norm_num) hp2).mpr hsq5
      have hcast : ((p : ℕ) : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) :=
        (ZMod.natCast_mod p 5).symm
      rw [hcast] at hsqp
      rcases hmod with h | h
      · rw [h] at hsqp
        exact hnsq2 hsqp
      · rw [h] at hsqp
        exact hnsq3 hsqp

end NumberField.SqrtFive

/-!
## Different
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open IsDedekindDomain

namespace NumberField.SqrtFive

private theorem goldenIntO_adjoin_eq_top :
    Algebra.adjoin ℤ ({goldenIntO} : Set (𝓞 K)) = ⊤ := by
  apply le_antisymm le_top
  intro x _
  have hxint : (x : K) ∈ integralClosure ℤ K := x.2
  have hfield : (x : K) ∈ Algebra.adjoin ℤ ({goldenRoot} : Set K) := by
    simpa [concreteRingOfIntegers] using (by
      rw [ringOfIntegers_eq] at hxint
      exact hxint)
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hfield
  rcases hfield with ⟨P, hP⟩
  have hx_eq : x = aeval goldenIntO P := by
    apply Subtype.ext
    change (x : K) = ((aeval goldenIntO P : 𝓞 K) : K)
    rw [← hP]
    simpa [goldenIntO] using
      (Polynomial.aeval_algHom_apply (algebraMap (𝓞 K) K).toIntAlgHom goldenIntO P)
  rw [hx_eq]
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨P, rfl⟩

private theorem goldenIntO_minpoly :
    minpoly ℤ goldenIntO = X ^ 2 - X - 1 := by
  letI : IsScalarTower ℤ (𝓞 K) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hint : IsIntegral ℤ goldenIntO := Algebra.IsIntegral.isIntegral goldenIntO
  have hfrac :
      minpoly ℚ ((algebraMap (𝓞 K) K) goldenIntO) =
        map (algebraMap ℤ ℚ) (minpoly ℤ goldenIntO) :=
    @minpoly.isIntegrallyClosed_eq_field_fractions ℤ (𝓞 K)
      inferInstance inferInstance inferInstance inferInstance
      ℚ K inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance this inferInstance inferInstance
      goldenIntO hint
  apply (Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective)
  rw [← hfrac]
  change minpoly ℚ goldenRoot = map (algebraMap ℤ ℚ) (X ^ 2 - X - 1 : ℤ[X])
  have hminQ : minpoly ℚ goldenRoot = (X ^ 2 - X - 1 : ℚ[X]) := by
    exact (minpoly.eq_of_irreducible_of_monic
      (Polynomial.X_pow_sub_X_sub_one_irreducible_rat (n := 2)
        (by norm_num : (2 : ℕ) ≠ 1))
      (by
        simp
        linear_combination goldenRoot_sq) (by
        rw [show (X ^ 2 - X - 1 : ℚ[X]) = X ^ 2 - (X + 1) by ring]
        apply monic_X_pow_sub
        simpa using (show degree (X + C (1 : ℚ)) < (2 : WithBot ℕ) by
          rw [degree_X_add_C]
          norm_num))).symm
  rw [hminQ]
  simp [sub_eq_add_neg]

theorem differentIdeal_eq_span_sqrtFive :
    differentIdeal ℤ (𝓞 K) = Ideal.span {sqrtFiveIntO} := by
  have hcond : conductor ℤ goldenIntO = ⊤ :=
    conductor_eq_top_of_adjoin_eq_top goldenIntO_adjoin_eq_top
  have hadjoin : Algebra.adjoin ℚ ({algebraMap (𝓞 K) K goldenIntO} : Set K) = ⊤ := by
    simpa [goldenIntO] using adjoin_goldenRoot_eq_top
  have hdiff := conductor_mul_differentIdeal ℤ ℚ K (B := 𝓞 K) goldenIntO hadjoin
  rw [hcond, Ideal.top_mul] at hdiff
  have hae : aeval goldenIntO (derivative (minpoly ℤ goldenIntO)) = sqrtFiveIntO := by
    rw [goldenIntO_minpoly]
    rw [show derivative (X ^ 2 - X - (1 : ℤ[X])) = (2 : ℤ[X]) * X - 1 by
      simp]
    calc
      aeval goldenIntO ((2 : ℤ[X]) * X - 1) =
          aeval goldenIntO (C (2 : ℤ)) * aeval goldenIntO X - aeval goldenIntO 1 := by
        rw [show (2 : ℤ[X]) = C (2 : ℤ) by rfl, map_sub, map_mul]
      _ = sqrtFiveIntO := by
        rw [aeval_C, aeval_X, map_one]
        simp [sqrtFiveIntO]
  rw [hdiff, hae]

theorem absNorm_differentIdeal_eq_five :
    Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = 5 := by
  rw [NumberField.absNorm_differentIdeal (K := K), numberField_discr_eq]
  norm_num

theorem prime_dvd_differentIdeal_iff_eq_span_sqrtFive
    (P : Ideal (𝓞 K)) (_hP : P.IsPrime) (_hP0 : P ≠ ⊥) :
    P ∣ differentIdeal ℤ (𝓞 K) ↔ P = Ideal.span {sqrtFiveIntO} := by
  constructor
  · intro hdiv
    haveI : P.IsPrime := _hP
    have hle : Ideal.span {sqrtFiveIntO} ≤ P := by
      rw [← differentIdeal_eq_span_sqrtFive]
      exact Ideal.le_of_dvd hdiv
    have hI0 : Ideal.span ({sqrtFiveIntO} : Set (𝓞 K)) ≠ ⊥ := by
      intro hbot
      have hzero : sqrtFiveIntO = 0 := Ideal.span_singleton_eq_bot.mp hbot
      have hsqrt : sqrtFiveIntO ^ 2 = (5 : 𝓞 K) := by
        apply Subtype.ext
        change (2 * goldenRoot - 1) ^ 2 = (5 : K)
        exact sqrtFiveRoot_sq
      rw [hzero] at hsqrt
      norm_num at hsqrt
    exact ((isPrime_span_sqrtFiveIntO.isMaximal hI0).eq_of_le _hP.ne_top hle).symm
  · intro h
    rw [h, differentIdeal_eq_span_sqrtFive]

end NumberField.SqrtFive
