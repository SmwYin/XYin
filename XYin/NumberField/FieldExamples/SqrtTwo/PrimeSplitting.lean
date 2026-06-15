/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.Discriminant
import XYin.NumberField.FieldExamples.Common

/-!
# `ℚ(√2)` PrimeSplitting

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

namespace NumberField.SqrtTwo

/-- `2` is (totally) ramified: `(2) = (√2)²` as ideals of `𝓞 K`, directly from `(√2)² = 2`.
It is the unique ramified prime, matching the discriminant `8 = 2³`. -/
theorem span_two_eq : Ideal.span {(2 : 𝓞 K)} = Ideal.span {sqrtTwoInteger} ^ 2 := by
  rw [Ideal.span_singleton_pow, sqrtTwoInteger_sq]
/-- The prime `(√2)` above `2` has norm `2` (residue degree `f = 1`). -/
theorem absNorm_span_sqrtTwoInteger : Ideal.absNorm (Ideal.span {sqrtTwoInteger}) = 2 := by
  have h := intNorm_eq_normForm 0 1
  have hs : (0 : ℤ) • (1 : 𝓞 K) + (1 : ℤ) • sqrtTwoInteger = sqrtTwoInteger := by simp
  rw [hs] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  norm_num

/-- `(√2)` is a prime ideal — the unique prime of `𝓞 K` above `2`. -/
theorem isPrime_span_sqrtTwoInteger : (Ideal.span {sqrtTwoInteger}).IsPrime := by
  have h : Irreducible (Ideal.absNorm (Ideal.span {sqrtTwoInteger})) := by
    rw [absNorm_span_sqrtTwoInteger]
    exact Nat.prime_two
  exact Ideal.isPrime_of_irreducible_absNorm h

/-- The ramified prime `(√2)` lies over `(2)`. -/
theorem liesOver_span_sqrtTwoInteger :
    (Ideal.span {sqrtTwoInteger}).LiesOver (Ideal.span {(2 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_sqrtTwoInteger.ne_top
    (show Prime (2 : ℤ) by norm_num)]
  change (2 : 𝓞 K) ∈ Ideal.span {sqrtTwoInteger}
  rw [← sqrtTwoInteger_sq]
  simpa [pow_two] using
    Ideal.mul_mem_right sqrtTwoInteger (Ideal.span {sqrtTwoInteger})
      (Ideal.mem_span_singleton_self sqrtTwoInteger)

/-- The ramified prime `(√2)` has inertia degree `1` over `2`. -/
theorem inertiaDeg_span_sqrtTwoInteger :
    (Ideal.span {(2 : ℤ)}).inertiaDeg (Ideal.span {sqrtTwoInteger}) = 1 := by
  haveI : (Ideal.span {sqrtTwoInteger}).LiesOver (Ideal.span {(2 : ℤ)}) :=
    liesOver_span_sqrtTwoInteger
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {sqrtTwoInteger})
    (p := 2) Nat.prime_two
  rw [absNorm_span_sqrtTwoInteger] at h
  exact ((Nat.Prime.pow_eq_iff Nat.prime_two).mp h.symm).2

/-- The ramified prime `(√2)` has ramification index `2` over `2`. -/
theorem ramificationIdx_span_sqrtTwoInteger :
    (Ideal.span {(2 : ℤ)}).ramificationIdx (Ideal.span {sqrtTwoInteger}) = 2 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(2 : 𝓞 K)} ≤ Ideal.span {sqrtTwoInteger} ^ 2
    rw [span_two_eq]
  · intro hle3
    have hdvd : Ideal.absNorm (Ideal.span {sqrtTwoInteger} ^ 3) ∣
        Ideal.absNorm (Ideal.span {((2 : ℤ) : 𝓞 K)}) := by
      simpa [Ideal.map_span, Set.image_singleton] using Ideal.absNorm_dvd_absNorm_of_le hle3
    have hnorm2 : Ideal.absNorm (Ideal.span {((2 : ℤ) : 𝓞 K)}) = 4 := by
      change Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) = 4
      have h := intNorm_eq_normForm 2 0
      norm_num at h
      rw [Ideal.absNorm_span_singleton, h]
      rfl
    have hnorm3 : Ideal.absNorm (Ideal.span {sqrtTwoInteger} ^ 3) = 8 := by
      rw [map_pow, absNorm_span_sqrtTwoInteger]
      norm_num
    rw [hnorm3, hnorm2] at hdvd
    norm_num at hdvd

/-- `7 ≡ -1 (mod 8)` splits: `7 = (3 + √2)(3 - √2)` and `(7)` is a product of two distinct
primes of norm `7`. -/
theorem span_seven_eq :
    Ideal.span {(7 : 𝓞 K)} =
      Ideal.span {3 + sqrtTwoInteger} * Ideal.span {3 - sqrtTwoInteger} := by
  rw [Ideal.span_singleton_mul_span_singleton]
  have h : (3 + sqrtTwoInteger) * (3 - sqrtTwoInteger) = (7 : 𝓞 K) := by
    calc
      (3 + sqrtTwoInteger) * (3 - sqrtTwoInteger) = 9 - sqrtTwoInteger ^ 2 := by ring
      _ = 7 := by rw [sqrtTwoInteger_sq]; norm_num
  rw [h]

/-- The prime `(3 + √2)` above `7` has norm `7` (residue degree `f = 1`). -/
theorem absNorm_span_three_add_sqrtTwo :
    Ideal.absNorm (Ideal.span {3 + sqrtTwoInteger}) = 7 := by
  have h := intNorm_eq_normForm 3 1
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- `(3 + √2)` is a prime ideal — one of the two primes of `𝓞 K` above `7`. -/
theorem isPrime_span_three_add_sqrtTwo : (Ideal.span {3 + sqrtTwoInteger}).IsPrime := by
  have h : Irreducible (Ideal.absNorm (Ideal.span {3 + sqrtTwoInteger})) := by
    rw [absNorm_span_three_add_sqrtTwo]
    exact (Nat.irreducible_iff_nat_prime 7).mpr (by norm_num)
  exact Ideal.isPrime_of_irreducible_absNorm h

/-- The conjugate prime `(3 - √2)` above `7` has norm `7`. -/
theorem absNorm_span_three_sub_sqrtTwo :
    Ideal.absNorm (Ideal.span {3 - sqrtTwoInteger}) = 7 := by
  have h := intNorm_eq_normForm 3 (-1)
  have h3 : (3 : ℤ) • (1 : 𝓞 K) + (-1 : ℤ) • sqrtTwoInteger = 3 - sqrtTwoInteger := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [h3] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- `(3 - √2)` is the conjugate prime above `7`. -/
theorem isPrime_span_three_sub_sqrtTwo : (Ideal.span {3 - sqrtTwoInteger}).IsPrime := by
  have h : Irreducible (Ideal.absNorm (Ideal.span {3 - sqrtTwoInteger})) := by
    rw [absNorm_span_three_sub_sqrtTwo]
    exact (Nat.irreducible_iff_nat_prime 7).mpr (by norm_num)
  exact Ideal.isPrime_of_irreducible_absNorm h

/-- The prime `(3 + √2)` lies over `(7)`. -/
theorem liesOver_span_three_add_sqrtTwo :
    (Ideal.span {3 + sqrtTwoInteger}).LiesOver (Ideal.span {(7 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_three_add_sqrtTwo.ne_top
    (show Prime (7 : ℤ) by norm_num)]
  change (7 : 𝓞 K) ∈ Ideal.span {3 + sqrtTwoInteger}
  rw [show (7 : 𝓞 K) = (3 + sqrtTwoInteger) * (3 - sqrtTwoInteger) from by
    rw [show (3 + sqrtTwoInteger) * (3 - sqrtTwoInteger) = 9 - sqrtTwoInteger ^ 2 by ring]
    rw [sqrtTwoInteger_sq]
    norm_num]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self (3 + sqrtTwoInteger))

/-- The prime `(3 - √2)` lies over `(7)`. -/
theorem liesOver_span_three_sub_sqrtTwo :
    (Ideal.span {3 - sqrtTwoInteger}).LiesOver (Ideal.span {(7 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_three_sub_sqrtTwo.ne_top
    (show Prime (7 : ℤ) by norm_num)]
  change (7 : 𝓞 K) ∈ Ideal.span {3 - sqrtTwoInteger}
  rw [show (7 : 𝓞 K) = (3 - sqrtTwoInteger) * (3 + sqrtTwoInteger) from by
    rw [show (3 - sqrtTwoInteger) * (3 + sqrtTwoInteger) = 9 - sqrtTwoInteger ^ 2 by ring]
    rw [sqrtTwoInteger_sq]
    norm_num]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self (3 - sqrtTwoInteger))

/-- The split prime `(3 + √2)` has inertia degree `1` over `7`. -/
theorem inertiaDeg_span_three_add_sqrtTwo :
    (Ideal.span {(7 : ℤ)}).inertiaDeg (Ideal.span {3 + sqrtTwoInteger}) = 1 := by
  haveI : (Ideal.span {3 + sqrtTwoInteger}).LiesOver (Ideal.span {(7 : ℤ)}) :=
    liesOver_span_three_add_sqrtTwo
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {3 + sqrtTwoInteger})
    (p := 7) (by norm_num : Nat.Prime 7)
  rw [absNorm_span_three_add_sqrtTwo] at h
  exact ((Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp h.symm).2

/-- The split prime `(3 - √2)` has inertia degree `1` over `7`. -/
theorem inertiaDeg_span_three_sub_sqrtTwo :
    (Ideal.span {(7 : ℤ)}).inertiaDeg (Ideal.span {3 - sqrtTwoInteger}) = 1 := by
  haveI : (Ideal.span {3 - sqrtTwoInteger}).LiesOver (Ideal.span {(7 : ℤ)}) :=
    liesOver_span_three_sub_sqrtTwo
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {3 - sqrtTwoInteger})
    (p := 7) (by norm_num : Nat.Prime 7)
  rw [absNorm_span_three_sub_sqrtTwo] at h
  exact ((Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp h.symm).2
/-- There is no prime of `𝓞 K` with residue field `𝔽₃`: `X² - 2` has no root mod `3`. -/
private theorem absNorm_ne_three (P : Ideal (𝓞 K)) : Ideal.absNorm P ≠ 3 := by
  intro hcard
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcard
  haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card ((𝓞 K) ⧸ P) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) (by norm_num) hcard'
  obtain ⟨t, ht⟩ := e.surjective (Ideal.Quotient.mk P sqrtTwoInteger)
  have ht2 : t ^ 2 = 2 := by
    apply e.injective
    rw [map_pow, ht, ← map_pow (Ideal.Quotient.mk P), sqrtTwoInteger_sq]
    simpa using (map_ofNat e 2).symm
  clear ht
  revert t
  decide

/-- `3` is inert in `ℚ(√2)`: `2` is not a square mod `3`, so `X² - 2` is irreducible mod `3`
and `(3)` is itself prime. -/
theorem isPrime_span_three : (Ideal.span {(3 : 𝓞 K)}).IsPrime := by
  have habs9 : Ideal.absNorm (Ideal.span {(3 : 𝓞 K)}) = 9 := by
    have h := intNorm_eq_normForm 3 0
    have h3 : (3 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • sqrtTwoInteger = 3 := by
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

/-- The inert prime `(3)` has norm `9` (residue degree `f = 2`). -/
theorem absNorm_span_three : Ideal.absNorm (Ideal.span {(3 : 𝓞 K)}) = 9 := by
  have h := intNorm_eq_normForm 3 0
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- The inert prime `(3)` lies over `(3)`. -/
theorem liesOver_span_three : (Ideal.span {(3 : 𝓞 K)}).LiesOver (Ideal.span {(3 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_three.ne_top
    (show Prime (3 : ℤ) by norm_num)]
  change (3 : 𝓞 K) ∈ Ideal.span {(3 : 𝓞 K)}
  exact Ideal.mem_span_singleton_self _

/-- The inert prime `(3)` has inertia degree `2`. -/
theorem inertiaDeg_span_three :
    (Ideal.span {(3 : ℤ)}).inertiaDeg (Ideal.span {(3 : 𝓞 K)}) = 2 := by
  haveI : (Ideal.span {(3 : 𝓞 K)}).LiesOver (Ideal.span {(3 : ℤ)}) := liesOver_span_three
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {(3 : 𝓞 K)})
    (p := 3) Nat.prime_three
  rw [absNorm_span_three] at h
  change 3 ^ 2 = 3 ^ (Ideal.span {(3 : ℤ)}).inertiaDeg (Ideal.span {(3 : 𝓞 K)}) at h
  exact Nat.pow_right_injective Nat.prime_three.one_lt h.symm

/-- A rational prime generates an ideal of norm `p²` in the quadratic ring `ℤ[√2]`. -/
private theorem absNorm_span_natCast (p : ℕ) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 2 := by
  have h := intNorm_eq_normForm (p : ℤ) 0
  have hps : ((p : ℤ)) • (1 : 𝓞 K) + (0 : ℤ) • sqrtTwoInteger = ((p : ℕ) : 𝓞 K) := by
    simp
  rw [hps] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  simp [Int.natAbs_pow]

private theorem li_one_sqrtTwo : LinearIndependent ℤ ![(1 : 𝓞 K), sqrtTwoInteger] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_two] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  have hsum : ∑ i : Fin 2, g i • sqrtTwoExplicitIntegralBasis i = 0 := by
    rw [Fin.sum_univ_two, sqrtTwoExplicitIntegralBasis_zero, sqrtTwoExplicitIntegralBasis_one]
    exact hg
  exact Fintype.linearIndependent_iff.mp sqrtTwoExplicitIntegralBasis.linearIndependent g hsum

private theorem exists_o2_coords (z : 𝓞 K) :
    ∃ A B : ℤ, z = A • (1 : 𝓞 K) + B • sqrtTwoInteger := by
  let A : ℤ := sqrtTwoExplicitIntegralBasis.repr z 0
  let B : ℤ := sqrtTwoExplicitIntegralBasis.repr z 1
  refine ⟨A, B, ?_⟩
  have hsum := sqrtTwoExplicitIntegralBasis.sum_repr z
  rw [Fin.sum_univ_two, sqrtTwoExplicitIntegralBasis_zero,
    sqrtTwoExplicitIntegralBasis_one] at hsum
  simpa [A, B] using hsum.symm

/-- An element `A + B√2` with `B = ±1` is never divisible by a rational prime `p ≥ 2`. -/
private theorem unit_sqrtTwo_coeff_not_mem (p : ℕ) (hp : 2 ≤ p) (A B : ℤ)
    (hB : B = 1 ∨ B = -1) :
    ((A : ℤ) : 𝓞 K) + ((B : ℤ) : 𝓞 K) * sqrtTwoInteger ∉
      Ideal.span {((p : ℕ) : 𝓞 K)} := by
  intro hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨A', m, hzdec⟩ := exists_o2_coords z
  rw [hzdec] at hz
  have hsum : ∑ i : Fin 2,
      (![A - p * A', B - p * m] i) • (![(1 : 𝓞 K), sqrtTwoInteger] i) = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zsmul_eq_mul] at hz ⊢
    push_cast at hz ⊢
    linear_combination hz
  have hcoeff := Fintype.linearIndependent_iff.mp li_one_sqrtTwo _ hsum 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hcoeff
  rcases hB with rfl | rfl
  · have h1 : (p : ℤ) ∣ 1 := ⟨m, by linarith [hcoeff]⟩
    have := Int.le_of_dvd one_pos h1
    omega
  · have h1 : (p : ℤ) ∣ 1 := ⟨-m, by linarith [hcoeff]⟩
    have := Int.le_of_dvd one_pos h1
    omega

/-- The splitting law at ramified primes: a rational prime `p` ramifies in `ℚ(√2)` iff
`p = 2`, i.e. iff `p` divides the discriminant `8`. -/
theorem ramified_iff_eq_two (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔ p = 2 := by
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
    have hle2' : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 2 := by
      simpa [Ideal.map_span, Set.image_singleton] using hle2
    have hno3 : ¬ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 3 :=
      not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow hp habsp hkeq hk0
    have hunram : ¬ Algebra.IsUnramifiedAt ℤ P :=
      not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ hp hpmemP hPbot hle2'
        hno3
    have hPdiff : P ∣ differentIdeal ℤ (𝓞 K) := dvd_differentIdeal_iff.mpr hunram
    have habsP8 : Ideal.absNorm P ∣ 8 := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPdiff)
      rw [NumberField.absNorm_differentIdeal (K := K), sqrtTwo_numberField_discr] at h
      simpa using h
    have hpdvd : p ∣ 8 := (hkeq ▸ dvd_pow_self p hk0).trans habsP8
    have hpdiv2 : p ∣ 2 := by
      have hpow : p ∣ 2 ^ 3 := by simpa using hpdvd
      exact hp.dvd_of_dvd_pow hpow
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdiv2
  · rintro rfl
    refine ⟨Ideal.span {sqrtTwoInteger}, isPrime_span_sqrtTwoInteger, ?_⟩
    have hcast : ((2 : ℕ) : 𝓞 K) = (2 : 𝓞 K) := by norm_num
    rw [hcast, span_two_eq]

/-- Each split prime over `7` is unramified: `(3 + √2)` has ramification index `1`. -/
theorem ramificationIdx_span_three_add_sqrtTwo :
    (Ideal.span {(7 : ℤ)}).ramificationIdx (Ideal.span {3 + sqrtTwoInteger}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    change Ideal.span {(7 : 𝓞 K)} ≤ Ideal.span {3 + sqrtTwoInteger}
    rw [span_seven_eq]
    exact Ideal.mul_le_right
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(7 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {3 + sqrtTwoInteger}, isPrime_span_three_add_sqrtTwo, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h72 := (ramified_iff_eq_two 7 (by norm_num)).mp hram
    norm_num at h72

/-- Each split prime over `7` is unramified: `(3 - √2)` has ramification index `1`. -/
theorem ramificationIdx_span_three_sub_sqrtTwo :
    (Ideal.span {(7 : ℤ)}).ramificationIdx (Ideal.span {3 - sqrtTwoInteger}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    change Ideal.span {(7 : 𝓞 K)} ≤ Ideal.span {3 - sqrtTwoInteger}
    rw [span_seven_eq]
    exact Ideal.mul_le_left
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(7 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {3 - sqrtTwoInteger}, isPrime_span_three_sub_sqrtTwo, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h72 := (ramified_iff_eq_two 7 (by norm_num)).mp hram
    norm_num at h72

/-- The inert prime `(3)` is unramified: it has ramification index `1`. -/
theorem ramificationIdx_span_three :
    (Ideal.span {(3 : ℤ)}).ramificationIdx (Ideal.span {(3 : 𝓞 K)}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    simp
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(3 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {(3 : 𝓞 K)}, isPrime_span_three, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h32 := (ramified_iff_eq_two 3 Nat.prime_three).mp hram
    norm_num at h32

private theorem absNorm_span_prime_sqrtTwo_sub_of_mul (p : ℕ) (hp : p.Prime) (c k : ℤ)
    (hprod : (sqrtTwoInteger - (c : 𝓞 K)) * (sqrtTwoInteger + (c : 𝓞 K)) =
      ((p : ℕ) : 𝓞 K) * (k : 𝓞 K)) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K), sqrtTwoInteger - (c : 𝓞 K)}) = p := by
  let P : Ideal (𝓞 K) := Ideal.span {((p : ℕ) : 𝓞 K), sqrtTwoInteger - (c : 𝓞 K)}
  change Ideal.absNorm P = p
  have hp_memP : ((p : ℕ) : 𝓞 K) ∈ P := Ideal.subset_span (Set.mem_insert _ _)
  have hsc_memP : sqrtTwoInteger - (c : 𝓞 K) ∈ P :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hPle : Ideal.span {((p : ℕ) : 𝓞 K)} ≤ P :=
    (Ideal.span_singleton_le_iff_mem _).mpr hp_memP
  have hPnot1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    intro htop
    have h1 : (1 : 𝓞 K) ∈ P := htop ▸ Submodule.mem_top
    change (1 : 𝓞 K) ∈ Ideal.span {((p : ℕ) : 𝓞 K), sqrtTwoInteger - (c : 𝓞 K)} at h1
    rw [Ideal.mem_span_pair] at h1
    obtain ⟨α, β, hαβ⟩ := h1
    have hsc' : sqrtTwoInteger + (c : 𝓞 K) ∈ Ideal.span {((p : ℕ) : 𝓞 K)} := by
      rw [Ideal.mem_span_singleton]
      refine ⟨α * (sqrtTwoInteger + (c : 𝓞 K)) + β * (k : 𝓞 K), ?_⟩
      calc sqrtTwoInteger + (c : 𝓞 K)
          = (α * ((p : ℕ) : 𝓞 K) + β * (sqrtTwoInteger - (c : 𝓞 K))) *
              (sqrtTwoInteger + (c : 𝓞 K)) := by
            rw [hαβ, one_mul]
        _ = ((p : ℕ) : 𝓞 K) * (α * (sqrtTwoInteger + (c : 𝓞 K)) + β * (k : 𝓞 K)) := by
            linear_combination β * hprod
    refine unit_sqrtTwo_coeff_not_mem p hp.two_le c 1 (Or.inl rfl) ?_
    rw [show ((c : ℤ) : 𝓞 K) + ((1 : ℤ) : 𝓞 K) * sqrtTwoInteger =
      sqrtTwoInteger + (c : 𝓞 K) by
        push_cast
        ring]
    exact hsc'
  have hPnotsq : Ideal.absNorm P ≠ p ^ 2 := by
    intro hNP
    have heq := eq_of_le_of_absNorm_eq hPle (absNorm_span_natCast p) hNP
      (pow_ne_zero 2 hp.pos.ne')
    refine unit_sqrtTwo_coeff_not_mem p hp.two_le (-c) 1 (Or.inl rfl) ?_
    rw [show (((-c : ℤ) : 𝓞 K) + ((1 : ℤ) : 𝓞 K) * sqrtTwoInteger) =
      sqrtTwoInteger - (c : 𝓞 K) by
        push_cast
        ring]
    rw [heq]
    exact hsc_memP
  exact eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq hp
    ((absNorm_span_natCast p) ▸ Ideal.absNorm_dvd_absNorm_of_le hPle) hPnot1 hPnotsq

private theorem pm_one_mod_eight_of_prime_norm (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧ Ideal.absNorm P = p) →
      p % 8 = 1 ∨ p % 8 = 7 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rintro ⟨P, hPprime, hPle, hNP⟩
  have hcard : Nat.card ((𝓞 K) ⧸ P) = p := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hNP
    exact hNP
  haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.pos.ne')
  haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card ((𝓞 K) ⧸ P) = p := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) hp hcard'
  obtain ⟨t, ht⟩ := e.surjective (Ideal.Quotient.mk P sqrtTwoInteger)
  have ht2 : t ^ 2 = 2 := by
    apply e.injective
    rw [map_pow, ht, ← map_pow (Ideal.Quotient.mk P), sqrtTwoInteger_sq]
    simpa using (map_ofNat e 2).symm
  have hsq2 : IsSquare ((2 : ℕ) : ZMod p) := by
    rw [isSquare_iff_exists_sq]
    exact ⟨t, by simpa using ht2.symm⟩
  exact (ZMod.exists_sq_eq_two_iff (p := p) hp2).mp hsq2

private theorem exists_prime_norm_of_pm_one_mod_eight (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    p % 8 = 1 ∨ p % 8 = 7 →
      ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧ Ideal.absNorm P = p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro hmod
  have hsq2 : IsSquare ((2 : ℕ) : ZMod p) :=
    (ZMod.exists_sq_eq_two_iff (p := p) hp2).mpr hmod
  rw [isSquare_iff_exists_sq] at hsq2
  obtain ⟨s, hs⟩ := hsq2
  set c : ℤ := (s.val : ℤ) with hcdef
  have hct : ((c : ℤ) : ZMod p) = s := by
    rw [hcdef]
    exact_mod_cast ZMod.natCast_rightInverse s
  have hdvd : (p : ℤ) ∣ 2 - c * c := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hct]
    have hs' : s * s = 2 := by simpa [pow_two] using hs.symm
    linear_combination -hs'
  obtain ⟨k, hk⟩ := hdvd
  have hkRing : (2 : 𝓞 K) - (c : 𝓞 K) * (c : 𝓞 K) = ((p : ℕ) : 𝓞 K) * (k : 𝓞 K) := by
    have h := congrArg (fun n : ℤ => ((n : ℤ) : 𝓞 K)) hk
    push_cast at h
    exact h
  have hprod : (sqrtTwoInteger - (c : 𝓞 K)) * (sqrtTwoInteger + (c : 𝓞 K)) =
      ((p : ℕ) : 𝓞 K) * (k : 𝓞 K) := by
    calc (sqrtTwoInteger - (c : 𝓞 K)) * (sqrtTwoInteger + (c : 𝓞 K)) =
          sqrtTwoInteger ^ 2 - (c : 𝓞 K) * (c : 𝓞 K) := by ring
      _ = (2 : 𝓞 K) - (c : 𝓞 K) * (c : 𝓞 K) := by rw [sqrtTwoInteger_sq]
      _ = ((p : ℕ) : 𝓞 K) * (k : 𝓞 K) := hkRing
  let P : Ideal (𝓞 K) := Ideal.span {((p : ℕ) : 𝓞 K), sqrtTwoInteger - (c : 𝓞 K)}
  have hPle : Ideal.span {((p : ℕ) : 𝓞 K)} ≤ P :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span (Set.mem_insert _ _))
  have hNP : Ideal.absNorm P = p := absNorm_span_prime_sqrtTwo_sub_of_mul p hp c k hprod
  have hPprime : P.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hNP]
    exact (Nat.irreducible_iff_nat_prime p).mpr hp
  exact ⟨P, hPprime, hPle, hNP⟩

theorem exists_prime_norm_iff_pm_one_mod_eight (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧ Ideal.absNorm P = p) ↔
      p % 8 = 1 ∨ p % 8 = 7 := by
  constructor
  · exact pm_one_mod_eight_of_prime_norm p hp hp2
  · exact exists_prime_norm_of_pm_one_mod_eight p hp hp2

private theorem pm_one_mod_eight_of_splits (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) → p % 8 = 1 ∨ p % 8 = 7 := by
  rintro ⟨P, Q, hPprime, hQprime, hPQne, hspan⟩
  have hPle : Ideal.span {(p : 𝓞 K)} ≤ P := by
    rw [hspan]
    exact Ideal.mul_le_right
  have hPnorm_dvd : Ideal.absNorm P ∣ p ^ 2 :=
    absNorm_span_natCast p ▸ Ideal.absNorm_dvd_absNorm_of_le hPle
  obtain ⟨k, hk2, hPnorm⟩ := (Nat.dvd_prime_pow hp).mp hPnorm_dvd
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hPnorm
    exact hPprime.ne_top (Ideal.absNorm_eq_one_iff.mp hPnorm)
  have hmul := _root_.map_mul Ideal.absNorm P Q
  have hspan' : Ideal.span {((p : ℕ) : 𝓞 K)} = P * Q := by
    simpa using hspan
  rw [← hspan', absNorm_span_natCast] at hmul
  have hQnorm_ne_one : Ideal.absNorm Q ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hQprime.ne_top
  have hPnorm_eq : Ideal.absNorm P = p := by
    interval_cases k
    · exact (hk0 rfl).elim
    · simpa using hPnorm
    · exfalso
      rw [hPnorm] at hmul
      have hQone : Ideal.absNorm Q = 1 :=
        (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2)
          (by rw [mul_one]; exact hmul)).symm
      exact hQnorm_ne_one hQone
  exact (exists_prime_norm_iff_pm_one_mod_eight p hp hp2).mp
    ⟨P, hPprime, hPle, hPnorm_eq⟩

private theorem splits_of_pm_one_mod_eight (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    p % 8 = 1 ∨ p % 8 = 7 →
      ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
        Ideal.span {(p : 𝓞 K)} = P * Q := by
  intro hmod
  obtain ⟨P, hPprime, hPle, hPnorm⟩ :=
    (exists_prime_norm_iff_pm_one_mod_eight p hp hp2).mpr hmod
  obtain ⟨Q, hspan⟩ := Ideal.dvd_iff_le.mpr hPle
  have hQnorm : Ideal.absNorm Q = p := by
    have hmul := _root_.map_mul Ideal.absNorm P Q
    have hspan' : Ideal.span {((p : ℕ) : 𝓞 K)} = P * Q := by
      simpa using hspan
    rw [← hspan', absNorm_span_natCast, hPnorm] at hmul
    rw [pow_two] at hmul
    exact Nat.eq_of_mul_eq_mul_left hp.pos hmul.symm
  have hQprime : Q.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hQnorm]
    exact (Nat.irreducible_iff_nat_prime p).mpr hp
  have hPQ : P ≠ Q := by
    intro h
    have hram : ∃ R : Ideal (𝓞 K), R.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ R ^ 2 := by
      refine ⟨P, hPprime, ?_⟩
      rw [hspan, h, sq]
    exact hp2 ((ramified_iff_eq_two p hp).mp hram)
  exact ⟨P, Q, hPprime, hQprime, hPQ, by simpa using hspan⟩

/-- The quadratic splitting law for `ℚ(√2)`: an odd rational prime `p` splits into two
distinct primes iff `p ≡ ±1 (mod 8)` (i.e. iff `2` is a quadratic residue mod `p`, by the
second supplement to quadratic reciprocity), and is inert otherwise. -/
theorem splits_iff_pm_one_mod_eight (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) ↔ p % 8 = 1 ∨ p % 8 = 7 := by
  constructor
  · exact pm_one_mod_eight_of_splits p hp hp2
  · exact splits_of_pm_one_mod_eight p hp hp2


end NumberField.SqrtTwo


/-!
## Kummer-Dedekind
-/

noncomputable section


open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open Polynomial

namespace NumberField.SqrtTwo

/-- The reduction of the minimal polynomial `X^2 - 2` modulo `p`. -/
abbrev sqrtTwoPolynomialMod (p : ℕ) : (ZMod p)[X] :=
  X ^ 2 - C (2 : ZMod p)

/-- The generator `√2` generates the full ring of integers, so Kummer-Dedekind has no
exceptional conductor primes for this integral primitive element. -/
theorem sqrtTwoInteger_exponent_eq_one :
    RingOfIntegers.exponent sqrtTwoInteger = 1 := by
  rw [RingOfIntegers.exponent_eq_one_iff]
  exact sqrtTwoInteger_adjoin_eq_top

/-- Every rational prime is coprime to the Kummer-Dedekind exponent of `√2`. -/
theorem sqrtTwoInteger_exponent_not_dvd (p : ℕ) [Fact p.Prime] :
    ¬ p ∣ RingOfIntegers.exponent sqrtTwoInteger := by
  rw [sqrtTwoInteger_exponent_eq_one]
  exact (Fact.out : p.Prime).not_dvd_one

/-- Kummer-Dedekind computes the residual degree from the degree of a mod-`p` factor. -/
theorem sqrtTwo_kummerDedekind_inertiaDeg
    {p : ℕ} [Fact p.Prime] {Q : (ZMod p)[X]}
    (hQ : Q ∈ RingOfIntegers.monicFactorsMod sqrtTwoInteger p) :
    Ideal.inertiaDeg (Ideal.span {(p : ℤ)})
        ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
          (θ := sqrtTwoInteger) (sqrtTwoInteger_exponent_not_dvd p)).symm ⟨Q, hQ⟩ :
          Ideal (𝓞 K)) = Q.natDegree := by
  exact NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (θ := sqrtTwoInteger) (sqrtTwoInteger_exponent_not_dvd p) hQ

/-- Kummer-Dedekind computes the ramification index from the multiplicity of a mod-`p` factor. -/
theorem sqrtTwo_kummerDedekind_ramificationIdx
    {p : ℕ} [Fact p.Prime] {Q : (ZMod p)[X]}
    (hQ : Q ∈ RingOfIntegers.monicFactorsMod sqrtTwoInteger p) :
    Ideal.ramificationIdx (Ideal.span {(p : ℤ)})
        ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
          (θ := sqrtTwoInteger) (sqrtTwoInteger_exponent_not_dvd p)).symm ⟨Q, hQ⟩ :
          Ideal (𝓞 K)) = multiplicity Q (sqrtTwoPolynomialMod p) := by
  rw [NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (θ := sqrtTwoInteger) (sqrtTwoInteger_exponent_not_dvd p) hQ]
  congr 1
  rw [sqrtTwoInteger_minpoly, sqrtTwoIntegerPolynomial, sqrtTwoPolynomialMod]
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  congr 2
  norm_num

/-- Modulo `2`, Kummer-Dedekind sees the double root responsible for ramification. -/
theorem sqrtTwoPolynomialMod_two :
    sqrtTwoPolynomialMod 2 = X ^ 2 := by
  rw [sqrtTwoPolynomialMod]
  have h : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  rw [h]
  simp

/-- Modulo `7`, Kummer-Dedekind sees the two roots `±3`. -/
theorem sqrtTwoPolynomialMod_seven_factor :
    sqrtTwoPolynomialMod 7 =
      (X - C (3 : ZMod 7)) * (X + C (3 : ZMod 7)) := by
  rw [sqrtTwoPolynomialMod]
  ring_nf
  have hC : (C (2 : ZMod 7) : (ZMod 7)[X]) = C (3 : ZMod 7) ^ 2 := by
    rw [← map_pow]
    congr
  rw [hC]

/-- Modulo `3`, the polynomial is irreducible, matching the inert prime `(3)`. -/
theorem sqrtTwoPolynomialMod_three_irreducible :
    Irreducible (sqrtTwoPolynomialMod 3) := by
  rw [sqrtTwoPolynomialMod]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, natDegree_X_pow_sub_C]
    norm_num
  · intro x hx
    fin_cases x
    · change Polynomial.eval (0 : ZMod 3) (X ^ 2 - C 2) = 0 at hx
      norm_num at hx
      exact (by decide : (2 : ZMod 3) ≠ 0) hx
    · change Polynomial.eval (1 : ZMod 3) (X ^ 2 - C 2) = 0 at hx
      norm_num at hx
    · change Polynomial.eval (2 : ZMod 3) (X ^ 2 - C 2) = 0 at hx
      norm_num at hx
      exact (by decide : (2 : ZMod 3) ≠ 0) hx

/-- The Kummer-Dedekind root condition is the same as the existing norm-`p` prime condition. -/
theorem exists_root_mod_iff_exists_prime_norm
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ c : ZMod p, c ^ 2 = (2 : ZMod p)) ↔
      ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧
        Ideal.absNorm P = p := by
  calc
    (∃ c : ZMod p, c ^ 2 = (2 : ZMod p)) ↔ p % 8 = 1 ∨ p % 8 = 7 := by
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      simpa [isSquare_iff_exists_sq, eq_comm] using (ZMod.exists_sq_eq_two_iff (p := p) hp2)
    _ ↔ (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧
        Ideal.absNorm P = p) :=
      (exists_prime_norm_iff_pm_one_mod_eight p hp hp2).symm

/-- Kummer-Dedekind's splitting condition agrees with the existing `±1 mod 8` law. -/
theorem kummerDedekind_splits_iff_pm_one_mod_eight
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ c : ZMod p, c ^ 2 = (2 : ZMod p)) ↔ p % 8 = 1 ∨ p % 8 = 7 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  simpa [isSquare_iff_exists_sq, eq_comm] using (ZMod.exists_sq_eq_two_iff (p := p) hp2)

/-- The inert cases are the complementary odd residue classes modulo `8`. -/
theorem kummerDedekind_inert_iff_three_or_five_mod_eight
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Irreducible (sqrtTwoPolynomialMod p) ↔ p % 8 = 3 ∨ p % 8 = 5 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hdeg : (sqrtTwoPolynomialMod p).natDegree = 2 := by
    rw [sqrtTwoPolynomialMod, natDegree_X_pow_sub_C]
  have hroot_iff (c : ZMod p) :
      (sqrtTwoPolynomialMod p).IsRoot c ↔ c ^ 2 = (2 : ZMod p) := by
    simpa [sqrtTwoPolynomialMod, pow_two] using
      (sub_eq_zero : c * c - (2 : ZMod p) = 0 ↔ c * c = (2 : ZMod p))
  have hirr_iff_not_sq : Irreducible (sqrtTwoPolynomialMod p) ↔
      ¬ ∃ c : ZMod p, c ^ 2 = (2 : ZMod p) := by
    constructor
    · intro hirr hs
      obtain ⟨c, hc⟩ := hs
      exact hirr.not_isRoot_of_natDegree_ne_one (by rw [hdeg]; norm_num)
        ((hroot_iff c).2 hc)
    · intro hnot
      apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      · rw [Finset.mem_Icc, hdeg]
        norm_num
      · intro c hc
        exact hnot ⟨c, (hroot_iff c).1 hc⟩
  have hsq_iff : (∃ c : ZMod p, c ^ 2 = (2 : ZMod p)) ↔
      p % 8 = 1 ∨ p % 8 = 7 := by
    simpa [isSquare_iff_exists_sq, eq_comm] using
      (ZMod.exists_sq_eq_two_iff (p := p) hp2)
  have hodd : p % 2 = 1 := by
    simpa [Nat.odd_iff] using hp.odd_of_ne_two hp2
  have hmod2 : p % 8 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 8), hodd]
  have hnot_pm_one_iff :
      ¬ (p % 8 = 1 ∨ p % 8 = 7) ↔ p % 8 = 3 ∨ p % 8 = 5 := by
    constructor
    · intro h
      have hlt : p % 8 < 8 := Nat.mod_lt p (by norm_num)
      interval_cases hcase : p % 8 <;> omega
    · intro h hpm
      omega
  calc
    Irreducible (sqrtTwoPolynomialMod p) ↔
        ¬ ∃ c : ZMod p, c ^ 2 = (2 : ZMod p) := hirr_iff_not_sq
    _ ↔ ¬ (p % 8 = 1 ∨ p % 8 = 7) := not_congr hsq_iff
    _ ↔ p % 8 = 3 ∨ p % 8 = 5 := hnot_pm_one_iff

/-- Complete Kummer-Dedekind splitting type for unramified rational primes in `ℚ(√2)`. -/
theorem kummerDedekind_splittingType_mod_eight
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ((∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
        Ideal.span {(p : 𝓞 K)} = P * Q) ↔ p % 8 = 1 ∨ p % 8 = 7) ∧
      (Irreducible (sqrtTwoPolynomialMod p) ↔ p % 8 = 3 ∨ p % 8 = 5) := by
  exact ⟨splits_iff_pm_one_mod_eight p hp hp2,
    kummerDedekind_inert_iff_three_or_five_mod_eight p hp hp2⟩

/-- The Kummer-Dedekind prediction at `2` matches the concrete factorization `(2)=(√2)^2`. -/
theorem kummerDedekind_two_matches_concrete_ramification :
    sqrtTwoPolynomialMod 2 = X ^ 2 ∧
      Ideal.span {(2 : 𝓞 K)} = Ideal.span {sqrtTwoInteger} ^ 2 := by
  exact ⟨sqrtTwoPolynomialMod_two, span_two_eq⟩

/-- The Kummer-Dedekind prediction at `7` matches the concrete split ideal factorization. -/
theorem kummerDedekind_seven_matches_concrete_factorization :
    sqrtTwoPolynomialMod 7 =
        (X - C (3 : ZMod 7)) * (X + C (3 : ZMod 7)) ∧
      Ideal.span {(7 : 𝓞 K)} =
        Ideal.span {3 + sqrtTwoInteger} * Ideal.span {3 - sqrtTwoInteger} := by
  exact ⟨sqrtTwoPolynomialMod_seven_factor, span_seven_eq⟩

end NumberField.SqrtTwo


/-!
## Different
-/

noncomputable section


open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtTwo

/-- For `ℚ(√2)`, the different is generated by `2√2`. -/
theorem differentIdeal_eq_span_two_mul_sqrtTwo :
    differentIdeal ℤ (𝓞 K) = Ideal.span {(2 : 𝓞 K) * sqrtTwoInteger} := by
  have hcond : conductor ℤ sqrtTwoInteger = ⊤ :=
    conductor_eq_top_of_adjoin_eq_top sqrtTwoInteger_adjoin_eq_top
  have hadjoin : Algebra.adjoin ℚ ({algebraMap (𝓞 K) K sqrtTwoInteger} : Set K) = ⊤ := by
    simpa [sqrtTwoInteger] using adjoin_sqrtTwoRoot_eq_top
  have hdiff := conductor_mul_differentIdeal ℤ ℚ K (B := 𝓞 K) sqrtTwoInteger hadjoin
  rw [hcond, Ideal.top_mul] at hdiff
  have hae : aeval sqrtTwoInteger (derivative (minpoly ℤ sqrtTwoInteger)) =
      (2 : 𝓞 K) * sqrtTwoInteger := by
    rw [sqrtTwoInteger_minpoly]
    rw [show derivative sqrtTwoIntegerPolynomial = (2 : ℤ[X]) * X by
      simp [sqrtTwoIntegerPolynomial]]
    calc
      aeval sqrtTwoInteger ((2 : ℤ[X]) * X) =
          aeval sqrtTwoInteger (C (2 : ℤ)) * aeval sqrtTwoInteger X := by
        rw [show (2 : ℤ[X]) = C (2 : ℤ) by rfl, map_mul]
      _ = (2 : 𝓞 K) * sqrtTwoInteger := by
        rw [aeval_C, aeval_X]
        norm_num
  rw [hdiff, hae]

/-- Equivalently, the different is the cube of the unique ramified prime above `2`. -/
theorem differentIdeal_eq_span_sqrtTwoInteger_pow_three :
    differentIdeal ℤ (𝓞 K) = Ideal.span {sqrtTwoInteger} ^ 3 := by
  rw [differentIdeal_eq_span_two_mul_sqrtTwo, Ideal.span_singleton_pow]
  have hpow : sqrtTwoInteger ^ 3 = (2 : 𝓞 K) * sqrtTwoInteger := by
    calc
      sqrtTwoInteger ^ 3 = sqrtTwoInteger ^ 2 * sqrtTwoInteger := by ring
      _ = (2 : 𝓞 K) * sqrtTwoInteger := by rw [sqrtTwoInteger_sq]
  rw [hpow]

/-- The absolute norm of the different is the absolute discriminant `8`. -/
theorem absNorm_differentIdeal_eq_eight :
    Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = 8 := by
  rw [differentIdeal_eq_span_sqrtTwoInteger_pow_three, map_pow, absNorm_span_sqrtTwoInteger]
  norm_num

/-- The concrete ramified prime `(√2)` is exactly the support of the different. -/
theorem prime_dvd_differentIdeal_iff_eq_span_sqrtTwo
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) (_hP0 : P ≠ ⊥) :
    P ∣ differentIdeal ℤ (𝓞 K) ↔ P = Ideal.span {sqrtTwoInteger} := by
  constructor
  · intro hdiv
    haveI : P.IsPrime := hP
    have hlePow : Ideal.span {sqrtTwoInteger} ^ 3 ≤ P := by
      rw [← differentIdeal_eq_span_sqrtTwoInteger_pow_three]
      exact Ideal.le_of_dvd hdiv
    have hleI : Ideal.span {sqrtTwoInteger} ≤ P :=
      Ideal.IsPrime.le_of_pow_le (P := P) hlePow
    have hI0 : Ideal.span ({sqrtTwoInteger} : Set (𝓞 K)) ≠ ⊥ := by
      intro hbot
      have hzero : sqrtTwoInteger = 0 := Ideal.span_singleton_eq_bot.mp hbot
      have hK : sqrtTwoRoot = 0 := by
        change (algebraMap (𝓞 K) K) sqrtTwoInteger = 0
        rw [hzero, map_zero]
      have h2 : (2 : K) = 0 := by
        rw [← sqrtTwoRoot_sq, hK]
        norm_num
      norm_num at h2
    exact ((isPrime_span_sqrtTwoInteger.isMaximal hI0).eq_of_le hP.ne_top hleI).symm
  · intro h
    rw [h, differentIdeal_eq_span_sqrtTwoInteger_pow_three]
    exact dvd_pow_self (Ideal.span {sqrtTwoInteger}) (by norm_num : 3 ≠ 0)

end NumberField.SqrtTwo
