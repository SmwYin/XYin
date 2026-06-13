/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.NormForm
import XYin.NumberField.FieldExamples.Common

/-!
# `ℚ(√2)` Prime splitting

This file develops the prime splitting part of the `ℚ(√2)` number field example.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open NumberField.FieldExamples

namespace NumberField.SqrtTwo

/-- `2` is (totally) ramified: `(2) = (√2)²` as ideals of `𝓞 K`, directly from `(√2)² = 2`.
It is the unique ramified prime, matching the discriminant `8 = 2³`. -/
theorem span_two_eq : Ideal.span {(2 : O2)} = Ideal.span {sqrtTwoInteger} ^ 2 := by
  rw [Ideal.span_singleton_pow, sqrtTwoInteger_sq]
/-- The prime `(√2)` above `2` has norm `2` (residue degree `f = 1`). -/
theorem absNorm_span_sqrtTwoInteger : Ideal.absNorm (Ideal.span {sqrtTwoInteger}) = 2 := by
  have h := intNorm_eq_normForm 0 1
  have hs : (0 : ℤ) • (1 : O2) + (1 : ℤ) • sqrtTwoInteger = sqrtTwoInteger := by simp
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
  change (2 : O2) ∈ Ideal.span {sqrtTwoInteger}
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
    change Ideal.span {(2 : O2)} ≤ Ideal.span {sqrtTwoInteger} ^ 2
    rw [span_two_eq]
  · intro hle3
    have hdvd : Ideal.absNorm (Ideal.span {sqrtTwoInteger} ^ 3) ∣
        Ideal.absNorm (Ideal.span {((2 : ℤ) : O2)}) := by
      simpa [Ideal.map_span, Set.image_singleton] using Ideal.absNorm_dvd_absNorm_of_le hle3
    have hnorm2 : Ideal.absNorm (Ideal.span {((2 : ℤ) : O2)}) = 4 := by
      change Ideal.absNorm (Ideal.span {(2 : O2)}) = 4
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
    Ideal.span {(7 : O2)} =
      Ideal.span {3 + sqrtTwoInteger} * Ideal.span {3 - sqrtTwoInteger} := by
  rw [Ideal.span_singleton_mul_span_singleton]
  have h : (3 + sqrtTwoInteger) * (3 - sqrtTwoInteger) = (7 : O2) := by
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
  have h3 : (3 : ℤ) • (1 : O2) + (-1 : ℤ) • sqrtTwoInteger = 3 - sqrtTwoInteger := by
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
  change (7 : O2) ∈ Ideal.span {3 + sqrtTwoInteger}
  rw [show (7 : O2) = (3 + sqrtTwoInteger) * (3 - sqrtTwoInteger) from by
    rw [show (3 + sqrtTwoInteger) * (3 - sqrtTwoInteger) = 9 - sqrtTwoInteger ^ 2 by ring]
    rw [sqrtTwoInteger_sq]
    norm_num]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self (3 + sqrtTwoInteger))

/-- The prime `(3 - √2)` lies over `(7)`. -/
theorem liesOver_span_three_sub_sqrtTwo :
    (Ideal.span {3 - sqrtTwoInteger}).LiesOver (Ideal.span {(7 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_three_sub_sqrtTwo.ne_top
    (show Prime (7 : ℤ) by norm_num)]
  change (7 : O2) ∈ Ideal.span {3 - sqrtTwoInteger}
  rw [show (7 : O2) = (3 - sqrtTwoInteger) * (3 + sqrtTwoInteger) from by
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
private theorem absNorm_ne_three (P : Ideal O2) : Ideal.absNorm P ≠ 3 := by
  intro hcard
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcard
  haveI : Finite (O2 ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype (O2 ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card (O2 ⧸ P) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let e := ZMod.ringEquivOfPrime (O2 ⧸ P) (by norm_num) hcard'
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
theorem isPrime_span_three : (Ideal.span {(3 : O2)}).IsPrime := by
  have habs9 : Ideal.absNorm (Ideal.span {(3 : O2)}) = 9 := by
    have h := intNorm_eq_normForm 3 0
    have h3 : (3 : ℤ) • (1 : O2) + (0 : ℤ) • sqrtTwoInteger = 3 := by
      simp
    rw [h3] at h
    norm_num at h
    rw [Ideal.absNorm_span_singleton, h]
    rfl
  have htop : Ideal.span {(3 : O2)} ≠ ⊤ := by
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
theorem absNorm_span_three : Ideal.absNorm (Ideal.span {(3 : O2)}) = 9 := by
  have h := intNorm_eq_normForm 3 0
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- The inert prime `(3)` lies over `(3)`. -/
theorem liesOver_span_three : (Ideal.span {(3 : O2)}).LiesOver (Ideal.span {(3 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_three.ne_top
    (show Prime (3 : ℤ) by norm_num)]
  change (3 : O2) ∈ Ideal.span {(3 : O2)}
  exact Ideal.mem_span_singleton_self _

/-- The inert prime `(3)` has inertia degree `2`. -/
theorem inertiaDeg_span_three :
    (Ideal.span {(3 : ℤ)}).inertiaDeg (Ideal.span {(3 : O2)}) = 2 := by
  haveI : (Ideal.span {(3 : O2)}).LiesOver (Ideal.span {(3 : ℤ)}) := liesOver_span_three
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {(3 : O2)})
    (p := 3) Nat.prime_three
  rw [absNorm_span_three] at h
  change 3 ^ 2 = 3 ^ (Ideal.span {(3 : ℤ)}).inertiaDeg (Ideal.span {(3 : O2)}) at h
  exact Nat.pow_right_injective Nat.prime_three.one_lt h.symm

/-- A rational prime generates an ideal of norm `p²` in the quadratic ring `ℤ[√2]`. -/
private theorem absNorm_span_natCast (p : ℕ) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : O2)}) = p ^ 2 := by
  have h := intNorm_eq_normForm (p : ℤ) 0
  have hps : ((p : ℤ)) • (1 : O2) + (0 : ℤ) • sqrtTwoInteger = ((p : ℕ) : O2) := by
    simp
  rw [hps] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  simp [Int.natAbs_pow]

private theorem li_one_sqrtTwo : LinearIndependent ℤ ![(1 : O2), sqrtTwoInteger] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_two] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  have hsum : ∑ i : Fin 2, g i • sqrtTwoExplicitIntegralBasis i = 0 := by
    rw [Fin.sum_univ_two, sqrtTwoExplicitIntegralBasis_zero, sqrtTwoExplicitIntegralBasis_one]
    exact hg
  exact Fintype.linearIndependent_iff.mp sqrtTwoExplicitIntegralBasis.linearIndependent g hsum

private theorem exists_o2_coords (z : O2) :
    ∃ A B : ℤ, z = A • (1 : O2) + B • sqrtTwoInteger := by
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
    ((A : ℤ) : O2) + ((B : ℤ) : O2) * sqrtTwoInteger ∉
      Ideal.span {((p : ℕ) : O2)} := by
  intro hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨A', m, hzdec⟩ := exists_o2_coords z
  rw [hzdec] at hz
  have hsum : ∑ i : Fin 2,
      (![A - p * A', B - p * m] i) • (![(1 : O2), sqrtTwoInteger] i) = 0 := by
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
    (∃ P : Ideal O2, P.IsPrime ∧ Ideal.span {(p : O2)} ≤ P ^ 2) ↔ p = 2 := by
  constructor
  · rintro ⟨P, hP, hle2⟩
    haveI : P.IsPrime := hP
    have hple : Ideal.span {((p : ℕ) : O2)} ≤ P :=
      hle2.trans (Ideal.pow_le_self (by norm_num))
    have hpmemP : ((p : ℕ) : O2) ∈ P := hple (Ideal.mem_span_singleton_self _)
    have hpne : ((p : ℕ) : O2) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hPbot : P ≠ ⊥ := by
      intro h
      rw [h] at hpmemP
      exact hpne (Ideal.mem_bot.mp hpmemP)
    have habsp : Ideal.absNorm (Ideal.span {((p : ℕ) : O2)}) = p ^ 2 :=
      absNorm_span_natCast p
    have habsPp2 : Ideal.absNorm P ∣ p ^ 2 :=
      habsp ▸ Ideal.absNorm_dvd_absNorm_of_le hple
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow hp).mp habsPp2
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hkeq
      exact hP.ne_top (Ideal.absNorm_eq_one_iff.mp hkeq)
    have hle2' : Ideal.map (algebraMap ℤ O2) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 2 := by
      simpa [Ideal.map_span, Set.image_singleton] using hle2
    have hno3 : ¬ Ideal.map (algebraMap ℤ O2) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 3 :=
      not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow hp habsp hkeq hk0
    have hunram : ¬ Algebra.IsUnramifiedAt ℤ P :=
      not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ hp hpmemP hPbot hle2'
        hno3
    have hPdiff : P ∣ differentIdeal ℤ O2 := dvd_differentIdeal_iff.mpr hunram
    have habsP8 : Ideal.absNorm P ∣ 8 := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPdiff)
      rw [NumberField.absNorm_differentIdeal (K := QSqrtTwo), sqrtTwo_numberField_discr] at h
      simpa using h
    have hpdvd : p ∣ 8 := (hkeq ▸ dvd_pow_self p hk0).trans habsP8
    have hpdiv2 : p ∣ 2 := by
      have hpow : p ∣ 2 ^ 3 := by simpa using hpdvd
      exact hp.dvd_of_dvd_pow hpow
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdiv2
  · rintro rfl
    refine ⟨Ideal.span {sqrtTwoInteger}, isPrime_span_sqrtTwoInteger, ?_⟩
    have hcast : ((2 : ℕ) : O2) = (2 : O2) := by norm_num
    rw [hcast, span_two_eq]

/-- Each split prime over `7` is unramified: `(3 + √2)` has ramification index `1`. -/
theorem ramificationIdx_span_three_add_sqrtTwo :
    (Ideal.span {(7 : ℤ)}).ramificationIdx (Ideal.span {3 + sqrtTwoInteger}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    change Ideal.span {(7 : O2)} ≤ Ideal.span {3 + sqrtTwoInteger}
    rw [span_seven_eq]
    exact Ideal.mul_le_right
  · intro hle2
    have hram : ∃ P : Ideal O2, P.IsPrime ∧ Ideal.span {(7 : O2)} ≤ P ^ 2 := by
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
    change Ideal.span {(7 : O2)} ≤ Ideal.span {3 - sqrtTwoInteger}
    rw [span_seven_eq]
    exact Ideal.mul_le_left
  · intro hle2
    have hram : ∃ P : Ideal O2, P.IsPrime ∧ Ideal.span {(7 : O2)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {3 - sqrtTwoInteger}, isPrime_span_three_sub_sqrtTwo, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h72 := (ramified_iff_eq_two 7 (by norm_num)).mp hram
    norm_num at h72

/-- The inert prime `(3)` is unramified: it has ramification index `1`. -/
theorem ramificationIdx_span_three :
    (Ideal.span {(3 : ℤ)}).ramificationIdx (Ideal.span {(3 : O2)}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    simp
  · intro hle2
    have hram : ∃ P : Ideal O2, P.IsPrime ∧ Ideal.span {(3 : O2)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {(3 : O2)}, isPrime_span_three, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h32 := (ramified_iff_eq_two 3 Nat.prime_three).mp hram
    norm_num at h32

private theorem absNorm_span_prime_sqrtTwo_sub_of_mul (p : ℕ) (hp : p.Prime) (c k : ℤ)
    (hprod : (sqrtTwoInteger - (c : O2)) * (sqrtTwoInteger + (c : O2)) =
      ((p : ℕ) : O2) * (k : O2)) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : O2), sqrtTwoInteger - (c : O2)}) = p := by
  let P : Ideal O2 := Ideal.span {((p : ℕ) : O2), sqrtTwoInteger - (c : O2)}
  change Ideal.absNorm P = p
  have hp_memP : ((p : ℕ) : O2) ∈ P := Ideal.subset_span (Set.mem_insert _ _)
  have hsc_memP : sqrtTwoInteger - (c : O2) ∈ P :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hPle : Ideal.span {((p : ℕ) : O2)} ≤ P :=
    (Ideal.span_singleton_le_iff_mem _).mpr hp_memP
  have hPnot1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    intro htop
    have h1 : (1 : O2) ∈ P := htop ▸ Submodule.mem_top
    change (1 : O2) ∈ Ideal.span {((p : ℕ) : O2), sqrtTwoInteger - (c : O2)} at h1
    rw [Ideal.mem_span_pair] at h1
    obtain ⟨α, β, hαβ⟩ := h1
    have hsc' : sqrtTwoInteger + (c : O2) ∈ Ideal.span {((p : ℕ) : O2)} := by
      rw [Ideal.mem_span_singleton]
      refine ⟨α * (sqrtTwoInteger + (c : O2)) + β * (k : O2), ?_⟩
      calc sqrtTwoInteger + (c : O2)
          = (α * ((p : ℕ) : O2) + β * (sqrtTwoInteger - (c : O2))) *
              (sqrtTwoInteger + (c : O2)) := by
            rw [hαβ, one_mul]
        _ = ((p : ℕ) : O2) * (α * (sqrtTwoInteger + (c : O2)) + β * (k : O2)) := by
            linear_combination β * hprod
    refine unit_sqrtTwo_coeff_not_mem p hp.two_le c 1 (Or.inl rfl) ?_
    rw [show ((c : ℤ) : O2) + ((1 : ℤ) : O2) * sqrtTwoInteger =
      sqrtTwoInteger + (c : O2) by
        push_cast
        ring]
    exact hsc'
  have hPnotsq : Ideal.absNorm P ≠ p ^ 2 := by
    intro hNP
    have heq := eq_of_le_of_absNorm_eq hPle (absNorm_span_natCast p) hNP
      (pow_ne_zero 2 hp.pos.ne')
    refine unit_sqrtTwo_coeff_not_mem p hp.two_le (-c) 1 (Or.inl rfl) ?_
    rw [show (((-c : ℤ) : O2) + ((1 : ℤ) : O2) * sqrtTwoInteger) =
      sqrtTwoInteger - (c : O2) by
        push_cast
        ring]
    rw [heq]
    exact hsc_memP
  exact eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq hp
    ((absNorm_span_natCast p) ▸ Ideal.absNorm_dvd_absNorm_of_le hPle) hPnot1 hPnotsq

private theorem pm_one_mod_eight_of_prime_norm (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ P : Ideal O2, P.IsPrime ∧ Ideal.span {(p : O2)} ≤ P ∧ Ideal.absNorm P = p) →
      p % 8 = 1 ∨ p % 8 = 7 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rintro ⟨P, hPprime, hPle, hNP⟩
  have hcard : Nat.card (O2 ⧸ P) = p := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hNP
    exact hNP
  haveI : Finite (O2 ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.pos.ne')
  haveI : Fintype (O2 ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card (O2 ⧸ P) = p := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let e := ZMod.ringEquivOfPrime (O2 ⧸ P) hp hcard'
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
      ∃ P : Ideal O2, P.IsPrime ∧ Ideal.span {(p : O2)} ≤ P ∧ Ideal.absNorm P = p := by
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
  have hkO2 : (2 : O2) - (c : O2) * (c : O2) = ((p : ℕ) : O2) * (k : O2) := by
    have h := congrArg (fun n : ℤ => ((n : ℤ) : O2)) hk
    push_cast at h
    exact h
  have hprod : (sqrtTwoInteger - (c : O2)) * (sqrtTwoInteger + (c : O2)) =
      ((p : ℕ) : O2) * (k : O2) := by
    calc (sqrtTwoInteger - (c : O2)) * (sqrtTwoInteger + (c : O2)) =
          sqrtTwoInteger ^ 2 - (c : O2) * (c : O2) := by ring
      _ = (2 : O2) - (c : O2) * (c : O2) := by rw [sqrtTwoInteger_sq]
      _ = ((p : ℕ) : O2) * (k : O2) := hkO2
  let P : Ideal O2 := Ideal.span {((p : ℕ) : O2), sqrtTwoInteger - (c : O2)}
  have hPle : Ideal.span {((p : ℕ) : O2)} ≤ P :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span (Set.mem_insert _ _))
  have hNP : Ideal.absNorm P = p := absNorm_span_prime_sqrtTwo_sub_of_mul p hp c k hprod
  have hPprime : P.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hNP]
    exact (Nat.irreducible_iff_nat_prime p).mpr hp
  exact ⟨P, hPprime, hPle, hNP⟩

private theorem exists_prime_norm_iff_pm_one_mod_eight (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ P : Ideal O2, P.IsPrime ∧ Ideal.span {(p : O2)} ≤ P ∧ Ideal.absNorm P = p) ↔
      p % 8 = 1 ∨ p % 8 = 7 := by
  constructor
  · exact pm_one_mod_eight_of_prime_norm p hp hp2
  · exact exists_prime_norm_of_pm_one_mod_eight p hp hp2

private theorem pm_one_mod_eight_of_splits (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ P Q : Ideal O2, P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : O2)} = P * Q) → p % 8 = 1 ∨ p % 8 = 7 := by
  rintro ⟨P, Q, hPprime, hQprime, hPQne, hspan⟩
  have hPle : Ideal.span {(p : O2)} ≤ P := by
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
  have hspan' : Ideal.span {((p : ℕ) : O2)} = P * Q := by
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
      ∃ P Q : Ideal O2, P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
        Ideal.span {(p : O2)} = P * Q := by
  intro hmod
  obtain ⟨P, hPprime, hPle, hPnorm⟩ :=
    (exists_prime_norm_iff_pm_one_mod_eight p hp hp2).mpr hmod
  obtain ⟨Q, hspan⟩ := Ideal.dvd_iff_le.mpr hPle
  have hQnorm : Ideal.absNorm Q = p := by
    have hmul := _root_.map_mul Ideal.absNorm P Q
    have hspan' : Ideal.span {((p : ℕ) : O2)} = P * Q := by
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
    have hram : ∃ R : Ideal O2, R.IsPrime ∧ Ideal.span {(p : O2)} ≤ R ^ 2 := by
      refine ⟨P, hPprime, ?_⟩
      rw [hspan, h, sq]
    exact hp2 ((ramified_iff_eq_two p hp).mp hram)
  exact ⟨P, Q, hPprime, hQprime, hPQ, by simpa using hspan⟩

/-- The quadratic splitting law for `ℚ(√2)`: an odd rational prime `p` splits into two
distinct primes iff `p ≡ ±1 (mod 8)` (i.e. iff `2` is a quadratic residue mod `p`, by the
second supplement to quadratic reciprocity), and is inert otherwise. -/
theorem splits_iff_pm_one_mod_eight (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ P Q : Ideal O2, P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : O2)} = P * Q) ↔ p % 8 = 1 ∨ p % 8 = 7 := by
  constructor
  · exact pm_one_mod_eight_of_splits p hp hp2
  · exact splits_of_pm_one_mod_eight p hp hp2


end NumberField.SqrtTwo
