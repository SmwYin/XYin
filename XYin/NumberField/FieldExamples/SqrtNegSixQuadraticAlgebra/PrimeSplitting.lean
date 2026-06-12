import XYin.NumberField.FieldExamples.SqrtNegSixQuadraticAlgebra.NormForm

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors QuadraticAlgebra

namespace XYin.NumberField.New.SqrtNegSixQuadraticAlgebra

/-! ## 5. Splitting of primes -/

/-- The ramified prime above `2`: the ideal `(2, θ)`. It is *not* principal — see
`not_isPrincipal_primeAboveTwo`. -/
def primeAboveTwo : Ideal (𝓞 K) := Ideal.span {(2 : 𝓞 K), thetaInt}

/-- The ramified prime above `3`: the ideal `(3, θ)`. -/
def primeAboveThree : Ideal (𝓞 K) := Ideal.span {(3 : 𝓞 K), thetaInt}

/-- `2` is ramified: `(2) = (2, θ)²`. -/
theorem span_two_eq : Ideal.span {(2 : 𝓞 K)} = primeAboveTwo ^ 2 := by
  rw [sq, primeAboveTwo, Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have h4 : (2 : 𝓞 K) * 2 ∈
        Ideal.span
          ({(2 : 𝓞 K) * 2, (2 : 𝓞 K) * thetaInt, thetaInt * 2,
            thetaInt * thetaInt} : Set (𝓞 K)) :=
      Ideal.subset_span (by simp)
    have hθ2 : thetaInt * thetaInt ∈
        Ideal.span
          ({(2 : 𝓞 K) * 2, (2 : 𝓞 K) * thetaInt, thetaInt * 2,
            thetaInt * thetaInt} : Set (𝓞 K)) :=
      Ideal.subset_span (by simp)
    convert Ideal.sub_mem _ (neg_mem h4) hθ2 using 1
    rw [show thetaInt * thetaInt = thetaInt ^ 2 by ring, thetaInt_sq]
    ring
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.mem_span_singleton.mpr ⟨(2 : 𝓞 K), by ring⟩
    · exact Ideal.mem_span_singleton.mpr ⟨thetaInt, by ring⟩
    · exact Ideal.mem_span_singleton.mpr ⟨thetaInt, by ring⟩
    · rw [show thetaInt * thetaInt = thetaInt ^ 2 by ring, thetaInt_sq]
      exact Ideal.mem_span_singleton.mpr ⟨(-3 : 𝓞 K), by ring⟩

/-- `(2, θ)` is a prime ideal of norm `2`. -/
theorem isPrime_primeAboveTwo : primeAboveTwo.IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  have habs : Ideal.absNorm primeAboveTwo = 2 := by
    have hspan : Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) = 4 := by
      have h := intNorm_eq_normForm 2 0
      have heq : (2 : 𝓞 K) = (2 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt := by simp
      rw [Ideal.absNorm_span_singleton, heq, h]
      rfl
    have h := congrArg Ideal.absNorm span_two_eq
    rw [hspan, map_pow] at h
    nlinarith
  rw [habs]
  exact (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)

/-- The ramified prime `(2, θ)` has norm `2`. -/
theorem absNorm_primeAboveTwo : Ideal.absNorm primeAboveTwo = 2 := by
  have hspan : Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) = 4 := by
    have h := intNorm_eq_normForm 2 0
    have heq : (2 : 𝓞 K) = (2 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt := by simp
    rw [Ideal.absNorm_span_singleton, heq, h]
    rfl
  have h := congrArg Ideal.absNorm span_two_eq
  rw [hspan, map_pow] at h
  nlinarith

/-- `(2, θ)` is not principal: no element of `ℤ[√-6]` has norm `±2`, since `x² + 6y² = 2`
has no integer solutions. This single ideal witnesses the nontrivial class group. -/
theorem not_isPrincipal_primeAboveTwo : ¬ Submodule.IsPrincipal primeAboveTwo := by
  intro hprincipal
  haveI : Submodule.IsPrincipal primeAboveTwo := hprincipal
  let a := Submodule.IsPrincipal.generator primeAboveTwo
  have hspan : Ideal.span ({a} : Set (𝓞 K)) = primeAboveTwo := by
    exact Ideal.span_singleton_generator primeAboveTwo
  have habs : (Algebra.norm ℤ a).natAbs = 2 := by
    rw [← Ideal.absNorm_span_singleton, hspan, absNorm_primeAboveTwo]
  obtain ⟨x, y, ha⟩ := exists_eq_smul_one_add_smul_theta a
  have hnorm : Algebra.norm ℤ a = x ^ 2 + 6 * y ^ 2 := by
    rw [ha, intNorm_eq_normForm]
  rw [hnorm, Int.natAbs_eq_iff] at habs
  rcases habs with h | h
  · exact normForm_ne_two x y h
  · have hnonneg : (0 : ℤ) ≤ x ^ 2 + 6 * y ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg y]
    omega

/-- `3` is ramified: `(3) = (3, θ)²`. -/
theorem span_three_eq : Ideal.span {(3 : 𝓞 K)} = primeAboveThree ^ 2 := by
  rw [sq, primeAboveThree, Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have h9 := Ideal.subset_span
      (show (3 : 𝓞 K) * 3 ∈
        ({(3 : 𝓞 K) * 3, (3 : 𝓞 K) * thetaInt, thetaInt * 3,
          thetaInt * thetaInt} : Set (𝓞 K)) by simp)
    have hθ2 := Ideal.subset_span
      (show thetaInt * thetaInt ∈
        ({(3 : 𝓞 K) * 3, (3 : 𝓞 K) * thetaInt, thetaInt * 3,
          thetaInt * thetaInt} : Set (𝓞 K)) by simp)
    convert Ideal.add_mem _ h9 hθ2 using 1
    rw [show thetaInt * thetaInt = thetaInt ^ 2 by ring, thetaInt_sq]
    ring
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.mem_span_singleton.mpr ⟨(3 : 𝓞 K), by ring⟩
    · exact Ideal.mem_span_singleton.mpr ⟨thetaInt, by ring⟩
    · exact Ideal.mem_span_singleton.mpr ⟨thetaInt, by ring⟩
    · rw [show thetaInt * thetaInt = thetaInt ^ 2 by ring, thetaInt_sq]
      exact Ideal.mem_span_singleton.mpr ⟨(-2 : 𝓞 K), by ring⟩

/-- `(3, θ)` is a prime ideal of norm `3`, also non-principal (`x² + 6y² = 3` is
unsolvable). -/
theorem isPrime_primeAboveThree : primeAboveThree.IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  have habs : Ideal.absNorm primeAboveThree = 3 := by
    have hspan : Ideal.absNorm (Ideal.span {(3 : 𝓞 K)}) = 9 := by
      have h := intNorm_eq_normForm 3 0
      have heq : (3 : 𝓞 K) = (3 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt := by simp
      rw [Ideal.absNorm_span_singleton, heq, h]
      rfl
    have h := congrArg Ideal.absNorm span_three_eq
    rw [hspan, map_pow] at h
    nlinarith
  rw [habs]
  exact (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)

/-- The elementary identity `7 = (1 + θ)(1 - θ)` in `ℤ[θ]` (norms: `1 + 6 = 7`). -/
theorem seven_eq_mul : (7 : 𝓞 K) = (1 + thetaInt) * (1 - thetaInt) := by
  ring_nf; rw [thetaInt_sq]; ring

/-- `7` splits with *principal* prime factors: `(7) = (1 + θ)(1 - θ)`, matching the
representation `7 = 1² + 6 · 1²` by the principal form. -/
theorem span_seven_eq :
    Ideal.span {(7 : 𝓞 K)} = Ideal.span {1 + thetaInt} * Ideal.span {1 - thetaInt} := by
  rw [Ideal.span_singleton_mul_span_singleton, ← seven_eq_mul]

/-- `(1 + θ)` is a prime ideal of norm `7`. -/
theorem isPrime_span_one_add_theta : (Ideal.span {1 + thetaInt}).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  have habs : Ideal.absNorm (Ideal.span {1 + thetaInt}) = 7 := by
    have h := intNorm_eq_normForm 1 1
    have heq : (1 : 𝓞 K) + thetaInt = (1 : ℤ) • (1 : 𝓞 K) + (1 : ℤ) • thetaInt := by
      simp
    rw [Ideal.absNorm_span_singleton, heq, h]
    rfl
  rw [habs]
  exact (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)

/-- `5` splits, but with *non-principal* prime factors `(5, θ - 2)` and `(5, θ + 2)`:
`-6 ≡ 2² (mod 5)` yet `x² + 6y² = 5` has no integer solutions (the prime `5` is represented
by the non-principal genus form `2x² + 3y²` instead). -/
theorem span_five_eq :
    Ideal.span {(5 : 𝓞 K)} =
      Ideal.span {(5 : 𝓞 K), thetaInt - 2} * Ideal.span {(5 : 𝓞 K), thetaInt + 2} := by
  rw [Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have h25 : (5 : 𝓞 K) * 5 ∈
        Ideal.span
          ({(5 : 𝓞 K) * 5, (5 : 𝓞 K) * (thetaInt + 2), (thetaInt - 2) * 5,
            (thetaInt - 2) * (thetaInt + 2)} : Set (𝓞 K)) :=
      Ideal.subset_span (by simp)
    have hlast : (thetaInt - 2) * (thetaInt + 2) ∈
        Ideal.span
          ({(5 : 𝓞 K) * 5, (5 : 𝓞 K) * (thetaInt + 2), (thetaInt - 2) * 5,
            (thetaInt - 2) * (thetaInt + 2)} : Set (𝓞 K)) :=
      Ideal.subset_span (by simp)
    convert Ideal.add_mem _ h25 (Ideal.mul_mem_left _ (2 : 𝓞 K) hlast) using 1
    rw [show (thetaInt - 2) * (thetaInt + 2) = thetaInt ^ 2 - 4 by ring, thetaInt_sq]
    ring
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.mem_span_singleton.mpr ⟨(5 : 𝓞 K), by ring⟩
    · exact Ideal.mem_span_singleton.mpr ⟨thetaInt + 2, by ring⟩
    · exact Ideal.mem_span_singleton.mpr ⟨thetaInt - 2, by ring⟩
    · rw [show (thetaInt - 2) * (thetaInt + 2) = thetaInt ^ 2 - 4 by ring, thetaInt_sq]
      exact Ideal.mem_span_singleton.mpr ⟨(-2 : 𝓞 K), by ring⟩

private theorem span_five_theta_sub_two_ne_top :
    Ideal.span {(5 : 𝓞 K), thetaInt - 2} ≠ ⊤ := by
  intro htop
  have hmem : (1 : 𝓞 K) ∈ Ideal.span {(5 : 𝓞 K), thetaInt - 2} := by
    rw [htop]
    trivial
  rw [Ideal.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  obtain ⟨x, y, ha⟩ := exists_eq_smul_one_add_smul_theta a
  obtain ⟨u, v, hb⟩ := exists_eq_smul_one_add_smul_theta b
  have hsum : ∑ i : Fin 2,
      (![5 * x - 2 * u - 6 * v - 1, 5 * y + u - 2 * v] i) •
        (![(1 : 𝓞 K), thetaInt] i) = 0 := by
    rw [Fin.sum_univ_two]
    rw [ha, hb] at hab
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zsmul_eq_mul] at hab ⊢
    push_cast at hab ⊢
    linear_combination hab - (v : 𝓞 K) * thetaInt_sq
  have hcoeff0 := Fintype.linearIndependent_iff.mp linearIndependent_one_theta _ hsum 0
  have hcoeff1 := Fintype.linearIndependent_iff.mp linearIndependent_one_theta _ hsum 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hcoeff0 hcoeff1
  have hdiv : (5 : ℤ) ∣ 1 := by
    refine ⟨-(x + y + v), ?_⟩
    omega
  have := Int.le_of_dvd zero_lt_one hdiv
  norm_num at this

/-- `(5, θ - 2)` is a non-principal prime of norm `5`. -/
theorem not_isPrincipal_primeAboveFive :
    ¬ Submodule.IsPrincipal (Ideal.span {(5 : 𝓞 K), thetaInt - 2}) := by
  intro hprincipal
  let I : Ideal (𝓞 K) := Ideal.span {(5 : 𝓞 K), thetaInt - 2}
  have hI_ne_top : I ≠ ⊤ := by
    simpa [I] using span_five_theta_sub_two_ne_top
  haveI : Submodule.IsPrincipal I := by simpa [I] using hprincipal
  let a := Submodule.IsPrincipal.generator I
  have hspan : Ideal.span ({a} : Set (𝓞 K)) = I := by
    exact Ideal.span_singleton_generator I
  have h5mem : (5 : 𝓞 K) ∈ Ideal.span ({a} : Set (𝓞 K)) := by
    rw [hspan]
    change (5 : 𝓞 K) ∈ Ideal.span {(5 : 𝓞 K), thetaInt - 2}
    exact Ideal.subset_span (by simp)
  have hthetamem : thetaInt - 2 ∈ Ideal.span ({a} : Set (𝓞 K)) := by
    rw [hspan]
    change thetaInt - 2 ∈ Ideal.span {(5 : 𝓞 K), thetaInt - 2}
    exact Ideal.subset_span (by simp)
  rw [Ideal.mem_span_singleton] at h5mem hthetamem
  obtain ⟨b, hb⟩ := h5mem
  obtain ⟨c, hc⟩ := hthetamem
  have hN5 : Algebra.norm ℤ (5 : 𝓞 K) = 25 := by
    have h := intNorm_eq_normForm 5 0
    have heq : (5 : 𝓞 K) = (5 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt := by
      simp
    rw [← heq] at h
    exact h
  have hNtheta : Algebra.norm ℤ (thetaInt - 2) = 10 := by
    have h := intNorm_eq_normForm (-2) 1
    have heq : thetaInt - 2 = (-2 : ℤ) • (1 : 𝓞 K) + (1 : ℤ) • thetaInt := by
      simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_one]
      ring
    rw [heq, h]
    norm_num
  let A : ℤ := Algebra.norm ℤ a
  let B : ℤ := Algebra.norm ℤ b
  let C : ℤ := Algebra.norm ℤ c
  have hprod5 : A * B = 25 := by
    have h := congrArg (Algebra.norm ℤ) hb
    rw [map_mul, hN5] at h
    exact (by simpa [A, B] using h.symm)
  have hprod10 : A * C = 10 := by
    have h := congrArg (Algebra.norm ℤ) hc
    rw [map_mul, hNtheta] at h
    exact (by simpa [A, C] using h.symm)
  have hA_nonneg : 0 ≤ A := by simpa [A] using intNorm_nonneg a
  have hB_nonneg : 0 ≤ B := by simpa [B] using intNorm_nonneg b
  have hC_nonneg : 0 ≤ C := by simpa [C] using intNorm_nonneg c
  have hA_ne1 : A ≠ 1 := by
    intro hA1
    have hunit : IsUnit a := (isUnit_iff_intNorm_eq_one a).mpr (by simpa [A] using hA1)
    exact hI_ne_top (by
      rw [← hspan]
      exact Ideal.span_singleton_eq_top.mpr hunit)
  have hA_ne5 : A ≠ 5 := by
    intro hA5
    exact intNorm_ne_five a (by simpa [A] using hA5)
  have hA_pos : 0 < A := by nlinarith
  have hB_pos : 0 < B := by nlinarith
  have hA_le : A ≤ 25 := by nlinarith [hprod5, hB_pos]
  interval_cases A <;> omega

/-- `13` is inert in `ℚ(√-6)`: `-6` is not a square mod `13`. -/
theorem isPrime_span_thirteen : (Ideal.span {(13 : 𝓞 K)}).IsPrime := by
  have habs169 : Ideal.absNorm (Ideal.span ({(13 : 𝓞 K)} : Set (𝓞 K))) = 169 := by
    have h := intNorm_eq_normForm 13 0
    have heq : (13 : 𝓞 K) = (13 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt := by
      simp
    rw [Ideal.absNorm_span_singleton, heq, h]
    rfl
  have htop : Ideal.span ({(13 : 𝓞 K)} : Set (𝓞 K)) ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at habs169
    norm_num at habs169
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ htop
  have hdvd : Ideal.absNorm M ∣ 169 := habs169 ▸ Ideal.absNorm_dvd_absNorm_of_le hMle
  have hM1 : Ideal.absNorm M ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hMmax.ne_top
  have hM13 : Ideal.absNorm M ≠ 13 := by
    intro hcard
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcard
    haveI : Finite ((𝓞 K) ⧸ M) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    haveI : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _
    have hcard' : Fintype.card ((𝓞 K) ⧸ M) = 13 := by
      rw [← Nat.card_eq_fintype_card]
      exact hcard
    let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ M) (by norm_num) hcard'
    obtain ⟨t, ht⟩ := e.surjective (Ideal.Quotient.mk M thetaInt)
    have ht2 : t ^ 2 + 6 = 0 := by
      apply e.injective
      rw [map_add, map_pow, ht, map_ofNat, ← map_pow (Ideal.Quotient.mk M), thetaInt_sq]
      rw [map_zero, map_neg, map_ofNat]
      ring
    clear ht
    revert t
    decide
  have hM169 : Ideal.absNorm M = 169 := by
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow (show Nat.Prime 13 by norm_num)).mp
      (show Ideal.absNorm M ∣ 13 ^ 2 from by simpa using hdvd)
    interval_cases k
    · rw [pow_zero] at hkeq
      exact absurd hkeq hM1
    · rw [pow_one] at hkeq
      exact absurd hkeq hM13
    · rw [hkeq]
      norm_num
  have heq : Ideal.span ({(13 : 𝓞 K)} : Set (𝓞 K)) = M := by
    obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hMle
    have hmul := _root_.map_mul Ideal.absNorm M C
    rw [← hC, habs169, hM169] at hmul
    have hC1 : Ideal.absNorm C = 1 := by
      nlinarith
    rw [hC, Ideal.absNorm_eq_one_iff.mp hC1, Ideal.mul_top]
  rw [heq]
  exact hMmax.isPrime

/-- The splitting law for `ℚ(√-6)`: a prime `p ∤ 24` splits into two distinct primes iff
`-6` is a square mod `p`, iff `p ≡ 1, 5, 7, 11 (mod 24)`. -/
theorem splits_iff_mod_twentyfour (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) ↔
        p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 := by
  sorry

/-- A rational prime `p` ramifies in `ℚ(√-6)` iff `p ∈ {2, 3}`, i.e. iff `p` divides the
discriminant `-24`. -/
theorem ramified_iff (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔ p = 2 ∨ p = 3 := by
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
    have hfin : Module.finrank ℤ (𝓞 K) = 2 := by
      rw [Module.finrank_eq_card_basis concreteIntegralBasis, Fintype.card_fin]
    have habsp : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 2 := by
      rw [Ideal.absNorm_span_singleton]
      have hcast : ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) ((p : ℕ) : ℤ) := by
        push_cast
        rfl
      rw [hcast, Algebra.norm_algebraMap, hfin, Int.natAbs_pow, Int.natAbs_natCast]
    have habsPp2 : Ideal.absNorm P ∣ p ^ 2 :=
      habsp ▸ Ideal.absNorm_dvd_absNorm_of_le hple
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow hp).mp habsPp2
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hkeq
      exact hP.ne_top (Ideal.absNorm_eq_one_iff.mp hkeq)
    have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) =
        Ideal.span {((p : ℕ) : 𝓞 K)} := by
      rw [Ideal.map_span, Set.image_singleton]
      norm_num
    have hle2' : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤
        P ^ 2 := by
      rw [hmap]
      exact hle2
    have hno3 : ¬ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤
        P ^ 3 := by
      intro h3
      rw [hmap] at h3
      have hd := Ideal.absNorm_dvd_absNorm_of_le h3
      rw [map_pow, habsp, hkeq, ← pow_mul] at hd
      rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
      omega
    have hidx : Ideal.ramificationIdx (Ideal.span {((p : ℕ) : ℤ)}) P ≠ 1 := by
      rw [Ideal.ramificationIdx_spec hle2' hno3]
      norm_num
    have hund : Ideal.under ℤ P = Ideal.span {((p : ℕ) : ℤ)} := by
      have hmem : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ P := by
        rw [Ideal.under, Ideal.mem_comap]
        have hcast2 : algebraMap ℤ (𝓞 K) ((p : ℕ) : ℤ) = ((p : ℕ) : 𝓞 K) := by
          push_cast
          rfl
        rw [hcast2]
        exact hpmemP
      have hle : Ideal.span {((p : ℕ) : ℤ)} ≤ Ideal.under ℤ P := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hmem
      have hprime : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
          (Nat.prime_iff_prime_int.mp hp)
      have hbot : Ideal.span {((p : ℕ) : ℤ)} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hp.ne_zero
      have hnetop : Ideal.under ℤ P ≠ ⊤ := by
        intro h
        have h1 : (1 : ℤ) ∈ Ideal.under ℤ P := h ▸ Submodule.mem_top
        rw [Ideal.under, Ideal.mem_comap, map_one] at h1
        exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
      exact ((hprime.isMaximal hbot).eq_of_le hnetop hle).symm
    have hunram : ¬ Algebra.IsUnramifiedAt ℤ P := by
      rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot, hund]
      exact hidx
    have hPdiff : P ∣ differentIdeal ℤ (𝓞 K) := dvd_differentIdeal_iff.mpr hunram
    have habsP24 : Ideal.absNorm P ∣ 24 := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPdiff)
      rw [NumberField.absNorm_differentIdeal (K := K), numberField_discr_eq] at h
      simpa using h
    have hpdvd : p ∣ 24 := (hkeq ▸ dvd_pow_self p hk0).trans habsP24
    have hpor : p ∣ 2 ^ 3 ∨ p ∣ 3 := by
      exact hp.dvd_mul.mp (by simpa using hpdvd)
    rcases hpor with hp2pow | hp3dvd
    · left
      have hp2dvd : p ∣ 2 := hp.dvd_of_dvd_pow hp2pow
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp2dvd
    · right
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp3dvd
  · rintro (rfl | rfl)
    · refine ⟨primeAboveTwo, isPrime_primeAboveTwo, ?_⟩
      have hcast : ((2 : ℕ) : 𝓞 K) = (2 : 𝓞 K) := by norm_num
      rw [hcast, span_two_eq]
    · refine ⟨primeAboveThree, isPrime_primeAboveThree, ?_⟩
      have hcast : ((3 : ℕ) : 𝓞 K) = (3 : 𝓞 K) := by norm_num
      rw [hcast, span_three_eq]


end XYin.NumberField.New.SqrtNegSixQuadraticAlgebra
