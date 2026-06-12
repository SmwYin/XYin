import XYin.NumberField.FieldExamples.SqrtNegSixQuadraticAlgebra.NormForm

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors QuadraticAlgebra

namespace XYin.NumberField.New.SqrtNegSixQuadraticAlgebra

/-! ## 5. Splitting of primes -/

/-- Nonzero ideals with equal absolute norms and one inclusion are equal. -/
private theorem eq_of_le_of_absNorm_eq {I J : Ideal (𝓞 K)} (hle : I ≤ J) {n : ℕ}
    (hI : Ideal.absNorm I = n) (hJ : Ideal.absNorm J = n) (hn : n ≠ 0) : I = J := by
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hmul := _root_.map_mul Ideal.absNorm J C
  rw [← hC, hI, hJ] at hmul
  have hC1 : Ideal.absNorm C = 1 :=
    (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn)
      (by rw [mul_one]; exact hmul)).symm
  rw [hC, Ideal.absNorm_eq_one_iff.mp hC1, Ideal.mul_top]

/-- A rational prime generates an ideal of norm `p²` in `𝓞 K`. -/
private theorem absNorm_span_natCast (p : ℕ) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 2 := by
  have h := intNorm_eq_normForm (p : ℤ) 0
  have hps : ((p : ℤ)) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt = ((p : ℕ) : 𝓞 K) := by
    simp
  rw [hps] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  simp [Int.natAbs_pow]

/-- An element `A + Bθ` with `B = ±1` is never divisible by a rational prime `p ≥ 2`. -/
private theorem unit_theta_coeff_not_mem (p : ℕ) (hp : 2 ≤ p) (A B : ℤ)
    (hB : B = 1 ∨ B = -1) :
    ((A : ℤ) : 𝓞 K) + ((B : ℤ) : 𝓞 K) * thetaInt ∉
      Ideal.span {((p : ℕ) : 𝓞 K)} := by
  intro hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨A', m, hAm⟩ := exists_eq_smul_one_add_smul_theta z
  rw [hAm] at hz
  have hsum : ∑ i : Fin 2,
      (![A - p * A', B - p * m] i) • (![(1 : 𝓞 K), thetaInt] i) = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zsmul_eq_mul] at hz ⊢
    push_cast at hz ⊢
    linear_combination hz
  have hcoeff := Fintype.linearIndependent_iff.mp linearIndependent_one_theta _ hsum 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hcoeff
  rcases hB with rfl | rfl
  · have h1 : (p : ℤ) ∣ 1 := ⟨m, by linarith [hcoeff]⟩
    have := Int.le_of_dvd one_pos h1
    omega
  · have h1 : (p : ℤ) ∣ 1 := ⟨-m, by linarith [hcoeff]⟩
    have := Int.le_of_dvd one_pos h1
    omega

private theorem isSquare_neg_six_iff_mod_twentyfour
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    IsSquare ((-6 : ℤ) : ZMod p) ↔
      p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hjmod : jacobiSym (-6) p = jacobiSym (-6) (p % 24) := by
    simpa using (jacobiSym.mod_right (-6) hodd)
  have hcases : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨
      p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := by
    have hpmod2 : p % 2 ≠ 0 := by
      intro h0
      exact hp2 (((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm)
    have hpmod3 : p % 3 ≠ 0 := by
      intro h0
      exact hp3 (((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm)
    omega
  constructor
  · intro hs
    have hnotneg : jacobiSym (-6) p ≠ -1 := by
      intro hj
      exact (ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp hj) hs
    rcases hcases with h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exfalso; apply hnotneg; rw [hjmod, h]; norm_num
    · exfalso; apply hnotneg; rw [hjmod, h]; norm_num
    · exfalso; apply hnotneg; rw [hjmod, h]; norm_num
    · exfalso; apply hnotneg; rw [hjmod, h]; norm_num
  · intro hmod
    apply ZMod.isSquare_of_jacobiSym_eq_one
    rw [hjmod]
    rcases hmod with h | h | h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
    · rw [h]; norm_num
    · rw [h]; norm_num

private theorem exists_int_inverse_mod_prime
    (p : ℕ) [Fact p.Prime] (a : ℤ) (ha : (a : ZMod p) ≠ 0) :
    ∃ m : ℕ, ∃ k : ℤ, (m : ℤ) * a - 1 = (p : ℤ) * k := by
  refine ⟨(((a : ZMod p)⁻¹).val), ?_⟩
  have hm : (((((a : ZMod p)⁻¹).val : ℕ) : ZMod p) * (a : ZMod p)) = 1 := by
    rw [ZMod.natCast_rightInverse]
    exact inv_mul_cancel₀ ha
  have hlift : (p : ℤ) ∣ (((((a : ZMod p)⁻¹).val : ℕ) : ℤ) * a - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination hm
  obtain ⟨k, hk⟩ := hlift
  exact ⟨k, hk⟩

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

theorem absNorm_primeAboveThree : Ideal.absNorm primeAboveThree = 3 := by
  have hspan : Ideal.absNorm (Ideal.span {(3 : 𝓞 K)}) = 9 := by
    have h := intNorm_eq_normForm 3 0
    have heq : (3 : 𝓞 K) = (3 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt := by simp
    rw [Ideal.absNorm_span_singleton, heq, h]
    rfl
  have h := congrArg Ideal.absNorm span_three_eq
  rw [hspan, map_pow] at h
  nlinarith

/-- The principal ideal `(θ)` is the product of the two ramified primes above `2` and `3`. -/
theorem span_theta_eq : Ideal.span {thetaInt} = primeAboveTwo * primeAboveThree := by
  rw [primeAboveTwo, primeAboveThree, Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have h2θ : (2 : 𝓞 K) * thetaInt ∈
        Ideal.span
          ({(2 : 𝓞 K) * 3, (2 : 𝓞 K) * thetaInt, thetaInt * 3,
            thetaInt * thetaInt} : Set (𝓞 K)) :=
      Ideal.subset_span (by simp)
    have h3θ : thetaInt * 3 ∈
        Ideal.span
          ({(2 : 𝓞 K) * 3, (2 : 𝓞 K) * thetaInt, thetaInt * 3,
            thetaInt * thetaInt} : Set (𝓞 K)) :=
      Ideal.subset_span (by simp)
    convert Ideal.sub_mem _ h3θ h2θ using 1
    ring
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · rw [show (2 : 𝓞 K) * 3 = thetaInt * (-thetaInt) by
        rw [show thetaInt * (-thetaInt) = -(thetaInt ^ 2) by ring, thetaInt_sq]
        ring]
      exact Ideal.mem_span_singleton.mpr ⟨-thetaInt, by ring⟩
    · exact Ideal.mem_span_singleton.mpr ⟨(2 : 𝓞 K), by ring⟩
    · exact Ideal.mem_span_singleton.mpr ⟨(3 : 𝓞 K), by ring⟩
    · exact Ideal.mem_span_singleton.mpr ⟨thetaInt, by ring⟩

theorem ideal_eq_primeAboveTwo_of_absNorm_eq_two
    (I : Ideal (𝓞 K)) (hI : Ideal.absNorm I = 2) : I = primeAboveTwo := by
  have hIprime : I.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hI]
    exact (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)
  haveI : I.IsPrime := hIprime
  have h2mem : (2 : 𝓞 K) ∈ I := by
    have hunder := Ideal.span_singleton_absNorm (S := 𝓞 K) (I := I) (by rw [hI]; norm_num)
    have hmem_under : (2 : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) I := by
      rw [← hunder]
      rw [hI]
      exact Ideal.mem_span_singleton_self _
    have hmem : ((2 : ℤ) : 𝓞 K) ∈ I := by
      simpa [Ideal.mem_comap] using hmem_under
    norm_num at hmem ⊢
    exact hmem
  have hθmem : thetaInt ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hsq : (Ideal.Quotient.mk I thetaInt) ^ 2 = 0 := by
      rw [← map_pow, thetaInt_sq]
      rw [map_neg, map_ofNat]
      change -(6 : (𝓞 K) ⧸ I) = 0
      have h6mem : (6 : 𝓞 K) ∈ I := by
        convert Ideal.mul_mem_left I (3 : 𝓞 K) h2mem using 1
        norm_num
      rw [← Ideal.Quotient.eq_zero_iff_mem] at h6mem
      norm_num at h6mem ⊢
      exact h6mem
    exact sq_eq_zero_iff.mp hsq
  symm
  exact eq_of_le_of_absNorm_eq (by
    rw [primeAboveTwo, Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact h2mem
    · exact hθmem) absNorm_primeAboveTwo hI (by norm_num)

theorem ideal_eq_primeAboveThree_of_absNorm_eq_three
    (I : Ideal (𝓞 K)) (hI : Ideal.absNorm I = 3) : I = primeAboveThree := by
  have hIprime : I.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hI]
    exact (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)
  haveI : I.IsPrime := hIprime
  have h3mem : (3 : 𝓞 K) ∈ I := by
    have hunder := Ideal.span_singleton_absNorm (S := 𝓞 K) (I := I) (by rw [hI]; norm_num)
    have hmem_under : (3 : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) I := by
      rw [← hunder]
      rw [hI]
      exact Ideal.mem_span_singleton_self _
    have hmem : ((3 : ℤ) : 𝓞 K) ∈ I := by
      simpa [Ideal.mem_comap] using hmem_under
    norm_num at hmem ⊢
    exact hmem
  have hθmem : thetaInt ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hsq : (Ideal.Quotient.mk I thetaInt) ^ 2 = 0 := by
      rw [← map_pow, thetaInt_sq]
      rw [map_neg, map_ofNat]
      change -(6 : (𝓞 K) ⧸ I) = 0
      have h6mem : (6 : 𝓞 K) ∈ I := by
        convert Ideal.mul_mem_left I (2 : 𝓞 K) h3mem using 1
        norm_num
      rw [← Ideal.Quotient.eq_zero_iff_mem] at h6mem
      norm_num at h6mem ⊢
      exact h6mem
    exact sq_eq_zero_iff.mp hsq
  symm
  exact eq_of_le_of_absNorm_eq (by
    rw [primeAboveThree, Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact h3mem
    · exact hθmem) absNorm_primeAboveThree hI (by norm_num)

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
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · rintro ⟨P, Q, hPprime, hQprime, hPQne, hspan⟩
    have hmul : Ideal.absNorm P * Ideal.absNorm Q = p ^ 2 := by
      rw [← _root_.map_mul Ideal.absNorm, ← hspan, absNorm_span_natCast]
    have hP1 : Ideal.absNorm P ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact hPprime.ne_top
    have hQ1 : Ideal.absNorm Q ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact hQprime.ne_top
    have hNP : Ideal.absNorm P = p := by
      obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp ⟨_, hmul.symm⟩
      interval_cases k
      · rw [pow_zero] at hkeq
        exact absurd hkeq hP1
      · rw [pow_one] at hkeq
        exact hkeq
      · exfalso
        rw [hkeq] at hmul
        have hQ1' : Ideal.absNorm Q = 1 :=
          Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by rw [mul_one]; exact hmul)
        exact hQ1 hQ1'
    have hcard : Nat.card ((𝓞 K) ⧸ P) = p := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hNP
      exact hNP
    haveI : Finite ((𝓞 K) ⧸ P) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.pos.ne')
    haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
    have hcard' : Fintype.card ((𝓞 K) ⧸ P) = p := by
      rw [← Nat.card_eq_fintype_card]
      exact hcard
    let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) hp hcard'
    obtain ⟨t, ht⟩ := e.surjective (Ideal.Quotient.mk P thetaInt)
    have ht2 : t ^ 2 + 6 = 0 := by
      apply e.injective
      rw [map_add, map_pow, ht, map_ofNat, ← map_pow (Ideal.Quotient.mk P), thetaInt_sq]
      rw [map_zero, map_neg, map_ofNat]
      ring
    have hsq : IsSquare ((-6 : ℤ) : ZMod p) := by
      refine ⟨t, ?_⟩
      push_cast
      linear_combination -ht2
    exact (isSquare_neg_six_iff_mod_twentyfour p hp hp2 hp3).mp hsq
  · intro hmod
    have hsq : IsSquare ((-6 : ℤ) : ZMod p) :=
      (isSquare_neg_six_iff_mod_twentyfour p hp hp2 hp3).mpr hmod
    obtain ⟨s, hs⟩ := hsq
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h0
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
        ((ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h0)))
    set c : ℤ := (s.val : ℤ) with hcdef
    set d : ℤ := ((-s).val : ℤ) with hddef
    have hct : ((c : ℤ) : ZMod p) = s := by
      rw [hcdef]
      exact_mod_cast ZMod.natCast_rightInverse s
    have hdt : ((d : ℤ) : ZMod p) = -s := by
      rw [hddef]
      exact_mod_cast ZMod.natCast_rightInverse (-s)
    have hdvd1 : (p : ℤ) ∣ c + d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hct, hdt]
      ring
    have hdvd2 : (p : ℤ) ∣ c * d - 6 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hct, hdt]
      linear_combination hs
    obtain ⟨k₁, hk₁⟩ := hdvd1
    obtain ⟨k₂, hk₂⟩ := hdvd2
    have hk₁K : (c : 𝓞 K) + (d : 𝓞 K) = ((p : ℕ) : 𝓞 K) * (k₁ : 𝓞 K) := by
      have h := congrArg (fun n : ℤ => ((n : ℤ) : 𝓞 K)) hk₁
      push_cast at h
      exact h
    have hk₂K : (c : 𝓞 K) * (d : 𝓞 K) - 6 =
        ((p : ℕ) : 𝓞 K) * (k₂ : 𝓞 K) := by
      have h := congrArg (fun n : ℤ => ((n : ℤ) : 𝓞 K)) hk₂
      push_cast at h
      exact h
    have hprod : (thetaInt - (c : 𝓞 K)) * (thetaInt - (d : 𝓞 K)) =
        ((p : ℕ) : 𝓞 K) * (-(k₁ : 𝓞 K) * thetaInt + (k₂ : 𝓞 K)) := by
      linear_combination thetaInt_sq - thetaInt * hk₁K + hk₂K
    set P := Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)} with hPdef
    set Q := Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (d : 𝓞 K)} with hQdef
    have hp_memP : ((p : ℕ) : 𝓞 K) ∈ P := Ideal.subset_span (Set.mem_insert _ _)
    have htc_memP : thetaInt - (c : 𝓞 K) ∈ P :=
      Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have hp_memQ : ((p : ℕ) : 𝓞 K) ∈ Q := Ideal.subset_span (Set.mem_insert _ _)
    have htd_memQ : thetaInt - (d : 𝓞 K) ∈ Q :=
      Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have hPle : Ideal.span {((p : ℕ) : 𝓞 K)} ≤ P :=
      (Ideal.span_singleton_le_iff_mem _).mpr hp_memP
    have hQle : Ideal.span {((p : ℕ) : 𝓞 K)} ≤ Q :=
      (Ideal.span_singleton_le_iff_mem _).mpr hp_memQ
    have hnorm : ∀ (I : Ideal (𝓞 K)), Ideal.span {((p : ℕ) : 𝓞 K)} ≤ I →
        Ideal.absNorm I ≠ 1 → Ideal.absNorm I ≠ p ^ 2 → Ideal.absNorm I = p := by
      intro I hle h1 hpsq
      obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp
        ((absNorm_span_natCast p) ▸ Ideal.absNorm_dvd_absNorm_of_le hle)
      interval_cases k
      · rw [pow_zero] at hkeq
        exact absurd hkeq h1
      · rw [pow_one] at hkeq
        exact hkeq
      · exact absurd hkeq hpsq
    have hPnot1 : Ideal.absNorm P ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      intro htop
      have h1 : (1 : 𝓞 K) ∈ P := htop ▸ Submodule.mem_top
      rw [hPdef, Ideal.mem_span_pair] at h1
      obtain ⟨α, β, hαβ⟩ := h1
      have htd : thetaInt - (d : 𝓞 K) ∈ Ideal.span {((p : ℕ) : 𝓞 K)} := by
        rw [Ideal.mem_span_singleton]
        refine ⟨α * (thetaInt - (d : 𝓞 K)) +
          β * (-(k₁ : 𝓞 K) * thetaInt + (k₂ : 𝓞 K)), ?_⟩
        calc thetaInt - (d : 𝓞 K)
            = (α * ((p : ℕ) : 𝓞 K) + β * (thetaInt - (c : 𝓞 K))) *
                (thetaInt - (d : 𝓞 K)) := by
              rw [hαβ, one_mul]
          _ = ((p : ℕ) : 𝓞 K) * (α * (thetaInt - (d : 𝓞 K)) +
                β * (-(k₁ : 𝓞 K) * thetaInt + (k₂ : 𝓞 K))) := by
              linear_combination β * hprod
      refine unit_theta_coeff_not_mem p hp.two_le (-d) 1 (Or.inl rfl) ?_
      rw [show ((-d : ℤ) : 𝓞 K) + ((1 : ℤ) : 𝓞 K) * thetaInt =
        thetaInt - (d : 𝓞 K) by push_cast; ring]
      exact htd
    have hQnot1 : Ideal.absNorm Q ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      intro htop
      have h1 : (1 : 𝓞 K) ∈ Q := htop ▸ Submodule.mem_top
      rw [hQdef, Ideal.mem_span_pair] at h1
      obtain ⟨α, β, hαβ⟩ := h1
      have htc : thetaInt - (c : 𝓞 K) ∈ Ideal.span {((p : ℕ) : 𝓞 K)} := by
        rw [Ideal.mem_span_singleton]
        refine ⟨α * (thetaInt - (c : 𝓞 K)) +
          β * (-(k₁ : 𝓞 K) * thetaInt + (k₂ : 𝓞 K)), ?_⟩
        calc thetaInt - (c : 𝓞 K)
            = (α * ((p : ℕ) : 𝓞 K) + β * (thetaInt - (d : 𝓞 K))) *
                (thetaInt - (c : 𝓞 K)) := by
              rw [hαβ, one_mul]
          _ = ((p : ℕ) : 𝓞 K) * (α * (thetaInt - (c : 𝓞 K)) +
                β * (-(k₁ : 𝓞 K) * thetaInt + (k₂ : 𝓞 K))) := by
              linear_combination β * hprod
      refine unit_theta_coeff_not_mem p hp.two_le (-c) 1 (Or.inl rfl) ?_
      rw [show ((-c : ℤ) : 𝓞 K) + ((1 : ℤ) : 𝓞 K) * thetaInt =
        thetaInt - (c : 𝓞 K) by push_cast; ring]
      exact htc
    have hPnotsq : Ideal.absNorm P ≠ p ^ 2 := by
      intro hNP
      have heq := eq_of_le_of_absNorm_eq hPle (absNorm_span_natCast p) hNP
        (pow_ne_zero 2 hp.pos.ne')
      refine unit_theta_coeff_not_mem p hp.two_le (-c) 1 (Or.inl rfl) ?_
      rw [show ((-c : ℤ) : 𝓞 K) + ((1 : ℤ) : 𝓞 K) * thetaInt =
        thetaInt - (c : 𝓞 K) by push_cast; ring]
      rw [heq]
      exact htc_memP
    have hQnotsq : Ideal.absNorm Q ≠ p ^ 2 := by
      intro hNQ
      have heq := eq_of_le_of_absNorm_eq hQle (absNorm_span_natCast p) hNQ
        (pow_ne_zero 2 hp.pos.ne')
      refine unit_theta_coeff_not_mem p hp.two_le (-d) 1 (Or.inl rfl) ?_
      rw [show ((-d : ℤ) : 𝓞 K) + ((1 : ℤ) : 𝓞 K) * thetaInt =
        thetaInt - (d : 𝓞 K) by push_cast; ring]
      rw [heq]
      exact htd_memQ
    have hNP : Ideal.absNorm P = p := hnorm P hPle hPnot1 hPnotsq
    have hNQ : Ideal.absNorm Q = p := hnorm Q hQle hQnot1 hQnotsq
    have hPprime : P.IsPrime := by
      apply Ideal.isPrime_of_irreducible_absNorm
      rw [hNP]
      exact hp
    have hQprime : Q.IsPrime := by
      apply Ideal.isPrime_of_irreducible_absNorm
      rw [hNQ]
      exact hp
    have hsne : s ≠ -s := by
      intro h0
      have h2s : (2 : ZMod p) * s = 0 := by linear_combination h0
      have hs0 : s = 0 := by
        rcases mul_eq_zero.mp h2s with h | h
        · exact absurd h h2ne
        · exact h
      have hneg6zero : ((-6 : ℤ) : ZMod p) = 0 := by
        rw [hs, hs0, mul_zero]
      have h6zero : ((6 : ℕ) : ZMod p) = 0 := by
        have h := congrArg Neg.neg hneg6zero
        simpa using h
      have hpdiv6 : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp h6zero
      have hpdiv23 : p ∣ 2 * 3 := by simpa using hpdiv6
      rcases hp.dvd_mul.mp hpdiv23 with hpdiv2 | hpdiv3
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpdiv2)
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpdiv3)
    have hPQne : P ≠ Q := by
      intro heq
      have hcd : ((c - d : ℤ) : ZMod p) ≠ 0 := by
        push_cast
        rw [hct, hdt]
        intro h0
        exact hsne (by linear_combination h0)
      obtain ⟨m, k₃, hk₃⟩ := exists_int_inverse_mod_prime p (c - d) hcd
      have hk₃K : ((m : ℕ) : 𝓞 K) * ((c : 𝓞 K) - (d : 𝓞 K)) - 1 =
          ((p : ℕ) : 𝓞 K) * (k₃ : 𝓞 K) := by
        have h := congrArg (fun n : ℤ => ((n : ℤ) : 𝓞 K)) hk₃
        push_cast at h
        exact h
      have h1 : (1 : 𝓞 K) ∈ P := by
        have htdP : thetaInt - (d : 𝓞 K) ∈ P := by
          rw [heq]
          exact htd_memQ
        have hid : (1 : 𝓞 K) = ((m : ℕ) : 𝓞 K) *
            ((thetaInt - (d : 𝓞 K)) - (thetaInt - (c : 𝓞 K))) -
            (k₃ : 𝓞 K) * ((p : ℕ) : 𝓞 K) := by
          linear_combination -hk₃K
        rw [hid]
        exact Submodule.sub_mem _
          (Ideal.mul_mem_left _ _ (Submodule.sub_mem _ htdP htc_memP))
          (Ideal.mul_mem_left _ _ hp_memP)
      have habs := hNP
      rw [(Ideal.eq_top_iff_one P).mpr h1, Ideal.absNorm_top] at habs
      exact hp2 (by omega)
    have hPQ : Ideal.span {((p : ℕ) : 𝓞 K)} = P * Q := by
      have hle1 : P * Q ≤ Ideal.span {((p : ℕ) : 𝓞 K)} := by
        rw [Ideal.mul_le]
        intro r1 hr1 r2 hr2
        rw [hPdef, Ideal.mem_span_pair] at hr1
        rw [hQdef, Ideal.mem_span_pair] at hr2
        obtain ⟨x1, y1, h1⟩ := hr1
        obtain ⟨x2, y2, h2⟩ := hr2
        rw [Ideal.mem_span_singleton]
        refine ⟨x1 * x2 * ((p : ℕ) : 𝓞 K) +
          x1 * y2 * (thetaInt - (d : 𝓞 K)) +
          y1 * x2 * (thetaInt - (c : 𝓞 K)) +
          y1 * y2 * (-(k₁ : 𝓞 K) * thetaInt + (k₂ : 𝓞 K)), ?_⟩
        rw [← h1, ← h2]
        linear_combination (y1 * y2) * hprod
      have hNPQ : Ideal.absNorm (P * Q) = p ^ 2 := by
        rw [_root_.map_mul, hNP, hNQ]
        ring
      exact (eq_of_le_of_absNorm_eq hle1 hNPQ (absNorm_span_natCast p)
        (pow_ne_zero 2 hp.pos.ne')).symm
    exact ⟨P, Q, hPprime, hQprime, hPQne, hPQ⟩

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
