import XYin.NumberField.FieldExamples.SqrtFive.NormForm

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtFive

private noncomputable def goldenOrderEquivRingOfIntegers : O5 ≃ₐ[ℤ] 𝓞 QSqrtFive :=
  IsIntegralClosure.equiv ℤ O5 QSqrtFive (𝓞 QSqrtFive)

private noncomputable def concreteIntegralBasis : Basis (Fin 2) ℤ (𝓞 QSqrtFive) :=
  sqrtFiveExplicitIntegralBasis.map goldenOrderEquivRingOfIntegers.toLinearEquiv

private theorem concreteIntegralBasis_basis_zero :
    algebraMap (𝓞 QSqrtFive) QSqrtFive (concreteIntegralBasis 0) = 1 := by
  change algebraMap (𝓞 QSqrtFive) QSqrtFive
      (goldenOrderEquivRingOfIntegers (sqrtFiveExplicitIntegralBasis 0)) = 1
  rw [goldenOrderEquivRingOfIntegers, IsIntegralClosure.algebraMap_equiv]
  exact goldenOrderToField_basis_zero

private theorem concreteIntegralBasis_basis_one :
    algebraMap (𝓞 QSqrtFive) QSqrtFive (concreteIntegralBasis 1) = goldenRoot := by
  change algebraMap (𝓞 QSqrtFive) QSqrtFive
      (goldenOrderEquivRingOfIntegers (sqrtFiveExplicitIntegralBasis 1)) = goldenRoot
  rw [goldenOrderEquivRingOfIntegers, IsIntegralClosure.algebraMap_equiv]
  exact goldenOrderToField_basis_one

/-! ## 5. Splitting of primes -/

/-- `√5 = 2φ - 1` as an element of `𝓞 QSqrtFive`. -/
noncomputable def sqrtFiveIntO : 𝓞 QSqrtFive := 2 * goldenIntO - 1

/-- `5` is (totally) ramified: `(5) = (√5)²` as ideals of `𝓞 K`, directly from
`(2φ - 1)² = 5`. It is the unique ramified prime, matching the discriminant `5`. -/
theorem span_five_eq :
    Ideal.span {(5 : 𝓞 QSqrtFive)} = Ideal.span {sqrtFiveIntO} ^ 2 := by
  rw [Ideal.span_singleton_pow,
    show sqrtFiveIntO ^ 2 = (5 : 𝓞 QSqrtFive) from by
      apply Subtype.ext
      change (2 * goldenRoot - 1) ^ 2 = (5 : QSqrtFive)
      exact sqrtFiveRoot_sq]

/-- The prime `(√5)` above `5` has norm `5` (residue degree `f = 1`). -/
theorem absNorm_span_sqrtFiveIntO : Ideal.absNorm (Ideal.span {sqrtFiveIntO}) = 5 := by
  have hsqrt : sqrtFiveIntO = (-1 : ℤ) • (1 : 𝓞 QSqrtFive) + (2 : ℤ) • goldenIntO := by
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

private theorem goldenIntO_sq : goldenIntO ^ 2 = goldenIntO + 1 :=
  Subtype.ext (by push_cast [goldenIntO]; exact goldenRoot_sq)

private theorem eq_of_le_of_absNorm_eq {I J : Ideal (𝓞 QSqrtFive)} (hle : I ≤ J) {n : ℕ}
    (hI : Ideal.absNorm I = n) (hJ : Ideal.absNorm J = n) (hn : n ≠ 0) : I = J := by
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hmul := _root_.map_mul Ideal.absNorm J C
  rw [← hC, hI, hJ] at hmul
  have hC1 : Ideal.absNorm C = 1 :=
    (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn)
      (by rw [mul_one]; exact hmul)).symm
  rw [hC, Ideal.absNorm_eq_one_iff.mp hC1, Ideal.mul_top]

private theorem absNorm_ne_two (P : Ideal (𝓞 QSqrtFive)) : Ideal.absNorm P ≠ 2 := by
  intro hcard
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcard
  haveI : Finite ((𝓞 QSqrtFive) ⧸ P) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype ((𝓞 QSqrtFive) ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card ((𝓞 QSqrtFive) ⧸ P) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let e := ZMod.ringEquivOfPrime ((𝓞 QSqrtFive) ⧸ P) (by norm_num) hcard'
  obtain ⟨t, ht⟩ := e.surjective (Ideal.Quotient.mk P goldenIntO)
  have ht2 : t ^ 2 = t + 1 := by
    apply e.injective
    rw [map_pow, ht, map_add, ht, map_one, ← map_pow (Ideal.Quotient.mk P),
      goldenIntO_sq, map_add, map_one]
  clear ht
  revert t
  decide

private theorem absNorm_ne_three (P : Ideal (𝓞 QSqrtFive)) : Ideal.absNorm P ≠ 3 := by
  intro hcard
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcard
  haveI : Finite ((𝓞 QSqrtFive) ⧸ P) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype ((𝓞 QSqrtFive) ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card ((𝓞 QSqrtFive) ⧸ P) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let e := ZMod.ringEquivOfPrime ((𝓞 QSqrtFive) ⧸ P) (by norm_num) hcard'
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
theorem isPrime_span_two : (Ideal.span {(2 : 𝓞 QSqrtFive)}).IsPrime := by
  have habs4 : Ideal.absNorm (Ideal.span {(2 : 𝓞 QSqrtFive)}) = 4 := by
    have h := intNorm_eq_normForm 2 0
    have h2 : (2 : ℤ) • (1 : 𝓞 QSqrtFive) + (0 : ℤ) • goldenIntO = 2 := by
      simp
    rw [h2] at h
    norm_num at h
    rw [Ideal.absNorm_span_singleton, h]
    rfl
  have htop : Ideal.span {(2 : 𝓞 QSqrtFive)} ≠ ⊤ := by
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
theorem absNorm_span_two : Ideal.absNorm (Ideal.span {(2 : 𝓞 QSqrtFive)}) = 4 := by
  have h := intNorm_eq_normForm 2 0
  have h2 : (2 : ℤ) • (1 : 𝓞 QSqrtFive) + (0 : ℤ) • goldenIntO = 2 := by
    simp
  rw [h2] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- `3` is inert in `ℚ(√5)`: `5` is not a square mod `3`, so `(3)` is itself prime (of norm
`9`). -/
theorem isPrime_span_three : (Ideal.span {(3 : 𝓞 QSqrtFive)}).IsPrime := by
  have habs9 : Ideal.absNorm (Ideal.span {(3 : 𝓞 QSqrtFive)}) = 9 := by
    have h := intNorm_eq_normForm 3 0
    have h3 : (3 : ℤ) • (1 : 𝓞 QSqrtFive) + (0 : ℤ) • goldenIntO = 3 := by
      simp
    rw [h3] at h
    norm_num at h
    rw [Ideal.absNorm_span_singleton, h]
    rfl
  have htop : Ideal.span {(3 : 𝓞 QSqrtFive)} ≠ ⊤ := by
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

/-- The elementary identity `11 = (3 + φ)(4 - φ)` in `𝓞 QSqrtFive`. -/
theorem eleven_eq_mul : (11 : 𝓞 QSqrtFive) = (3 + goldenIntO) * (4 - goldenIntO) := by
  apply Subtype.ext
  change (11 : QSqrtFive) = (3 + goldenRoot) * (4 - goldenRoot)
  rw [show (3 + goldenRoot) * (4 - goldenRoot) = 12 + goldenRoot - goldenRoot ^ 2 by ring]
  rw [goldenRoot_sq]
  ring

/-- `11 ≡ 1 (mod 5)` splits: `11 = (3 + φ)(4 - φ)` and `(11)` is a product of two distinct
primes of norm `11`. -/
theorem span_eleven_eq :
    Ideal.span {(11 : 𝓞 QSqrtFive)} =
      Ideal.span {3 + goldenIntO} * Ideal.span {4 - goldenIntO} := by
  rw [Ideal.span_singleton_mul_span_singleton, ← eleven_eq_mul]

/-- The prime `(3 + φ)` above `11` has norm `11` (residue degree `f = 1`). -/
theorem absNorm_span_three_add_golden :
    Ideal.absNorm (Ideal.span {3 + goldenIntO}) = 11 := by
  have h := intNorm_eq_normForm 3 1
  have h3 : (3 : ℤ) • (1 : 𝓞 QSqrtFive) + (1 : ℤ) • goldenIntO = 3 + goldenIntO := by
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
  have h4 : (4 : ℤ) • (1 : 𝓞 QSqrtFive) + (-1 : ℤ) • goldenIntO = 4 - goldenIntO := by
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

/-- The two principal primes above `11` are distinct. -/
theorem primesAboveEleven_ne :
    Ideal.span ({3 + goldenIntO} : Set (𝓞 QSqrtFive)) ≠ Ideal.span {4 - goldenIntO} := by
  intro h
  have h4 : (4 : 𝓞 QSqrtFive) - goldenIntO ∈
      Ideal.span ({3 + goldenIntO} : Set (𝓞 QSqrtFive)) := by
    rw [h]
    exact Ideal.mem_span_singleton_self _
  have hs : sqrtFiveIntO ∈ Ideal.span ({3 + goldenIntO} : Set (𝓞 QSqrtFive)) := by
    rw [show sqrtFiveIntO = (3 + goldenIntO) - ((4 : 𝓞 QSqrtFive) - goldenIntO) from by
      simp only [sqrtFiveIntO]
      ring]
    exact Ideal.sub_mem _ (Ideal.mem_span_singleton_self _) h4
  have h5 : (5 : 𝓞 QSqrtFive) ∈ Ideal.span ({3 + goldenIntO} : Set (𝓞 QSqrtFive)) := by
    rw [show (5 : 𝓞 QSqrtFive) = sqrtFiveIntO * sqrtFiveIntO from by
      apply Subtype.ext
      change (5 : QSqrtFive) = (2 * goldenRoot - 1) * (2 * goldenRoot - 1)
      rw [← pow_two, sqrtFiveRoot_sq]]
    exact Ideal.mul_mem_right _ _ hs
  have h11 : (11 : 𝓞 QSqrtFive) ∈ Ideal.span ({3 + goldenIntO} : Set (𝓞 QSqrtFive)) := by
    rw [eleven_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h1 : (1 : 𝓞 QSqrtFive) ∈ Ideal.span ({3 + goldenIntO} : Set (𝓞 QSqrtFive)) := by
    rw [show (1 : 𝓞 QSqrtFive) = 11 - 2 * 5 from by norm_num]
    exact Ideal.sub_mem _ h11 (Ideal.mul_mem_left _ _ h5)
  have htop : Ideal.span ({3 + goldenIntO} : Set (𝓞 QSqrtFive)) = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr h1
  have habs := absNorm_span_three_add_golden
  rw [htop, Ideal.absNorm_top] at habs
  norm_num at habs

private theorem absNorm_span_natCast (p : ℕ) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 QSqrtFive)}) = p ^ 2 := by
  have h := intNorm_eq_normForm (p : ℤ) 0
  have hps : ((p : ℤ)) • (1 : 𝓞 QSqrtFive) + (0 : ℤ) • goldenIntO =
      ((p : ℕ) : 𝓞 QSqrtFive) := by simp
  rw [hps] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  simp [Int.natAbs_pow]

private theorem concreteIntegralBasis_zero_eq_one :
    concreteIntegralBasis 0 = (1 : 𝓞 QSqrtFive) := by
  apply Subtype.ext
  exact concreteIntegralBasis_basis_zero

private theorem concreteIntegralBasis_one_eq_goldenIntO :
    concreteIntegralBasis 1 = goldenIntO := by
  apply Subtype.ext
  exact concreteIntegralBasis_basis_one

private theorem li_one_golden : LinearIndependent ℤ ![(1 : 𝓞 QSqrtFive), goldenIntO] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_two] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  have hsum : ∑ i : Fin 2, g i • concreteIntegralBasis i = 0 := by
    rw [Fin.sum_univ_two, concreteIntegralBasis_zero_eq_one,
      concreteIntegralBasis_one_eq_goldenIntO]
    exact hg
  exact Fintype.linearIndependent_iff.mp concreteIntegralBasis.linearIndependent g hsum

private theorem exists_o5_coords (z : 𝓞 QSqrtFive) :
    ∃ A B : ℤ, z = A • (1 : 𝓞 QSqrtFive) + B • goldenIntO := by
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
    ((A : ℤ) : 𝓞 QSqrtFive) + ((B : ℤ) : 𝓞 QSqrtFive) * goldenIntO ∉
      Ideal.span {((p : ℕ) : 𝓞 QSqrtFive)} := by
  intro hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨A', m, hzdec⟩ := exists_o5_coords z
  rw [hzdec] at hz
  have hsum : ∑ i : Fin 2,
      (![A - p * A', B - p * m] i) • (![(1 : 𝓞 QSqrtFive), goldenIntO] i) = 0 := by
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
    (∃ P : Ideal (𝓞 QSqrtFive), P.IsPrime ∧
      Ideal.span {(p : 𝓞 QSqrtFive)} ≤ P ^ 2) ↔ p = 5 := by
  constructor
  · rintro ⟨P, hP, hle2⟩
    haveI : P.IsPrime := hP
    have hple : Ideal.span {((p : ℕ) : 𝓞 QSqrtFive)} ≤ P :=
      hle2.trans (Ideal.pow_le_self (by norm_num))
    have hpmemP : ((p : ℕ) : 𝓞 QSqrtFive) ∈ P := hple (Ideal.mem_span_singleton_self _)
    have hpne : ((p : ℕ) : 𝓞 QSqrtFive) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hPbot : P ≠ ⊥ := by
      intro h
      rw [h] at hpmemP
      exact hpne (Ideal.mem_bot.mp hpmemP)
    have hfin : Module.finrank ℤ (𝓞 QSqrtFive) = 2 := by
      rw [Module.finrank_eq_card_basis concreteIntegralBasis, Fintype.card_fin]
    have habsp : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 QSqrtFive)}) = p ^ 2 := by
      rw [Ideal.absNorm_span_singleton]
      have hcast : ((p : ℕ) : 𝓞 QSqrtFive) =
          algebraMap ℤ (𝓞 QSqrtFive) ((p : ℕ) : ℤ) := by push_cast; rfl
      rw [hcast, Algebra.norm_algebraMap, hfin, Int.natAbs_pow, Int.natAbs_natCast]
    have habsPp2 : Ideal.absNorm P ∣ p ^ 2 :=
      habsp ▸ Ideal.absNorm_dvd_absNorm_of_le hple
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow hp).mp habsPp2
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hkeq
      exact hP.ne_top (Ideal.absNorm_eq_one_iff.mp hkeq)
    have hmap : Ideal.map (algebraMap ℤ (𝓞 QSqrtFive))
        (Ideal.span {((p : ℕ) : ℤ)}) = Ideal.span {((p : ℕ) : 𝓞 QSqrtFive)} := by
      rw [Ideal.map_span, Set.image_singleton]
      norm_num
    have hle2' : Ideal.map (algebraMap ℤ (𝓞 QSqrtFive))
        (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 2 := by
      rw [hmap]
      exact hle2
    have hno3 : ¬ Ideal.map (algebraMap ℤ (𝓞 QSqrtFive))
        (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 3 := by
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
        have hcast2 : algebraMap ℤ (𝓞 QSqrtFive) ((p : ℕ) : ℤ) =
            ((p : ℕ) : 𝓞 QSqrtFive) := by push_cast; rfl
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
    have hPdiff : P ∣ differentIdeal ℤ (𝓞 QSqrtFive) := dvd_differentIdeal_iff.mpr hunram
    have habsP5 : Ideal.absNorm P ∣ 5 := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPdiff)
      rw [NumberField.absNorm_differentIdeal (K := QSqrtFive), numberField_discr_eq] at h
      simpa using h
    have hpdvd : p ∣ 5 := (hkeq ▸ dvd_pow_self p hk0).trans habsP5
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpdvd
  · rintro rfl
    refine ⟨Ideal.span {sqrtFiveIntO}, isPrime_span_sqrtFiveIntO, ?_⟩
    have hcast : ((5 : ℕ) : 𝓞 QSqrtFive) = (5 : 𝓞 QSqrtFive) := by norm_num
    rw [hcast, span_five_eq]

/-- The quadratic splitting law for `ℚ(√5)`: a rational prime `p ≠ 5` splits into two
distinct primes iff `p ≡ ±1 (mod 5)` (i.e. iff `5` is a quadratic residue mod `p`, by
quadratic reciprocity), and is inert otherwise. -/
theorem splits_iff_pm_one_mod_five (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    (∃ P Q : Ideal (𝓞 QSqrtFive), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 QSqrtFive)} = P * Q) ↔ p % 5 = 1 ∨ p % 5 = 4 := by
  have hsq1 : IsSquare ((1 : ℕ) : ZMod 5) := by decide
  have hsq4 : IsSquare ((4 : ℕ) : ZMod 5) := by decide
  have hnsq2 : ¬ IsSquare ((2 : ℕ) : ZMod 5) := by decide
  have hnsq3 : ¬ IsSquare ((3 : ℕ) : ZMod 5) := by decide
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
          Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2)
            (by rw [mul_one]; exact hmul)
        exact hQ1 hQ1'
    have hcard : Nat.card ((𝓞 QSqrtFive) ⧸ P) = p := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hNP
      exact hNP
    haveI : Finite ((𝓞 QSqrtFive) ⧸ P) := Nat.finite_of_card_ne_zero
      (by rw [hcard]; exact hp.pos.ne')
    haveI : Fintype ((𝓞 QSqrtFive) ⧸ P) := Fintype.ofFinite _
    have hcard' : Fintype.card ((𝓞 QSqrtFive) ⧸ P) = p := by
      rw [← Nat.card_eq_fintype_card]
      exact hcard
    let e := ZMod.ringEquivOfPrime ((𝓞 QSqrtFive) ⧸ P) hp hcard'
    obtain ⟨t, ht⟩ := e.surjective (Ideal.Quotient.mk P goldenIntO)
    have ht2 : t ^ 2 = t + 1 := by
      apply e.injective
      rw [map_pow, ht, map_add, ht, map_one, ← map_pow (Ideal.Quotient.mk P),
        goldenIntO_sq, map_add, map_one]
    by_cases hp2 : p = 2
    · exfalso
      subst hp2
      clear ht
      revert t
      decide
    have hsq5 : IsSquare ((5 : ℕ) : ZMod p) := by
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
  · intro hmod
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
    have h2t : (2 : ZMod p) * t = 1 + s := by
      rw [htdef, mul_comm, div_mul_cancel₀ _ h2ne]
    have ht2 : t ^ 2 = t + 1 := by
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
    have hk₁K : (1 : 𝓞 QSqrtFive) - (c : 𝓞 QSqrtFive) - (c' : 𝓞 QSqrtFive) =
        ((p : ℕ) : 𝓞 QSqrtFive) * (k₁ : 𝓞 QSqrtFive) := by
      have h := congrArg (fun n : ℤ => ((n : ℤ) : 𝓞 QSqrtFive)) hk₁
      push_cast at h
      exact h
    have hk₂K : (1 : 𝓞 QSqrtFive) + (c : 𝓞 QSqrtFive) * (c' : 𝓞 QSqrtFive) =
        ((p : ℕ) : 𝓞 QSqrtFive) * (k₂ : 𝓞 QSqrtFive) := by
      have h := congrArg (fun n : ℤ => ((n : ℤ) : 𝓞 QSqrtFive)) hk₂
      push_cast at h
      exact h
    have hprod : (goldenIntO - (c : 𝓞 QSqrtFive)) * (goldenIntO - (c' : 𝓞 QSqrtFive)) =
        ((p : ℕ) : 𝓞 QSqrtFive) *
          ((k₁ : 𝓞 QSqrtFive) * goldenIntO + (k₂ : 𝓞 QSqrtFive)) := by
      linear_combination goldenIntO_sq + goldenIntO * hk₁K + hk₂K
    set P := Ideal.span {((p : ℕ) : 𝓞 QSqrtFive), goldenIntO - (c : 𝓞 QSqrtFive)}
      with hPdef
    set Q := Ideal.span {((p : ℕ) : 𝓞 QSqrtFive), goldenIntO - (c' : 𝓞 QSqrtFive)}
      with hQdef
    have hp_memP : ((p : ℕ) : 𝓞 QSqrtFive) ∈ P := Ideal.subset_span (Set.mem_insert _ _)
    have hgc_memP : goldenIntO - (c : 𝓞 QSqrtFive) ∈ P :=
      Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have hp_memQ : ((p : ℕ) : 𝓞 QSqrtFive) ∈ Q := Ideal.subset_span (Set.mem_insert _ _)
    have hgc'_memQ : goldenIntO - (c' : 𝓞 QSqrtFive) ∈ Q :=
      Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have hPle : Ideal.span {((p : ℕ) : 𝓞 QSqrtFive)} ≤ P :=
      (Ideal.span_singleton_le_iff_mem _).mpr hp_memP
    have hQle : Ideal.span {((p : ℕ) : 𝓞 QSqrtFive)} ≤ Q :=
      (Ideal.span_singleton_le_iff_mem _).mpr hp_memQ
    have hnorm : ∀ (I : Ideal (𝓞 QSqrtFive)),
        Ideal.span {((p : ℕ) : 𝓞 QSqrtFive)} ≤ I →
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
      have h1 : (1 : 𝓞 QSqrtFive) ∈ P := htop ▸ Submodule.mem_top
      rw [hPdef, Ideal.mem_span_pair] at h1
      obtain ⟨α, β, hαβ⟩ := h1
      have hgc' : goldenIntO - (c' : 𝓞 QSqrtFive) ∈
          Ideal.span {((p : ℕ) : 𝓞 QSqrtFive)} := by
        rw [Ideal.mem_span_singleton]
        refine ⟨α * (goldenIntO - (c' : 𝓞 QSqrtFive)) +
          β * ((k₁ : 𝓞 QSqrtFive) * goldenIntO + (k₂ : 𝓞 QSqrtFive)), ?_⟩
        calc goldenIntO - (c' : 𝓞 QSqrtFive)
            = (α * ((p : ℕ) : 𝓞 QSqrtFive) +
                β * (goldenIntO - (c : 𝓞 QSqrtFive))) *
              (goldenIntO - (c' : 𝓞 QSqrtFive)) := by
              rw [hαβ, one_mul]
          _ = ((p : ℕ) : 𝓞 QSqrtFive) *
              (α * (goldenIntO - (c' : 𝓞 QSqrtFive)) +
                β * ((k₁ : 𝓞 QSqrtFive) * goldenIntO + (k₂ : 𝓞 QSqrtFive))) := by
              linear_combination β * hprod
      refine unit_golden_coeff_not_mem p hp.two_le (-c') 1 (Or.inl rfl) ?_
      rw [show ((-c' : ℤ) : 𝓞 QSqrtFive) +
          ((1 : ℤ) : 𝓞 QSqrtFive) * goldenIntO =
        goldenIntO - (c' : 𝓞 QSqrtFive) by
        push_cast
        ring]
      exact hgc'
    have hQnot1 : Ideal.absNorm Q ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      intro htop
      have h1 : (1 : 𝓞 QSqrtFive) ∈ Q := htop ▸ Submodule.mem_top
      rw [hQdef, Ideal.mem_span_pair] at h1
      obtain ⟨α, β, hαβ⟩ := h1
      have hgc : goldenIntO - (c : 𝓞 QSqrtFive) ∈
          Ideal.span {((p : ℕ) : 𝓞 QSqrtFive)} := by
        rw [Ideal.mem_span_singleton]
        refine ⟨α * (goldenIntO - (c : 𝓞 QSqrtFive)) +
          β * ((k₁ : 𝓞 QSqrtFive) * goldenIntO + (k₂ : 𝓞 QSqrtFive)), ?_⟩
        calc goldenIntO - (c : 𝓞 QSqrtFive)
            = (α * ((p : ℕ) : 𝓞 QSqrtFive) +
                β * (goldenIntO - (c' : 𝓞 QSqrtFive))) *
              (goldenIntO - (c : 𝓞 QSqrtFive)) := by
              rw [hαβ, one_mul]
          _ = ((p : ℕ) : 𝓞 QSqrtFive) *
              (α * (goldenIntO - (c : 𝓞 QSqrtFive)) +
                β * ((k₁ : 𝓞 QSqrtFive) * goldenIntO + (k₂ : 𝓞 QSqrtFive))) := by
              linear_combination β * hprod
      refine unit_golden_coeff_not_mem p hp.two_le (-c) 1 (Or.inl rfl) ?_
      rw [show ((-c : ℤ) : 𝓞 QSqrtFive) +
          ((1 : ℤ) : 𝓞 QSqrtFive) * goldenIntO =
        goldenIntO - (c : 𝓞 QSqrtFive) by
        push_cast
        ring]
      exact hgc
    have hPnotsq : Ideal.absNorm P ≠ p ^ 2 := by
      intro hNP
      have heq := eq_of_le_of_absNorm_eq hPle (absNorm_span_natCast p) hNP
        (pow_ne_zero 2 hp.pos.ne')
      refine unit_golden_coeff_not_mem p hp.two_le (-c) 1 (Or.inl rfl) ?_
      rw [show ((-c : ℤ) : 𝓞 QSqrtFive) +
          ((1 : ℤ) : 𝓞 QSqrtFive) * goldenIntO =
        goldenIntO - (c : 𝓞 QSqrtFive) by
        push_cast
        ring]
      rw [heq]
      exact hgc_memP
    have hQnotsq : Ideal.absNorm Q ≠ p ^ 2 := by
      intro hNQ
      have heq := eq_of_le_of_absNorm_eq hQle (absNorm_span_natCast p) hNQ
        (pow_ne_zero 2 hp.pos.ne')
      refine unit_golden_coeff_not_mem p hp.two_le (-c') 1 (Or.inl rfl) ?_
      rw [show ((-c' : ℤ) : 𝓞 QSqrtFive) +
          ((1 : ℤ) : 𝓞 QSqrtFive) * goldenIntO =
        goldenIntO - (c' : 𝓞 QSqrtFive) by
        push_cast
        ring]
      rw [heq]
      exact hgc'_memQ
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
    have htne : t ≠ 1 - t := by
      intro h0
      have hs0 : s = 0 := by
        have h2t1 : (2 : ZMod p) * t = 1 := by linear_combination h0
        have : (1 : ZMod p) + s = 1 := by rw [← h2t, h2t1]
        linear_combination this
      have h50 : ((5 : ℕ) : ZMod p) = 0 := by
        rw [hs, hs0, mul_zero]
      exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
        ((ZMod.natCast_eq_zero_iff 5 p).mp h50))
    have hPQne : P ≠ Q := by
      intro heq
      have hcc' : ((c - c' : ℤ) : ZMod p) ≠ 0 := by
        push_cast
        rw [hct, hc't]
        intro h0
        exact htne (by linear_combination h0)
      obtain ⟨u, hu⟩ := isUnit_iff_ne_zero.mpr hcc'
      set w : ZMod p := ((u⁻¹ : (ZMod p)ˣ) : ZMod p) with hwdef
      have hw : w * ((c - c' : ℤ) : ZMod p) = 1 := by
        rw [hwdef, ← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hlift : (p : ℤ) ∣ ((w.val : ℤ) * (c - c') - 1) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [show ((w.val : ℕ) : ZMod p) = w from ZMod.natCast_rightInverse w]
        push_cast at hw
        linear_combination hw
      obtain ⟨k₃, hk₃⟩ := hlift
      have hk₃K : ((w.val : ℕ) : 𝓞 QSqrtFive) *
            ((c : 𝓞 QSqrtFive) - (c' : 𝓞 QSqrtFive)) - 1 =
          ((p : ℕ) : 𝓞 QSqrtFive) * (k₃ : 𝓞 QSqrtFive) := by
        have h := congrArg (fun n : ℤ => ((n : ℤ) : 𝓞 QSqrtFive)) hk₃
        push_cast at h
        exact h
      have h1 : (1 : 𝓞 QSqrtFive) ∈ P := by
        have hgc'P : goldenIntO - (c' : 𝓞 QSqrtFive) ∈ P := by
          rw [heq]
          exact hgc'_memQ
        have hid : (1 : 𝓞 QSqrtFive) = ((w.val : ℕ) : 𝓞 QSqrtFive) *
            ((goldenIntO - (c' : 𝓞 QSqrtFive)) - (goldenIntO - (c : 𝓞 QSqrtFive))) -
            (k₃ : 𝓞 QSqrtFive) * ((p : ℕ) : 𝓞 QSqrtFive) := by
          linear_combination -hk₃K
        rw [hid]
        exact Submodule.sub_mem _
          (Ideal.mul_mem_left _ _ (Submodule.sub_mem _ hgc'P hgc_memP))
          (Ideal.mul_mem_left _ _ hp_memP)
      have habs := hNP
      rw [(Ideal.eq_top_iff_one P).mpr h1, Ideal.absNorm_top] at habs
      exact hp2 (by omega)
    have hPQ : Ideal.span {((p : ℕ) : 𝓞 QSqrtFive)} = P * Q := by
      have hle1 : P * Q ≤ Ideal.span {((p : ℕ) : 𝓞 QSqrtFive)} := by
        rw [Ideal.mul_le]
        intro r1 hr1 r2 hr2
        rw [hPdef, Ideal.mem_span_pair] at hr1
        rw [hQdef, Ideal.mem_span_pair] at hr2
        obtain ⟨x1, y1, h1⟩ := hr1
        obtain ⟨x2, y2, h2⟩ := hr2
        rw [Ideal.mem_span_singleton]
        refine ⟨x1 * x2 * ((p : ℕ) : 𝓞 QSqrtFive) +
          x1 * y2 * (goldenIntO - (c' : 𝓞 QSqrtFive)) +
          y1 * x2 * (goldenIntO - (c : 𝓞 QSqrtFive)) +
          y1 * y2 * ((k₁ : 𝓞 QSqrtFive) * goldenIntO + (k₂ : 𝓞 QSqrtFive)), ?_⟩
        rw [← h1, ← h2]
        linear_combination (y1 * y2) * hprod
      have hNPQ : Ideal.absNorm (P * Q) = p ^ 2 := by
        rw [_root_.map_mul, hNP, hNQ]
        ring
      exact (eq_of_le_of_absNorm_eq hle1 hNPQ (absNorm_span_natCast p)
        (pow_ne_zero 2 hp.pos.ne')).symm
    exact ⟨P, Q, hPprime, hQprime, hPQne, hPQ⟩


end NumberField.SqrtFive
