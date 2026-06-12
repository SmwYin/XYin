import XYin.NumberField.FieldExamples.CubeRootThree.NormForm

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CubeRootThree

/-! ## 5. Splitting of primes -/

/-- `3` is totally ramified: `(3) = (θ)³` as ideals of `𝓞 K`, directly from `θ³ = 3`.
Together with `isPrime_span_theta` this gives ramification index `e = 3`. -/
theorem span_three_eq : Ideal.span {(3 : 𝓞 K)} = Ideal.span {thetaInt} ^ 3 := by
  rw [Ideal.span_singleton_pow, thetaInt_cube]

/-- The prime `(θ)` above `3` has norm `3` (residue degree `f = 1`). -/
theorem absNorm_span_theta : Ideal.absNorm (Ideal.span {thetaInt}) = 3 := by
  have h := intNorm_eq_normForm 0 1 0
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- `(θ)` is a prime ideal — the unique prime of `𝓞 K` above `3`. -/
theorem isPrime_span_theta : (Ideal.span {thetaInt}).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_span_theta]
  exact (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)

/-- Any prime of `𝓞 K` containing `3` equals `(θ)`: the prime above `3` is unique. -/
theorem eq_span_theta_of_three_mem (P : Ideal (𝓞 K)) (hP : P.IsPrime) (h3 : (3 : 𝓞 K) ∈ P) :
    P = Ideal.span {thetaInt} := by
  have hθ : thetaInt ∈ P := hP.mem_of_pow_mem 3 (by rw [thetaInt_cube]; exact h3)
  have hle : Ideal.span {thetaInt} ≤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hθ
  have hbot : Ideal.span {thetaInt} ≠ ⊥ := by
    intro h
    have h3' := absNorm_span_theta
    rw [h, Ideal.absNorm_bot] at h3'
    norm_num at h3'
  exact ((isPrime_span_theta.isMaximal hbot).eq_of_le hP.ne_top hle).symm

/-- The elementary identity `2 = (θ - 1)(θ² + θ + 1)` in `ℤ[θ]`, from `θ³ = 3`. -/
theorem two_eq_mul : (2 : 𝓞 K) = (thetaInt - 1) * (thetaInt ^ 2 + thetaInt + 1) := by
  linear_combination -thetaInt_cube

/-- `2` splits as a product of two primes of residue degrees `1` and `2`, matching the
factorisation `X³ - 3 ≡ (X + 1)(X² + X + 1) (mod 2)`. -/
theorem span_two_eq :
    Ideal.span {(2 : 𝓞 K)} =
      Ideal.span {thetaInt - 1} * Ideal.span {thetaInt ^ 2 + thetaInt + 1} := by
  rw [Ideal.span_singleton_mul_span_singleton, ← two_eq_mul]

/-- The prime `(θ - 1)` above `2` has norm `2` (residue degree `f = 1`). -/
theorem absNorm_span_theta_sub_one : Ideal.absNorm (Ideal.span {thetaInt - 1}) = 2 := by
  have h := intNorm_eq_normForm (-1) 1 0
  have he : (-1 : ℤ) • (1 : 𝓞 K) + (1 : ℤ) • thetaInt + (0 : ℤ) • thetaInt ^ 2 =
      thetaInt - 1 := by ring
  rw [he] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- `(θ - 1)` is a prime ideal — the degree-`1` prime of `𝓞 K` above `2`. -/
theorem isPrime_span_theta_sub_one : (Ideal.span {thetaInt - 1}).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_span_theta_sub_one]
  exact (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)

/-- The prime `(θ² + θ + 1)` above `2` has norm `4` (residue degree `f = 2`). -/
theorem absNorm_span_theta_sq_add_theta_add_one :
    Ideal.absNorm (Ideal.span {thetaInt ^ 2 + thetaInt + 1}) = 4 := by
  have h := intNorm_eq_normForm 1 1 1
  have he : (1 : ℤ) • (1 : 𝓞 K) + (1 : ℤ) • thetaInt + (1 : ℤ) • thetaInt ^ 2 =
      thetaInt ^ 2 + thetaInt + 1 := by ring
  rw [he] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- No prime of norm `2` contains `θ² + θ + 1`: in the residue field with two elements,
`t² + t + 1` has no root. This is the formal content of "`X² + X + 1` is irreducible mod `2`". -/
theorem absNorm_ne_two_of_quadFactor_mem (P : Ideal (𝓞 K)) (hP : P.IsMaximal)
    (hmem : thetaInt ^ 2 + thetaInt + 1 ∈ P) : Ideal.absNorm P ≠ 2 := by
  intro hcard
  haveI : P.IsMaximal := hP
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcard
  haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h01 : ∀ x : (𝓞 K) ⧸ P, x = 0 ∨ x = 1 := by
    intro x
    by_contra hx
    push Not at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hinj : Function.Injective (![0, 1, x] : Fin 3 → (𝓞 K) ⧸ P) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have hle := Nat.card_le_card_of_injective _ hinj
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, hcard] at hle
    omega
  have h2zero : (1 : (𝓞 K) ⧸ P) + 1 = 0 := by
    rcases h01 (1 + 1) with h | h
    · exact h
    · have h10 : (1 : (𝓞 K) ⧸ P) = 0 := by
        have := add_right_cancel (b := (1 : (𝓞 K) ⧸ P)) (a := (1 : (𝓞 K) ⧸ P)) (c := 0)
        rw [zero_add] at this
        exact this h
      exact absurd h10 one_ne_zero
  set t := Ideal.Quotient.mk P thetaInt with ht
  have htroot : t ^ 2 + t + 1 = 0 := by
    rw [ht, ← map_pow, ← map_add, ← map_one (Ideal.Quotient.mk P), ← map_add]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rcases h01 t with h | h
  · rw [h] at htroot
    simp at htroot
  · rw [h, one_pow] at htroot
    rw [h2zero, zero_add] at htroot
    exact one_ne_zero htroot

/-- Any prime of `𝓞 K` containing `θ² + θ + 1` equals `(θ² + θ + 1)`: its norm divides `4`,
cannot be `1` or `2`, hence is `4`, forcing equality. -/
theorem eq_span_quadFactor_of_mem (P : Ideal (𝓞 K)) (hP : P.IsPrime)
    (hmem : thetaInt ^ 2 + thetaInt + 1 ∈ P) :
    P = Ideal.span {thetaInt ^ 2 + thetaInt + 1} := by
  set Q : Ideal (𝓞 K) := Ideal.span {thetaInt ^ 2 + thetaInt + 1} with hQ
  have habsQ : Ideal.absNorm Q = 4 := absNorm_span_theta_sq_add_theta_add_one
  have hle : Q ≤ P := by rw [hQ, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
  have hQbot : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at habsQ
    norm_num at habsQ
  have hPbot : P ≠ ⊥ := fun h => hQbot (le_bot_iff.mp (h ▸ hle))
  have hPmax : P.IsMaximal := hP.isMaximal hPbot
  have hdvd : Ideal.absNorm P ∣ 4 := habsQ ▸ Ideal.absNorm_dvd_absNorm_of_le hle
  have hne1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hPmax.ne_top
  have hne2 : Ideal.absNorm P ≠ 2 := absNorm_ne_two_of_quadFactor_mem P hPmax hmem
  have h4 : Ideal.absNorm P = 4 := by
    have hle4 : Ideal.absNorm P ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    set n := Ideal.absNorm P with hn
    clear_value n
    interval_cases n <;> omega
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have habs : Ideal.absNorm Q = Ideal.absNorm P * Ideal.absNorm C := by
    rw [hC, map_mul]
  rw [habsQ, h4] at habs
  have hCtop : C = ⊤ := Ideal.absNorm_eq_one_iff.mp (by omega)
  rw [hC, hCtop, Ideal.mul_top]

/-- `(θ² + θ + 1)` is a prime ideal — the degree-`2` prime of `𝓞 K` above `2`. -/
theorem isPrime_span_theta_sq_add_theta_add_one :
    (Ideal.span {thetaInt ^ 2 + thetaInt + 1}).IsPrime := by
  have hQtop : Ideal.span {thetaInt ^ 2 + thetaInt + 1} ≠ ⊤ := by
    intro h
    have h4 := absNorm_span_theta_sq_add_theta_add_one
    rw [h, Ideal.absNorm_top] at h4
    norm_num at h4
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hQtop
  have hmem : thetaInt ^ 2 + thetaInt + 1 ∈ P := hle (Ideal.mem_span_singleton_self _)
  rw [← eq_span_quadFactor_of_mem P hPmax.isPrime hmem]
  exact hPmax.isPrime

/-- Any prime of `𝓞 K` containing `2` equals `(θ - 1)` or `(θ² + θ + 1)`: the two primes
above `2` are the only ones, and both are principal. -/
theorem eq_of_two_mem (P : Ideal (𝓞 K)) (hP : P.IsPrime) (h2 : (2 : 𝓞 K) ∈ P) :
    P = Ideal.span {thetaInt - 1} ∨ P = Ideal.span {thetaInt ^ 2 + thetaInt + 1} := by
  have hprod : (thetaInt - 1) * (thetaInt ^ 2 + thetaInt + 1) ∈ P := by
    rw [← two_eq_mul]; exact h2
  rcases hP.mem_or_mem hprod with h | h
  · left
    have hle : Ideal.span {thetaInt - 1} ≤ P := by
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact h
    have hbot : Ideal.span {thetaInt - 1} ≠ ⊥ := by
      intro hb
      have habs := absNorm_span_theta_sub_one
      rw [hb, Ideal.absNorm_bot] at habs
      norm_num at habs
    exact ((isPrime_span_theta_sub_one.isMaximal hbot).eq_of_le hP.ne_top hle).symm
  · right
    exact eq_span_quadFactor_of_mem P hP h

/-- The prime `(7)` is inert with norm `7³` (residue degree `f = 3`). -/
theorem absNorm_span_seven : Ideal.absNorm (Ideal.span {(7 : 𝓞 K)}) = 343 := by
  have h := intNorm_eq_normForm 7 0 0
  have he : (7 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt + (0 : ℤ) • thetaInt ^ 2 =
      (7 : 𝓞 K) := by ring
  rw [he] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- There is no prime of `𝓞 K` with residue field `𝔽₇`: `3` is not a cube mod `7`. -/
theorem absNorm_ne_seven (P : Ideal (𝓞 K)) (_hP : P.IsMaximal) : Ideal.absNorm P ≠ 7 := by
  intro hcard
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcard
  haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card ((𝓞 K) ⧸ P) = 7 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) (by norm_num) hcard'
  obtain ⟨s, hs⟩ := e.surjective (Ideal.Quotient.mk P thetaInt)
  have hs3 : s ^ 3 = (3 : ZMod 7) := by
    apply e.injective
    rw [map_pow, hs, map_ofNat, ← map_pow (Ideal.Quotient.mk P), thetaInt_cube, map_ofNat]
  clear hs
  revert s
  decide

/-- `7` is inert in `ℚ(∛3)`: `X³ - 3` is irreducible mod `7`, since `3` is not a cube mod `7`.
Every maximal ideal containing `(7)` has norm dividing `7³` but not `1`, `7` (no norm-`7`
prime exists) or `49` (a norm-`49` factor would force a norm-`7` prime), hence norm `7³` and
equals `(7)`. -/
theorem isPrime_span_seven : (Ideal.span {(7 : 𝓞 K)}).IsPrime := by
  set I : Ideal (𝓞 K) := Ideal.span {(7 : 𝓞 K)} with hI
  have habs : Ideal.absNorm I = 343 := absNorm_span_seven
  have htop : I ≠ ⊤ := by intro h; rw [h, Ideal.absNorm_top] at habs; norm_num at habs
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal I htop
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have habsP : Ideal.absNorm P ∣ 343 := habs ▸ Ideal.absNorm_dvd_absNorm_of_le hle
  have hP1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hPmax.ne_top
  have hP7 : Ideal.absNorm P ≠ 7 := absNorm_ne_seven P hPmax
  have hP49 : Ideal.absNorm P ≠ 49 := by
    intro h49
    have habsC : Ideal.absNorm C = 7 := by
      have h := habs
      rw [hC, map_mul, h49] at h
      omega
    have hCtop : C ≠ ⊤ := by
      intro h; rw [h, Ideal.absNorm_top] at habsC; norm_num at habsC
    obtain ⟨P', hP'max, hle'⟩ := Ideal.exists_le_maximal C hCtop
    have habsP' : Ideal.absNorm P' ∣ 7 := habsC ▸ Ideal.absNorm_dvd_absNorm_of_le hle'
    rcases (Nat.dvd_prime (by norm_num)).mp habsP' with h | h
    · rw [Ideal.absNorm_eq_one_iff] at h
      exact hP'max.ne_top h
    · exact absNorm_ne_seven P' hP'max h
  have hP343 : Ideal.absNorm P = 343 := by
    have h343 : (343 : ℕ) = 7 ^ 3 := by norm_num
    rw [h343] at habsP
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp habsP
    interval_cases k
    · rw [pow_zero] at hkeq; omega
    · rw [pow_one] at hkeq; omega
    · rw [show (7 : ℕ) ^ 2 = 49 by norm_num] at hkeq; omega
    · rw [show (7 : ℕ) ^ 3 = 343 by norm_num] at hkeq; omega
  have habsC1 : Ideal.absNorm C = 1 := by
    have h := habs
    rw [hC, map_mul, hP343] at h
    omega
  have hCtop : C = ⊤ := Ideal.absNorm_eq_one_iff.mp habsC1
  have hIP : I = P := by rw [hC, hCtop, Ideal.mul_top]
  rw [hIP]
  exact hPmax.isPrime

/-- The prime `(61, θ - r)` of `𝓞 K` above `61`, for `r` a cube root of `3` mod `61`. The
roots of `X³ - 3` mod `61` are `4`, `5` and `52`. -/
def primeAbove61 (r : ℤ) : Ideal (𝓞 K) := Ideal.span {(61 : 𝓞 K), thetaInt - (r : 𝓞 K)}

/-- The element `θ - 4` has norm `-61`. -/
theorem absNorm_span_theta_sub_four : Ideal.absNorm (Ideal.span {thetaInt - 4}) = 61 := by
  have h := intNorm_eq_normForm (-4) 1 0
  have he : (-4 : ℤ) • (1 : 𝓞 K) + (1 : ℤ) • thetaInt + (0 : ℤ) • thetaInt ^ 2 =
      thetaInt - 4 := by ring
  rw [he] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- The element `1 + 2θ + 2θ²` has norm `61`. -/
theorem absNorm_span_gen_five :
    Ideal.absNorm (Ideal.span {1 + 2 * thetaInt + 2 * thetaInt ^ 2}) = 61 := by
  have h := intNorm_eq_normForm 1 2 2
  have he : (1 : ℤ) • (1 : 𝓞 K) + (2 : ℤ) • thetaInt + (2 : ℤ) • thetaInt ^ 2 =
      1 + 2 * thetaInt + 2 * thetaInt ^ 2 := by ring
  rw [he] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- The element `2 - 2θ - θ²` has norm `-61`. -/
theorem absNorm_span_gen_fiftytwo :
    Ideal.absNorm (Ideal.span {2 - 2 * thetaInt - thetaInt ^ 2}) = 61 := by
  have h := intNorm_eq_normForm 2 (-2) (-1)
  have he : (2 : ℤ) • (1 : 𝓞 K) + (-2 : ℤ) • thetaInt + (-1 : ℤ) • thetaInt ^ 2 =
      2 - 2 * thetaInt - thetaInt ^ 2 := by ring
  rw [he] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- `(61, θ - 4)` is principal with generator `θ - 4` (its norm `-61` puts `61` in `(θ - 4)`). -/
theorem primeAbove61_four_eq : primeAbove61 4 = Ideal.span {thetaInt - 4} := by
  have hcast : ((4 : ℤ) : 𝓞 K) = (4 : 𝓞 K) := by norm_num
  rw [primeAbove61, hcast]
  apply le_antisymm
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, Ideal.mem_span_singleton_self _⟩
    have hmem := Ideal.absNorm_mem (Ideal.span {thetaInt - 4})
    rw [absNorm_span_theta_sub_four] at hmem
    exact_mod_cast hmem
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

/-- `(61, θ - 5)` is principal with generator `1 + 2θ + 2θ²`: one has
`θ - 5 = (1 + 2θ + 2θ²)(1 - θ)` and `1 + 2θ + 2θ² = 61 + (2θ + 12)(θ - 5)`. -/
theorem primeAbove61_five_eq :
    primeAbove61 5 = Ideal.span {1 + 2 * thetaInt + 2 * thetaInt ^ 2} := by
  have hcast : ((5 : ℤ) : 𝓞 K) = (5 : 𝓞 K) := by norm_num
  rw [primeAbove61, hcast]
  apply le_antisymm
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · have hmem := Ideal.absNorm_mem (Ideal.span {1 + 2 * thetaInt + 2 * thetaInt ^ 2})
      rw [absNorm_span_gen_five] at hmem
      exact_mod_cast hmem
    · rw [SetLike.mem_coe, Ideal.mem_span_singleton]
      exact ⟨1 - thetaInt, by linear_combination (2 : 𝓞 K) * thetaInt_cube⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_pair]
    exact ⟨1, 2 * thetaInt + 12, by ring⟩

/-- `(61, θ - 52)` is principal with generator `2 - 2θ - θ²`: one has
`θ - 52 = (2 - 2θ - θ²)(-2 + 6θ + 5θ²)` and `2 - 2θ - θ² = -46·61 - (θ + 54)(θ - 52)`. -/
theorem primeAbove61_fiftytwo_eq :
    primeAbove61 52 = Ideal.span {2 - 2 * thetaInt - thetaInt ^ 2} := by
  have hcast : ((52 : ℤ) : 𝓞 K) = (52 : 𝓞 K) := by norm_num
  rw [primeAbove61, hcast]
  apply le_antisymm
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · have hmem := Ideal.absNorm_mem (Ideal.span {2 - 2 * thetaInt - thetaInt ^ 2})
      rw [absNorm_span_gen_fiftytwo] at hmem
      exact_mod_cast hmem
    · rw [SetLike.mem_coe, Ideal.mem_span_singleton]
      exact ⟨-2 + 6 * thetaInt + 5 * thetaInt ^ 2,
        by linear_combination (5 * thetaInt + 16) * thetaInt_cube⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_pair]
    exact ⟨-46, -(thetaInt + 54), by ring⟩

/-- `61` splits completely: `61 ≡ 1 (mod 3)` and `3 ≡ 4³ (mod 61)` is a cubic residue, so
`X³ - 3 ≡ (X - 4)(X - 5)(X - 52) (mod 61)` and `(61)` is a product of three primes of norm
`61`. This is the generic split case of the cubic splitting law. -/
theorem span_sixtyOne_eq :
    Ideal.span {(61 : 𝓞 K)} = primeAbove61 4 * primeAbove61 5 * primeAbove61 52 := by
  rw [primeAbove61_four_eq, primeAbove61_five_eq, primeAbove61_fiftytwo_eq,
    Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
  have hprod : (61 : 𝓞 K) = (thetaInt - 4) * (1 + 2 * thetaInt + 2 * thetaInt ^ 2) *
      (2 - 2 * thetaInt - thetaInt ^ 2) := by
    linear_combination (2 * thetaInt ^ 2 - 2 * thetaInt - 23) * thetaInt_cube
  rw [← hprod]

/-- Each ideal `(61, θ - r)` for `r ∈ {4, 5, 52}` is prime. -/
theorem isPrime_primeAbove61 (r : ℤ) (hr : r = 4 ∨ r = 5 ∨ r = 52) :
    (primeAbove61 r).IsPrime := by
  have h61 : Irreducible (61 : ℕ) := (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)
  rcases hr with rfl | rfl | rfl
  · rw [primeAbove61_four_eq]
    exact Ideal.isPrime_of_irreducible_absNorm (absNorm_span_theta_sub_four ▸ h61)
  · rw [primeAbove61_five_eq]
    exact Ideal.isPrime_of_irreducible_absNorm (absNorm_span_gen_five ▸ h61)
  · rw [primeAbove61_fiftytwo_eq]
    exact Ideal.isPrime_of_irreducible_absNorm (absNorm_span_gen_fiftytwo ▸ h61)

/-- The three primes above `61` are pairwise distinct, so `61` is unramified and splits
completely. -/
theorem primeAbove61_pairwise_ne :
    primeAbove61 4 ≠ primeAbove61 5 ∧ primeAbove61 4 ≠ primeAbove61 52 ∧
      primeAbove61 5 ≠ primeAbove61 52 := by
  have hmem : ∀ r : ℤ, thetaInt - (r : 𝓞 K) ∈ primeAbove61 r := fun r =>
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have h61 : ∀ r : ℤ, (61 : 𝓞 K) ∈ primeAbove61 r := fun r =>
    Ideal.subset_span (Set.mem_insert _ _)
  have key : ∀ r s : ℤ, r = 4 ∨ r = 5 ∨ r = 52 → primeAbove61 r = primeAbove61 s →
      (1 : 𝓞 K) ∈ primeAbove61 r → False := fun r s hr h h1 =>
    (isPrime_primeAbove61 r hr).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · refine key 4 5 (Or.inl rfl) h ?_
    have hb : thetaInt - ((5 : ℤ) : 𝓞 K) ∈ primeAbove61 4 := by rw [h]; exact hmem 5
    have hsub := Ideal.sub_mem _ (hmem 4) hb
    have heq : (thetaInt - ((4 : ℤ) : 𝓞 K)) - (thetaInt - ((5 : ℤ) : 𝓞 K)) = (1 : 𝓞 K) := by
      push_cast; ring
    rwa [heq] at hsub
  · refine key 4 52 (Or.inl rfl) h ?_
    have hb : thetaInt - ((52 : ℤ) : 𝓞 K) ∈ primeAbove61 4 := by rw [h]; exact hmem 52
    have hsub := Ideal.sub_mem _ hb (hmem 4)
    have heq : (thetaInt - ((52 : ℤ) : 𝓞 K)) - (thetaInt - ((4 : ℤ) : 𝓞 K)) =
        (-48 : 𝓞 K) := by push_cast; ring
    rw [heq] at hsub
    have hone : (1 : 𝓞 K) = (-14 : 𝓞 K) * (-48) - 11 * 61 := by norm_num
    rw [hone]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hsub) (Ideal.mul_mem_left _ _ (h61 4))
  · refine key 5 52 (Or.inr (Or.inl rfl)) h ?_
    have hb : thetaInt - ((52 : ℤ) : 𝓞 K) ∈ primeAbove61 5 := by rw [h]; exact hmem 52
    have hsub := Ideal.sub_mem _ hb (hmem 5)
    have heq : (thetaInt - ((52 : ℤ) : 𝓞 K)) - (thetaInt - ((5 : ℤ) : 𝓞 K)) =
        (-47 : 𝓞 K) := by push_cast; ring
    rw [heq] at hsub
    have hone : (1 : 𝓞 K) = (-13 : 𝓞 K) * (-47) - 10 * 61 := by norm_num
    rw [hone]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hsub) (Ideal.mul_mem_left _ _ (h61 5))

private theorem adjoin_thetaInt_eq_top : Algebra.adjoin ℤ ({thetaInt} : Set (𝓞 K)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hxspan : x ∈ Submodule.span ℤ (Set.range integralBasisVectorsInt) := by
    rw [span_integralBasisVectorsInt_eq_top]
    trivial
  exact Submodule.span_induction (s := Set.range integralBasisVectorsInt)
    (p := fun y _ => y ∈ Algebra.adjoin ℤ ({thetaInt} : Set (𝓞 K)))
    (fun y hy => by
      rcases hy with ⟨i, rfl⟩
      fin_cases i
      · change (1 : 𝓞 K) ∈ Algebra.adjoin ℤ ({thetaInt} : Set (𝓞 K))
        exact one_mem _
      · exact Algebra.subset_adjoin (Set.mem_singleton thetaInt)
      · change thetaInt ^ 2 ∈ Algebra.adjoin ℤ ({thetaInt} : Set (𝓞 K))
        exact pow_mem (Algebra.subset_adjoin (Set.mem_singleton thetaInt)) 2)
    (by simp)
    (fun _ _ _ _ hy hz => add_mem hy hz)
    (fun a _ _ hy => zsmul_mem hy a)
    hxspan

private noncomputable abbrev thetaIntPowerBasis : PowerBasis ℤ (𝓞 K) :=
  PowerBasis.ofAdjoinEqTop' (NumberField.RingOfIntegers.isIntegral thetaInt)
    adjoin_thetaInt_eq_top

private theorem thetaIntPowerBasis_gen : thetaIntPowerBasis.gen = thetaInt := by
  exact PowerBasis.ofAdjoinEqTop'_gen (NumberField.RingOfIntegers.isIntegral thetaInt)
    adjoin_thetaInt_eq_top

private theorem thetaInt_minpoly_eq : minpoly ℤ thetaInt = X ^ 3 - C (3 : ℤ) := by
  have hf : cubePolynomial ≠ 0 := by intro h; simpa using congrArg natDegree h
  set pb := AdjoinRoot.powerBasis hf with hpb
  have hgen : pb.gen = cubeRootThree := AdjoinRoot.powerBasis_gen hf
  have hmonic : cubePolynomial.Monic := by monicity!
  have hminQ : minpoly ℚ cubeRootThree = cubePolynomial := by
    rw [← hgen]
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic hmonic hf
  have hcoe : (thetaInt : K) = cubeRootThree :=
    NumberField.RingOfIntegers.map_mk cubeRootThree cubeRootThree_integral
  have hfield := minpoly.isIntegrallyClosed_eq_field_fractions (R := ℤ) (S := K) ℚ K
    cubeRootThree_integral
  change minpoly ℚ cubeRootThree =
    Polynomial.map (algebraMap ℤ ℚ) (minpoly ℤ cubeRootThree) at hfield
  rw [hminQ] at hfield
  have htarget : Polynomial.map (algebraMap ℤ ℚ) (minpoly ℤ thetaInt) = cubePolynomial := by
    rw [← NumberField.RingOfIntegers.minpoly_coe thetaInt, hcoe]
    exact hfield.symm
  have hmap : Polynomial.map (algebraMap ℤ ℚ) (minpoly ℤ thetaInt) =
      Polynomial.map (algebraMap ℤ ℚ) (X ^ 3 - C (3 : ℤ)) := by
    rw [htarget, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rfl
  exact Polynomial.map_injective (algebraMap ℤ ℚ)
    (show Function.Injective (algebraMap ℤ ℚ) from Int.cast_injective) hmap

private noncomputable def residueHom (p : ℕ) (r : ℤ) (hr : ((r : ZMod p)) ^ 3 = 3) :
    (𝓞 K) →ₐ[ℤ] ZMod p :=
  thetaIntPowerBasis.lift ((r : ℤ) : ZMod p) (by
    rw [thetaIntPowerBasis_gen, thetaInt_minpoly_eq]
    simp only [map_sub, map_pow, aeval_X, map_ofNat]
    exact sub_eq_zero.mpr hr)

private theorem residueHom_thetaInt (p : ℕ) (r : ℤ) (hr : ((r : ZMod p)) ^ 3 = 3) :
    residueHom p r hr thetaInt = (r : ZMod p) := by
  rw [← thetaIntPowerBasis_gen]
  exact thetaIntPowerBasis.lift_gen ((r : ℤ) : ZMod p) _

private theorem ker_residueHom (p : ℕ) (r : ℤ) (hr : ((r : ZMod p)) ^ 3 = 3) :
    RingHom.ker (residueHom p r hr).toRingHom =
      Ideal.span {(p : 𝓞 K), thetaInt - (r : 𝓞 K)} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [RingHom.mem_ker] at hx
    obtain ⟨q, -, hq⟩ := thetaIntPowerBasis.exists_eq_aeval x
    rw [thetaIntPowerBasis_gen] at hq
    have key : x - ((q.eval r : ℤ) : 𝓞 K) ∈ Ideal.span {thetaInt - (r : 𝓞 K)} := by
      rw [Ideal.mem_span_singleton, hq]
      have hdvd := Polynomial.sub_dvd_eval_sub thetaInt ((r : ℤ) : 𝓞 K)
        (q.map (algebraMap ℤ (𝓞 K)))
      have e1 : (q.map (algebraMap ℤ (𝓞 K))).eval thetaInt =
          Polynomial.aeval thetaInt q := by
        rw [Polynomial.eval_map, ← Polynomial.aeval_def]
      have e2 : (q.map (algebraMap ℤ (𝓞 K))).eval ((r : ℤ) : 𝓞 K) =
          ((q.eval r : ℤ) : 𝓞 K) := by
        have hcast : ((r : ℤ) : 𝓞 K) = algebraMap ℤ (𝓞 K) r := by
          simp [algebraMap_int_eq]
        rw [Polynomial.eval_map, hcast, Polynomial.eval₂_at_apply]
        simp [algebraMap_int_eq]
      rw [e1, e2] at hdvd
      exact hdvd
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp key
    have hphi : ((q.eval r : ℤ) : ZMod p) = 0 := by
      have h1 : residueHom p r hr (x - ((q.eval r : ℤ) : 𝓞 K)) = 0 := by
        rw [hd, map_mul, map_sub, residueHom_thetaInt, map_intCast, sub_self, zero_mul]
      rw [map_sub, map_intCast, show residueHom p r hr x = 0 from hx, zero_sub,
        neg_eq_zero] at h1
      exact h1
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hphi
    have hx_eq : x = (thetaInt - (r : 𝓞 K)) * d + (p : 𝓞 K) * ((m : ℤ) : 𝓞 K) := by
      have h2 : x = (thetaInt - (r : 𝓞 K)) * d + ((q.eval r : ℤ) : 𝓞 K) := by
        rw [← hd]
        ring
      rw [h2, hm]
      push_cast
      ring
    rw [hx_eq]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_)) <;> simp
  · rw [Ideal.span_le]
    rintro y (rfl | rfl)
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      simp
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      have h0 : (residueHom p r hr) (thetaInt - (r : 𝓞 K)) = 0 := by
        rw [map_sub, residueHom_thetaInt, map_intCast, sub_self]
      exact h0

private theorem residueHom_surjective (p : ℕ) (r : ℤ) (hr : ((r : ZMod p)) ^ 3 = 3) :
    Function.Surjective (residueHom p r hr) := by
  intro z
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective z
  exact ⟨((m : ℤ) : 𝓞 K), by rw [map_intCast]; exact hm⟩

private theorem isMaximal_span_pair (p : ℕ) [Fact p.Prime] (r : ℤ)
    (hr : ((r : ZMod p)) ^ 3 = 3) :
    (Ideal.span {(p : 𝓞 K), thetaInt - (r : 𝓞 K)}).IsMaximal := by
  rw [← ker_residueHom p r hr]
  exact RingHom.ker_isMaximal_of_surjective _ (residueHom_surjective p r hr)

private theorem absNorm_span_pair (p : ℕ) (r : ℤ) (hr : ((r : ZMod p)) ^ 3 = 3) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K), thetaInt - (r : 𝓞 K)}) = p := by
  rw [← ker_residueHom p r hr, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (residueHom_surjective p r hr)).toEquiv]
  exact Nat.card_zmod p

/-- General degree-one splitting criterion: away from the ramified prime `3`, a rational
prime has a residue-degree-one prime above it iff `X³ - 3` has a root modulo `p`. -/
theorem exists_degree_one_prime_iff_cube_root_mod_p (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧
      Ideal.absNorm P = p) ↔ ∃ r : ZMod p, r ^ 3 = (3 : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have : p ≠ 3 := hp3
  constructor
  · rintro ⟨P, _hPprime, _hle, habs⟩
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at habs
    haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (by
      rw [habs]
      exact hp.ne_zero)
    haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
    have hcard' : Fintype.card ((𝓞 K) ⧸ P) = p := by
      rw [← Nat.card_eq_fintype_card]
      exact habs
    let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) hp hcard'
    obtain ⟨s, hs⟩ := e.surjective (Ideal.Quotient.mk P thetaInt)
    refine ⟨s, ?_⟩
    apply e.injective
    rw [map_pow, hs, map_ofNat, ← map_pow (Ideal.Quotient.mk P), thetaInt_cube, map_ofNat]
  · rintro ⟨r, hr⟩
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective r
    have hzroot : ((z : ℤ) : ZMod p) ^ 3 = 3 := by
      rw [hz]
      exact hr
    refine ⟨Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - ((z : ℤ) : 𝓞 K)},
      (isMaximal_span_pair p z hzroot).isPrime, ?_, absNorm_span_pair p z hzroot⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span (by simp)

/-- The splitting law at ramified primes: a rational prime `p` ramifies in `ℚ(∛3)` (some prime
of `𝓞 K` divides `(p)` at least twice) iff `p = 3`, i.e. iff `p` divides the discriminant
`-3⁵`. -/
theorem ramified_iff_eq_three (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔ p = 3 := by
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
    have hfin : Module.finrank ℤ (𝓞 K) = 3 := by
      rw [Module.finrank_eq_card_basis concreteIntegralBasis, Fintype.card_fin]
    have habsp : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 3 := by
      rw [Ideal.absNorm_span_singleton]
      have hcast : ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) ((p : ℕ) : ℤ) := by push_cast; rfl
      rw [hcast, Algebra.norm_algebraMap, hfin, Int.natAbs_pow, Int.natAbs_natCast]
    have habsPp3 : Ideal.absNorm P ∣ p ^ 3 :=
      habsp ▸ Ideal.absNorm_dvd_absNorm_of_le hple
    obtain ⟨k, hk3, hkeq⟩ := (Nat.dvd_prime_pow hp).mp habsPp3
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hkeq
      exact hP.ne_top (Ideal.absNorm_eq_one_iff.mp hkeq)
    have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) =
        Ideal.span {((p : ℕ) : 𝓞 K)} := by
      rw [Ideal.map_span, Set.image_singleton]
      norm_num
    have hle2' : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 2 := by
      rw [hmap]; exact hle2
    have hno4 : ¬ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 4 := by
      intro h4
      rw [hmap] at h4
      have hd := Ideal.absNorm_dvd_absNorm_of_le h4
      rw [map_pow, habsp, hkeq, ← pow_mul] at hd
      rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
      omega
    have hidx : Ideal.ramificationIdx (Ideal.span {((p : ℕ) : ℤ)}) P ≠ 1 := by
      by_cases h3 : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 3
      · rw [Ideal.ramificationIdx_spec h3 hno4]
        norm_num
      · rw [Ideal.ramificationIdx_spec hle2' h3]
        norm_num
    have hund : Ideal.under ℤ P = Ideal.span {((p : ℕ) : ℤ)} := by
      have hmem : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ P := by
        rw [Ideal.under, Ideal.mem_comap]
        have : algebraMap ℤ (𝓞 K) ((p : ℕ) : ℤ) = ((p : ℕ) : 𝓞 K) := by push_cast; rfl
        rw [this]
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
    have habsP243 : Ideal.absNorm P ∣ 243 := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPdiff)
      rw [NumberField.absNorm_differentIdeal (K := K), numberField_discr_eq] at h
      simpa using h
    have hpdvd : p ∣ 243 := ((hkeq ▸ dvd_pow_self p hk0).trans habsP243)
    have hp3 : p ∣ 3 := hp.dvd_of_dvd_pow (show p ∣ 3 ^ 5 by norm_num; exact hpdvd)
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp3
  · rintro rfl
    refine ⟨Ideal.span {thetaInt}, isPrime_span_theta, ?_⟩
    have hcast : ((3 : ℕ) : 𝓞 K) = (3 : 𝓞 K) := by norm_num
    rw [hcast, span_three_eq]
    exact Ideal.pow_le_pow_right (by norm_num)


end NumberField.CubeRootThree
