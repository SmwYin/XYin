/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.NormForm
import XYin.NumberField.FieldExamples.Common

/-!
# `ℚ(√-6)` Prime splitting

This file develops the prime splitting part of the `ℚ(√-6)` number field example.
-/

noncomputable section

open Module Polynomial
open NumberField.FieldExamples
open scoped NumberField nonZeroDivisors QuadraticAlgebra

namespace NumberField.SqrtNegSix

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

/-- The ramified prime `(2, θ)` lies over `(2)`. -/
theorem liesOver_primeAboveTwo : primeAboveTwo.LiesOver (Ideal.span {(2 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_primeAboveTwo.ne_top
    (show Prime (2 : ℤ) by norm_num)]
  change (2 : 𝓞 K) ∈ primeAboveTwo
  rw [primeAboveTwo]
  exact Ideal.subset_span (by simp)

/-- The ramified prime `(2, θ)` has inertia degree `1` over `2`. -/
theorem inertiaDeg_primeAboveTwo :
    (Ideal.span {(2 : ℤ)}).inertiaDeg primeAboveTwo = 1 := by
  haveI : primeAboveTwo.LiesOver (Ideal.span {(2 : ℤ)}) := liesOver_primeAboveTwo
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := primeAboveTwo) (p := 2) Nat.prime_two
  rw [absNorm_primeAboveTwo] at h
  exact ((Nat.Prime.pow_eq_iff Nat.prime_two).mp h.symm).2

/-- The ramified prime `(2, θ)` has ramification index `2` over `2`. -/
theorem ramificationIdx_primeAboveTwo :
    (Ideal.span {(2 : ℤ)}).ramificationIdx primeAboveTwo = 2 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(2 : 𝓞 K)} ≤ primeAboveTwo ^ 2
    rw [span_two_eq]
  · intro hle3
    have hdvd : Ideal.absNorm (primeAboveTwo ^ 3) ∣
        Ideal.absNorm (Ideal.span {((2 : ℤ) : 𝓞 K)}) := by
      simpa [Ideal.map_span, Set.image_singleton] using Ideal.absNorm_dvd_absNorm_of_le hle3
    have hnorm2 : Ideal.absNorm (Ideal.span {((2 : ℤ) : 𝓞 K)}) = 4 := by
      change Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) = 4
      have h := intNorm_eq_normForm 2 0
      have heq : (2 : 𝓞 K) = (2 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt := by simp
      rw [Ideal.absNorm_span_singleton, heq, h]
      rfl
    have hnorm3 : Ideal.absNorm (primeAboveTwo ^ 3) = 8 := by
      rw [map_pow, absNorm_primeAboveTwo]
      norm_num
    rw [hnorm3, hnorm2] at hdvd
    norm_num at hdvd

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

/-- The ramified prime `(3, θ)` lies over `(3)`. -/
theorem liesOver_primeAboveThree : primeAboveThree.LiesOver (Ideal.span {(3 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_primeAboveThree.ne_top
    (show Prime (3 : ℤ) by norm_num)]
  change (3 : 𝓞 K) ∈ primeAboveThree
  rw [primeAboveThree]
  exact Ideal.subset_span (by simp)

/-- The ramified prime `(3, θ)` has inertia degree `1` over `3`. -/
theorem inertiaDeg_primeAboveThree :
    (Ideal.span {(3 : ℤ)}).inertiaDeg primeAboveThree = 1 := by
  haveI : primeAboveThree.LiesOver (Ideal.span {(3 : ℤ)}) := liesOver_primeAboveThree
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := primeAboveThree) (p := 3) Nat.prime_three
  rw [absNorm_primeAboveThree] at h
  exact ((Nat.Prime.pow_eq_iff Nat.prime_three).mp h.symm).2

/-- The ramified prime `(3, θ)` has ramification index `2` over `3`. -/
theorem ramificationIdx_primeAboveThree :
    (Ideal.span {(3 : ℤ)}).ramificationIdx primeAboveThree = 2 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(3 : 𝓞 K)} ≤ primeAboveThree ^ 2
    rw [span_three_eq]
  · intro hle3
    have hdvd : Ideal.absNorm (primeAboveThree ^ 3) ∣
        Ideal.absNorm (Ideal.span {((3 : ℤ) : 𝓞 K)}) := by
      simpa [Ideal.map_span, Set.image_singleton] using Ideal.absNorm_dvd_absNorm_of_le hle3
    have hnorm3 : Ideal.absNorm (Ideal.span {((3 : ℤ) : 𝓞 K)}) = 9 := by
      change Ideal.absNorm (Ideal.span {(3 : 𝓞 K)}) = 9
      have h := intNorm_eq_normForm 3 0
      have heq : (3 : 𝓞 K) = (3 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt := by simp
      rw [Ideal.absNorm_span_singleton, heq, h]
      rfl
    have hnormP3 : Ideal.absNorm (primeAboveThree ^ 3) = 27 := by
      rw [map_pow, absNorm_primeAboveThree]
      norm_num
    rw [hnormP3, hnorm3] at hdvd
    norm_num at hdvd

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
theorem absNorm_span_one_add_theta : Ideal.absNorm (Ideal.span {1 + thetaInt}) = 7 := by
  have h := intNorm_eq_normForm 1 1
  have heq : (1 : 𝓞 K) + thetaInt = (1 : ℤ) • (1 : 𝓞 K) + (1 : ℤ) • thetaInt := by
    simp
  rw [Ideal.absNorm_span_singleton, heq, h]
  rfl

theorem isPrime_span_one_add_theta : (Ideal.span {1 + thetaInt}).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_span_one_add_theta]
  exact (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)

/-- `(1 - θ)` is the conjugate principal prime above `7`, also of norm `7`. -/
theorem absNorm_span_one_sub_theta : Ideal.absNorm (Ideal.span {1 - thetaInt}) = 7 := by
  have h := intNorm_eq_normForm 1 (-1)
  have heq : (1 : ℤ) • (1 : 𝓞 K) + (-1 : ℤ) • thetaInt = 1 - thetaInt := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [heq] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- `(1 - θ)` is the conjugate prime above `7`. -/
theorem isPrime_span_one_sub_theta : (Ideal.span {1 - thetaInt}).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_span_one_sub_theta]
  exact (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)

/-- The prime `(1 + θ)` lies over `(7)`. -/
theorem liesOver_span_one_add_theta :
    (Ideal.span {1 + thetaInt}).LiesOver (Ideal.span {(7 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_one_add_theta.ne_top
    (show Prime (7 : ℤ) by norm_num)]
  change (7 : 𝓞 K) ∈ Ideal.span {1 + thetaInt}
  rw [seven_eq_mul]
  exact Ideal.mul_mem_right (1 - thetaInt) (Ideal.span {1 + thetaInt})
    (Ideal.mem_span_singleton_self (1 + thetaInt))

/-- The prime `(1 - θ)` lies over `(7)`. -/
theorem liesOver_span_one_sub_theta :
    (Ideal.span {1 - thetaInt}).LiesOver (Ideal.span {(7 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_one_sub_theta.ne_top
    (show Prime (7 : ℤ) by norm_num)]
  change (7 : 𝓞 K) ∈ Ideal.span {1 - thetaInt}
  rw [show (7 : 𝓞 K) = (1 - thetaInt) * (1 + thetaInt) from by
    rw [seven_eq_mul]
    ring]
  exact Ideal.mul_mem_right (1 + thetaInt) (Ideal.span {1 - thetaInt})
    (Ideal.mem_span_singleton_self (1 - thetaInt))

/-- The split prime `(1 + θ)` has inertia degree `1` over `7`. -/
theorem inertiaDeg_span_one_add_theta :
    (Ideal.span {(7 : ℤ)}).inertiaDeg (Ideal.span {1 + thetaInt}) = 1 := by
  haveI : (Ideal.span {1 + thetaInt}).LiesOver (Ideal.span {(7 : ℤ)}) :=
    liesOver_span_one_add_theta
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {1 + thetaInt})
    (p := 7) (by norm_num : Nat.Prime 7)
  rw [absNorm_span_one_add_theta] at h
  exact ((Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp h.symm).2

/-- The split prime `(1 - θ)` has inertia degree `1` over `7`. -/
theorem inertiaDeg_span_one_sub_theta :
    (Ideal.span {(7 : ℤ)}).inertiaDeg (Ideal.span {1 - thetaInt}) = 1 := by
  haveI : (Ideal.span {1 - thetaInt}).LiesOver (Ideal.span {(7 : ℤ)}) :=
    liesOver_span_one_sub_theta
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {1 - thetaInt})
    (p := 7) (by norm_num : Nat.Prime 7)
  rw [absNorm_span_one_sub_theta] at h
  exact ((Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp h.symm).2

/-- `5` splits, but with *non-principal* prime factors `(5, θ - 2)` and `(5, θ + 2)`:
`-6 ≡ 2² (mod 5)` yet `x² + 6y² = 5` has no integer solutions (the prime `5` is represented
by the non-principal genus form `2x² + 3y²` instead). -/
def primeAboveFiveSubTwo : Ideal (𝓞 K) := Ideal.span {(5 : 𝓞 K), thetaInt - 2}

/-- The conjugate non-principal prime above `5`: `(5, θ + 2)`. -/
def primeAboveFiveAddTwo : Ideal (𝓞 K) := Ideal.span {(5 : 𝓞 K), thetaInt + 2}

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

/-- `(5, θ + 2)` is also a proper ideal. -/
private theorem span_five_theta_add_two_ne_top :
    Ideal.span {(5 : 𝓞 K), thetaInt + 2} ≠ ⊤ := by
  intro htop
  have hmem : (1 : 𝓞 K) ∈ Ideal.span {(5 : 𝓞 K), thetaInt + 2} := by
    rw [htop]
    trivial
  rw [Ideal.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  obtain ⟨x, y, ha⟩ := exists_eq_smul_one_add_smul_theta a
  obtain ⟨u, v, hb⟩ := exists_eq_smul_one_add_smul_theta b
  have hsum : ∑ i : Fin 2,
      (![5 * x + 2 * u - 6 * v - 1, 5 * y + u + 2 * v] i) •
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
    refine ⟨x - 2 * y - 2 * v, ?_⟩
    omega
  have := Int.le_of_dvd zero_lt_one hdiv
  norm_num at this

/-- The non-principal prime `(5, θ - 2)` has norm `5`. -/
theorem absNorm_primeAboveFiveSubTwo : Ideal.absNorm primeAboveFiveSubTwo = 5 := by
  have hspan5 : Ideal.absNorm (Ideal.span {(5 : 𝓞 K)}) = 25 := by
    simpa using absNorm_span_natCast 5
  have hle : Ideal.span {(5 : 𝓞 K)} ≤ primeAboveFiveSubTwo := by
    rw [primeAboveFiveSubTwo]
    exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span (by simp))
  have hdvd : Ideal.absNorm primeAboveFiveSubTwo ∣ 5 ^ 2 := by
    simpa [hspan5] using Ideal.absNorm_dvd_absNorm_of_le hle
  have hne1 : Ideal.absNorm primeAboveFiveSubTwo ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    simpa [primeAboveFiveSubTwo] using span_five_theta_sub_two_ne_top
  have hne25 : Ideal.absNorm primeAboveFiveSubTwo ≠ 25 := by
    intro h25
    have heq := eq_of_le_of_absNorm_eq hle hspan5 h25 (by norm_num)
    have hmem : thetaInt - 2 ∈ Ideal.span {(5 : 𝓞 K)} := by
      rw [heq]
      rw [primeAboveFiveSubTwo]
      exact Ideal.subset_span (by simp)
    refine unit_theta_coeff_not_mem 5 (by norm_num) (-2) 1 (Or.inl rfl) ?_
    rw [show (((-2 : ℤ) : 𝓞 K) + ((1 : ℤ) : 𝓞 K) * thetaInt =
      thetaInt - 2) by push_cast; ring]
    exact hmem
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hdvd
  interval_cases k
  · rw [pow_zero] at hkeq
    exact absurd hkeq hne1
  · simpa using hkeq
  · rw [show 5 ^ 2 = 25 by norm_num] at hkeq
    exact absurd hkeq hne25

/-- The non-principal prime `(5, θ + 2)` has norm `5`. -/
theorem absNorm_primeAboveFiveAddTwo : Ideal.absNorm primeAboveFiveAddTwo = 5 := by
  have hspan5 : Ideal.absNorm (Ideal.span {(5 : 𝓞 K)}) = 25 := by
    simpa using absNorm_span_natCast 5
  have hle : Ideal.span {(5 : 𝓞 K)} ≤ primeAboveFiveAddTwo := by
    rw [primeAboveFiveAddTwo]
    exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span (by simp))
  have hdvd : Ideal.absNorm primeAboveFiveAddTwo ∣ 5 ^ 2 := by
    simpa [hspan5] using Ideal.absNorm_dvd_absNorm_of_le hle
  have hne1 : Ideal.absNorm primeAboveFiveAddTwo ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    simpa [primeAboveFiveAddTwo] using span_five_theta_add_two_ne_top
  have hne25 : Ideal.absNorm primeAboveFiveAddTwo ≠ 25 := by
    intro h25
    have heq := eq_of_le_of_absNorm_eq hle hspan5 h25 (by norm_num)
    have hmem : thetaInt + 2 ∈ Ideal.span {(5 : 𝓞 K)} := by
      rw [heq]
      rw [primeAboveFiveAddTwo]
      exact Ideal.subset_span (by simp)
    refine unit_theta_coeff_not_mem 5 (by norm_num) 2 1 (Or.inl rfl) ?_
    rw [show (((2 : ℤ) : 𝓞 K) + ((1 : ℤ) : 𝓞 K) * thetaInt =
      thetaInt + 2) by push_cast; ring]
    exact hmem
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hdvd
  interval_cases k
  · rw [pow_zero] at hkeq
    exact absurd hkeq hne1
  · simpa using hkeq
  · rw [show 5 ^ 2 = 25 by norm_num] at hkeq
    exact absurd hkeq hne25

/-- `(5, θ - 2)` is a prime ideal. -/
theorem isPrime_primeAboveFiveSubTwo : primeAboveFiveSubTwo.IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_primeAboveFiveSubTwo]
  exact (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)

/-- `(5, θ + 2)` is a prime ideal. -/
theorem isPrime_primeAboveFiveAddTwo : primeAboveFiveAddTwo.IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_primeAboveFiveAddTwo]
  exact (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)

/-- The prime `(5, θ - 2)` lies over `(5)`. -/
theorem liesOver_primeAboveFiveSubTwo :
    primeAboveFiveSubTwo.LiesOver (Ideal.span {(5 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_primeAboveFiveSubTwo.ne_top
    (show Prime (5 : ℤ) by norm_num)]
  change (5 : 𝓞 K) ∈ primeAboveFiveSubTwo
  rw [primeAboveFiveSubTwo]
  exact Ideal.subset_span (by simp)

/-- The prime `(5, θ + 2)` lies over `(5)`. -/
theorem liesOver_primeAboveFiveAddTwo :
    primeAboveFiveAddTwo.LiesOver (Ideal.span {(5 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_primeAboveFiveAddTwo.ne_top
    (show Prime (5 : ℤ) by norm_num)]
  change (5 : 𝓞 K) ∈ primeAboveFiveAddTwo
  rw [primeAboveFiveAddTwo]
  exact Ideal.subset_span (by simp)

/-- The split prime `(5, θ - 2)` has inertia degree `1` over `5`. -/
theorem inertiaDeg_primeAboveFiveSubTwo :
    (Ideal.span {(5 : ℤ)}).inertiaDeg primeAboveFiveSubTwo = 1 := by
  haveI : primeAboveFiveSubTwo.LiesOver (Ideal.span {(5 : ℤ)}) :=
    liesOver_primeAboveFiveSubTwo
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := primeAboveFiveSubTwo)
    (p := 5) (by norm_num : Nat.Prime 5)
  rw [absNorm_primeAboveFiveSubTwo] at h
  exact ((Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 5)).mp h.symm).2

/-- The split prime `(5, θ + 2)` has inertia degree `1` over `5`. -/
theorem inertiaDeg_primeAboveFiveAddTwo :
    (Ideal.span {(5 : ℤ)}).inertiaDeg primeAboveFiveAddTwo = 1 := by
  haveI : primeAboveFiveAddTwo.LiesOver (Ideal.span {(5 : ℤ)}) :=
    liesOver_primeAboveFiveAddTwo
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := primeAboveFiveAddTwo)
    (p := 5) (by norm_num : Nat.Prime 5)
  rw [absNorm_primeAboveFiveAddTwo] at h
  exact ((Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 5)).mp h.symm).2

private theorem intNorm_five : Algebra.norm ℤ (5 : 𝓞 K) = 25 := by
  have h := intNorm_eq_normForm 5 0
  have heq : (5 : 𝓞 K) = (5 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt := by
    simp
  rwa [← heq] at h

private theorem intNorm_theta_sub_two : Algebra.norm ℤ (thetaInt - 2) = 10 := by
  have h := intNorm_eq_normForm (-2) 1
  have heq : thetaInt - 2 = (-2 : ℤ) • (1 : 𝓞 K) + (1 : ℤ) • thetaInt := by
    simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_one]
    ring
  rw [heq, h]
  norm_num

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
  let A : ℤ := Algebra.norm ℤ a
  let B : ℤ := Algebra.norm ℤ b
  let C : ℤ := Algebra.norm ℤ c
  have hprod5 : A * B = 25 := by
    have h := congrArg (Algebra.norm ℤ) hb
    rw [map_mul, intNorm_five] at h
    exact (by simpa [A, B] using h.symm)
  have hprod10 : A * C = 10 := by
    have h := congrArg (Algebra.norm ℤ) hc
    rw [map_mul, intNorm_theta_sub_two] at h
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

private theorem absNorm_span_thirteen_aux :
    Ideal.absNorm (Ideal.span {(13 : 𝓞 K)}) = 169 := by
  have h := intNorm_eq_normForm 13 0
  have heq : (13 : 𝓞 K) = (13 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt := by
    simp
  rw [Ideal.absNorm_span_singleton, heq, h]
  rfl

/-- `13` is inert in `ℚ(√-6)`: `-6` is not a square mod `13`. -/
theorem isPrime_span_thirteen : (Ideal.span {(13 : 𝓞 K)}).IsPrime := by
  have habs169 := absNorm_span_thirteen_aux
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

/-- The inert prime `(13)` has norm `13²`. -/
theorem absNorm_span_thirteen : Ideal.absNorm (Ideal.span {(13 : 𝓞 K)}) = 169 := by
  exact absNorm_span_thirteen_aux

/-- The inert prime `(13)` lies over `(13)`. -/
theorem liesOver_span_thirteen :
    (Ideal.span {(13 : 𝓞 K)}).LiesOver (Ideal.span {(13 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_thirteen.ne_top
    (show Prime (13 : ℤ) by norm_num)]
  change (13 : 𝓞 K) ∈ Ideal.span {(13 : 𝓞 K)}
  exact Ideal.mem_span_singleton_self _

/-- The inert prime `(13)` has inertia degree `2`. -/
theorem inertiaDeg_span_thirteen :
    (Ideal.span {(13 : ℤ)}).inertiaDeg (Ideal.span {(13 : 𝓞 K)}) = 2 := by
  haveI : (Ideal.span {(13 : 𝓞 K)}).LiesOver (Ideal.span {(13 : ℤ)}) :=
    liesOver_span_thirteen
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {(13 : 𝓞 K)})
    (p := 13) (by norm_num : Nat.Prime 13)
  rw [absNorm_span_thirteen] at h
  change 13 ^ 2 = 13 ^ (Ideal.span {(13 : ℤ)}).inertiaDeg
    (Ideal.span {(13 : 𝓞 K)}) at h
  exact Nat.pow_right_injective (by norm_num : 1 < 13) h.symm

private theorem mod_twentyfour_of_splits (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3)
    (h : ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) :
    p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rcases h with ⟨P, Q, hPprime, hQprime, _hPQne, hspan⟩
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

private theorem exists_root_data (p : ℕ) [NeZero p] {s : ZMod p}
    (hs : ((-6 : ℤ) : ZMod p) = s * s) :
    ∃ c d k₁ k₂ : ℤ,
      ((c : ℤ) : ZMod p) = s ∧ ((d : ℤ) : ZMod p) = -s ∧
        (thetaInt - (c : 𝓞 K)) * (thetaInt - (d : 𝓞 K)) =
          ((p : ℕ) : 𝓞 K) * (-(k₁ : 𝓞 K) * thetaInt + (k₂ : 𝓞 K)) := by
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
  refine ⟨c, d, k₁, k₂, hct, hdt, ?_⟩
  linear_combination thetaInt_sq - thetaInt * hk₁K + hk₂K

private theorem absNorm_span_pair_not_one (p : ℕ) (hp2le : 2 ≤ p)
    (c d k₁ k₂ : ℤ)
    (hprod : (thetaInt - (c : 𝓞 K)) * (thetaInt - (d : 𝓞 K)) =
      ((p : ℕ) : 𝓞 K) * (-(k₁ : 𝓞 K) * thetaInt + (k₂ : 𝓞 K))) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)}) ≠ 1 := by
  rw [Ne, Ideal.absNorm_eq_one_iff]
  intro htop
  have h1 : (1 : 𝓞 K) ∈ Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)} :=
    htop ▸ Submodule.mem_top
  rw [Ideal.mem_span_pair] at h1
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
  refine unit_theta_coeff_not_mem p hp2le (-d) 1 (Or.inl rfl) ?_
  rw [show ((-d : ℤ) : 𝓞 K) + ((1 : ℤ) : 𝓞 K) * thetaInt =
    thetaInt - (d : 𝓞 K) by push_cast; ring]
  exact htd

private theorem absNorm_span_pair_ne_prime_sq (p : ℕ) (hp : p.Prime) (c : ℤ) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)}) ≠ p ^ 2 := by
  intro hN
  have hle : Ideal.span {((p : ℕ) : 𝓞 K)} ≤
      Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)} :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span (Set.mem_insert _ _))
  have hmem : thetaInt - (c : 𝓞 K) ∈
      Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)} :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have heq := eq_of_le_of_absNorm_eq hle (absNorm_span_natCast p) hN
    (pow_ne_zero 2 hp.pos.ne')
  refine unit_theta_coeff_not_mem p hp.two_le (-c) 1 (Or.inl rfl) ?_
  rw [show ((-c : ℤ) : 𝓞 K) + ((1 : ℤ) : 𝓞 K) * thetaInt =
    thetaInt - (c : 𝓞 K) by push_cast; ring]
  rw [heq]
  exact hmem

private theorem absNorm_span_pair_eq_prime (p : ℕ) (hp : p.Prime)
    (c d k₁ k₂ : ℤ)
    (hprod : (thetaInt - (c : 𝓞 K)) * (thetaInt - (d : 𝓞 K)) =
      ((p : ℕ) : 𝓞 K) * (-(k₁ : 𝓞 K) * thetaInt + (k₂ : 𝓞 K))) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)}) = p := by
  have hle : Ideal.span {((p : ℕ) : 𝓞 K)} ≤
      Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)} :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span (Set.mem_insert _ _))
  exact eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq hp
    ((absNorm_span_natCast p) ▸ Ideal.absNorm_dvd_absNorm_of_le hle)
    (absNorm_span_pair_not_one p hp.two_le c d k₁ k₂ hprod)
    (absNorm_span_pair_ne_prime_sq p hp c)

private theorem root_ne_neg_of_square_neg_six (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) {s : ZMod p} (hs : ((-6 : ℤ) : ZMod p) = s * s) :
    s ≠ -s := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h0)))
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

private theorem span_pair_ne_of_roots_ne (p : ℕ) (hp : p.Prime) {c d : ℤ}
    (hcd : ((c - d : ℤ) : ZMod p) ≠ 0)
    (hNP : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)}) = p) :
    Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)} ≠
      Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (d : 𝓞 K)} := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro heq
  obtain ⟨m, k₃, hk₃⟩ := exists_int_inverse_mod_prime p (c - d) hcd
  have hk₃K : ((m : ℕ) : 𝓞 K) * ((c : 𝓞 K) - (d : 𝓞 K)) - 1 =
      ((p : ℕ) : 𝓞 K) * (k₃ : 𝓞 K) := by
    have h := congrArg (fun n : ℤ => ((n : ℤ) : 𝓞 K)) hk₃
    push_cast at h
    exact h
  have h1 : (1 : 𝓞 K) ∈ Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)} := by
    have htdP : thetaInt - (d : 𝓞 K) ∈
        Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)} := by
      rw [heq]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have hid : (1 : 𝓞 K) = ((m : ℕ) : 𝓞 K) *
        ((thetaInt - (d : 𝓞 K)) - (thetaInt - (c : 𝓞 K))) -
        (k₃ : 𝓞 K) * ((p : ℕ) : 𝓞 K) := by
      linear_combination -hk₃K
    rw [hid]
    exact Submodule.sub_mem _
      (Ideal.mul_mem_left _ _ (Submodule.sub_mem _ htdP
        (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
  have habs := hNP
  rw [(Ideal.eq_top_iff_one _).mpr h1, Ideal.absNorm_top] at habs
  exact hp.ne_one (by omega)

private theorem span_pair_mul_eq_span_natCast (p : ℕ) (hp : p.Prime) (c d k₁ k₂ : ℤ)
    (hprod : (thetaInt - (c : 𝓞 K)) * (thetaInt - (d : 𝓞 K)) =
      ((p : ℕ) : 𝓞 K) * (-(k₁ : 𝓞 K) * thetaInt + (k₂ : 𝓞 K)))
    (hNP : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)}) = p)
    (hNQ : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (d : 𝓞 K)}) = p) :
    Ideal.span {((p : ℕ) : 𝓞 K)} =
      Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)} *
        Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (d : 𝓞 K)} := by
  have hle : Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)} *
      Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (d : 𝓞 K)} ≤
        Ideal.span {((p : ℕ) : 𝓞 K)} := by
    rw [Ideal.mul_le]
    intro r1 hr1 r2 hr2
    rw [Ideal.mem_span_pair] at hr1
    rw [Ideal.mem_span_pair] at hr2
    obtain ⟨x1, y1, h1⟩ := hr1
    obtain ⟨x2, y2, h2⟩ := hr2
    rw [Ideal.mem_span_singleton]
    refine ⟨x1 * x2 * ((p : ℕ) : 𝓞 K) + x1 * y2 * (thetaInt - (d : 𝓞 K)) +
      y1 * x2 * (thetaInt - (c : 𝓞 K)) +
      y1 * y2 * (-(k₁ : 𝓞 K) * thetaInt + (k₂ : 𝓞 K)), ?_⟩
    rw [← h1, ← h2]
    linear_combination (y1 * y2) * hprod
  have hNPQ : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)} *
      Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (d : 𝓞 K)}) = p ^ 2 := by
    rw [_root_.map_mul, hNP, hNQ]
    ring
  exact (eq_of_le_of_absNorm_eq hle hNPQ (absNorm_span_natCast p)
    (pow_ne_zero 2 hp.pos.ne')).symm

private theorem splits_of_square_neg_six (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) {s : ZMod p} (hs : ((-6 : ℤ) : ZMod p) = s * s) :
    ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨c, d, k₁, k₂, hct, hdt, hprod⟩ := exists_root_data p hs
  let P : Ideal (𝓞 K) := Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (c : 𝓞 K)}
  let Q : Ideal (𝓞 K) := Ideal.span {((p : ℕ) : 𝓞 K), thetaInt - (d : 𝓞 K)}
  have hNP : Ideal.absNorm P = p := by
    dsimp [P]
    exact absNorm_span_pair_eq_prime p hp c d k₁ k₂ hprod
  have hprod_sym : (thetaInt - (d : 𝓞 K)) * (thetaInt - (c : 𝓞 K)) =
      ((p : ℕ) : 𝓞 K) * (-(k₁ : 𝓞 K) * thetaInt + (k₂ : 𝓞 K)) := by
    rw [mul_comm (thetaInt - (d : 𝓞 K)) (thetaInt - (c : 𝓞 K))]
    exact hprod
  have hNQ : Ideal.absNorm Q = p := by
    dsimp [Q]
    exact absNorm_span_pair_eq_prime p hp d c k₁ k₂ hprod_sym
  have hPprime : P.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hNP]
    exact hp
  have hQprime : Q.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hNQ]
    exact hp
  have hsne : s ≠ -s := root_ne_neg_of_square_neg_six p hp hp2 hp3 hs
  have hcd : ((c - d : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    rw [hct, hdt]
    intro h0
    exact hsne (by linear_combination h0)
  have hPQne : P ≠ Q := by
    dsimp [P, Q]
    exact span_pair_ne_of_roots_ne p hp hcd hNP
  have hPQ : Ideal.span {((p : ℕ) : 𝓞 K)} = P * Q := by
    dsimp [P, Q]
    exact span_pair_mul_eq_span_natCast p hp c d k₁ k₂ hprod hNP hNQ
  exact ⟨P, Q, hPprime, hQprime, hPQne, hPQ⟩

/-- The splitting law for `ℚ(√-6)`: a prime `p ∤ 24` splits into two distinct primes iff
`-6` is a square mod `p`, iff `p ≡ 1, 5, 7, 11 (mod 24)`. -/
theorem splits_iff_mod_twentyfour (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) ↔
        p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 := by
  constructor
  · exact mod_twentyfour_of_splits p hp hp2 hp3
  · intro hmod
    have hsq : IsSquare ((-6 : ℤ) : ZMod p) :=
      (isSquare_neg_six_iff_mod_twentyfour p hp hp2 hp3).mpr hmod
    obtain ⟨s, hs⟩ := hsq
    exact splits_of_square_neg_six p hp hp2 hp3 hs

private theorem eq_two_or_eq_three_of_prime_dvd_twentyfour {p : ℕ} (hp : p.Prime)
    (hpdvd : p ∣ 24) : p = 2 ∨ p = 3 := by
  have hpor : p ∣ 2 ^ 3 ∨ p ∣ 3 := hp.dvd_mul.mp (by simpa using hpdvd)
  rcases hpor with hp2pow | hp3dvd
  · left
    have hp2dvd : p ∣ 2 := hp.dvd_of_dvd_pow hp2pow
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2dvd
  · right
    exact (Nat.prime_dvd_prime_iff_eq hp (show Nat.Prime 3 from by decide)).mp hp3dvd

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
    have habsp : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 2 :=
      absNorm_span_natCast p
    have habsPp2 : Ideal.absNorm P ∣ p ^ 2 :=
      habsp ▸ Ideal.absNorm_dvd_absNorm_of_le hple
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow hp).mp habsPp2
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hkeq
      exact hP.ne_top (Ideal.absNorm_eq_one_iff.mp hkeq)
    have hle2' : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤
        P ^ 2 := by
      simpa [Ideal.map_span, Set.image_singleton] using hle2
    have hno3 : ¬ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤
        P ^ 3 :=
      not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow hp habsp hkeq hk0
    have hunram : ¬ Algebra.IsUnramifiedAt ℤ P :=
      not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ hp hpmemP hPbot hle2'
        hno3
    have hPdiff : P ∣ differentIdeal ℤ (𝓞 K) := dvd_differentIdeal_iff.mpr hunram
    have habsP24 : Ideal.absNorm P ∣ 24 := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPdiff)
      rw [NumberField.absNorm_differentIdeal (K := K), numberField_discr_eq] at h
      simpa using h
    have hpdvd : p ∣ 24 := (hkeq ▸ dvd_pow_self p hk0).trans habsP24
    exact eq_two_or_eq_three_of_prime_dvd_twentyfour hp hpdvd
  · rintro (rfl | rfl)
    · refine ⟨primeAboveTwo, isPrime_primeAboveTwo, ?_⟩
      have hcast : ((2 : ℕ) : 𝓞 K) = (2 : 𝓞 K) := by norm_num
      rw [hcast, span_two_eq]
    · refine ⟨primeAboveThree, isPrime_primeAboveThree, ?_⟩
      have hcast : ((3 : ℕ) : 𝓞 K) = (3 : 𝓞 K) := by norm_num
      rw [hcast, span_three_eq]

/-- The split prime `(1 + θ)` over `7` is unramified. -/
theorem ramificationIdx_span_one_add_theta :
    (Ideal.span {(7 : ℤ)}).ramificationIdx (Ideal.span {1 + thetaInt}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    change Ideal.span {(7 : 𝓞 K)} ≤ Ideal.span {1 + thetaInt}
    rw [span_seven_eq]
    exact Ideal.mul_le_right
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(7 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {1 + thetaInt}, isPrime_span_one_add_theta, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h := (ramified_iff 7 (by norm_num)).mp hram
    omega

/-- The split prime `(1 - θ)` over `7` is unramified. -/
theorem ramificationIdx_span_one_sub_theta :
    (Ideal.span {(7 : ℤ)}).ramificationIdx (Ideal.span {1 - thetaInt}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    change Ideal.span {(7 : 𝓞 K)} ≤ Ideal.span {1 - thetaInt}
    rw [span_seven_eq]
    exact Ideal.mul_le_left
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(7 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {1 - thetaInt}, isPrime_span_one_sub_theta, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h := (ramified_iff 7 (by norm_num)).mp hram
    omega

/-- The split prime `(5, θ - 2)` is unramified. -/
theorem ramificationIdx_primeAboveFiveSubTwo :
    (Ideal.span {(5 : ℤ)}).ramificationIdx primeAboveFiveSubTwo = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    change Ideal.span {(5 : 𝓞 K)} ≤ primeAboveFiveSubTwo
    rw [primeAboveFiveSubTwo]
    exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span (by simp))
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(5 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨primeAboveFiveSubTwo, isPrime_primeAboveFiveSubTwo, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h := (ramified_iff 5 (by norm_num)).mp hram
    omega

/-- The split prime `(5, θ + 2)` is unramified. -/
theorem ramificationIdx_primeAboveFiveAddTwo :
    (Ideal.span {(5 : ℤ)}).ramificationIdx primeAboveFiveAddTwo = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    change Ideal.span {(5 : 𝓞 K)} ≤ primeAboveFiveAddTwo
    rw [primeAboveFiveAddTwo]
    exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span (by simp))
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(5 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨primeAboveFiveAddTwo, isPrime_primeAboveFiveAddTwo, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h := (ramified_iff 5 (by norm_num)).mp hram
    omega

/-- The inert prime `(13)` is unramified. -/
theorem ramificationIdx_span_thirteen :
    (Ideal.span {(13 : ℤ)}).ramificationIdx (Ideal.span {(13 : 𝓞 K)}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    simp
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(13 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {(13 : 𝓞 K)}, isPrime_span_thirteen, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h := (ramified_iff 13 (by norm_num)).mp hram
    omega

end NumberField.SqrtNegSix
