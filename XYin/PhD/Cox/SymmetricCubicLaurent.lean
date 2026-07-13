/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.LaurentPolynomialEvaluation
import XYin.PhD.Cox.ModularPolynomial

/-!
# Finite Laurent detection for symmetric bivariate cubics

A symmetric bivariate polynomial of bidegree at most three has ten independent coefficients.
When two Laurent series have respective orders `-9` and `-3` and unit leading coefficients,
the ten corresponding triangular leading exponents detect whether the polynomial is zero.
-/

noncomputable section

namespace Cox

private theorem coeff_comm_of_swap_eq {K : Type*} [CommRing K]
    (P : BivariatePolynomial K) (hsymm : Polynomial.Bivariate.swap P = P) (i j : ℕ) :
    (P.coeff i).coeff j = (P.coeff j).coeff i := by
  have h := congrArg (fun Q : BivariatePolynomial K ↦ (Q.coeff i).coeff j) hsymm
  change ((Polynomial.Bivariate.swap P).coeff i).coeff j = (P.coeff i).coeff j at h
  rw [BivariatePolynomial.coeff_coeff_swap] at h
  exact h.symm

private def symmetricCubicExpansion {K : Type*} [CommRing K]
    (P : BivariatePolynomial K) : BivariatePolynomial K :=
  let c (i j : ℕ) : BivariatePolynomial K :=
    Polynomial.monomial i (Polynomial.monomial j ((P.coeff i).coeff j))
  c 0 0 +
    (c 1 0 + Polynomial.monomial 0 (Polynomial.monomial 1 ((P.coeff 1).coeff 0))) +
    c 1 1 +
    (c 2 0 + Polynomial.monomial 0 (Polynomial.monomial 2 ((P.coeff 2).coeff 0))) +
    (c 2 1 + Polynomial.monomial 1 (Polynomial.monomial 2 ((P.coeff 2).coeff 1))) +
    c 2 2 +
    (c 3 0 + Polynomial.monomial 0 (Polynomial.monomial 3 ((P.coeff 3).coeff 0))) +
    (c 3 1 + Polynomial.monomial 1 (Polynomial.monomial 3 ((P.coeff 3).coeff 1))) +
    (c 3 2 + Polynomial.monomial 2 (Polynomial.monomial 3 ((P.coeff 3).coeff 2))) +
    c 3 3

private theorem symmetricCubicExpansion_coeff_zero {K : Type*} [CommRing K]
    (P : BivariatePolynomial K) (hinner : (P.coeff 0).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P) :
    (symmetricCubicExpansion P).coeff 0 = P.coeff 0 := by
  apply Polynomial.ext
  intro j
  by_cases hj : j ≤ 3
  · interval_cases j <;>
      simp [symmetricCubicExpansion, Polynomial.coeff_monomial,
        coeff_comm_of_swap_eq P hsymm]
  · have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (hinner.trans_lt (lt_of_not_ge hj))
    have hj0 : j ≠ 0 := by lia
    have hj1 : j ≠ 1 := by lia
    have hj2 : j ≠ 2 := by lia
    have hj3 : j ≠ 3 := by lia
    rw [hz]
    simp [symmetricCubicExpansion, Polynomial.coeff_monomial, Polynomial.coeff_C, hj0,
      hj1, hj2, hj3, eq_comm]

private theorem symmetricCubicExpansion_coeff_one {K : Type*} [CommRing K]
    (P : BivariatePolynomial K) (hinner : (P.coeff 1).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P) :
    (symmetricCubicExpansion P).coeff 1 = P.coeff 1 := by
  apply Polynomial.ext
  intro j
  by_cases hj : j ≤ 3
  · interval_cases j <;>
      simp [symmetricCubicExpansion, Polynomial.coeff_monomial,
        coeff_comm_of_swap_eq P hsymm]
  · have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (hinner.trans_lt (lt_of_not_ge hj))
    have hj0 : j ≠ 0 := by lia
    have hj1 : j ≠ 1 := by lia
    have hj2 : j ≠ 2 := by lia
    have hj3 : j ≠ 3 := by lia
    rw [hz]
    simp [symmetricCubicExpansion, Polynomial.coeff_monomial, Polynomial.coeff_C, hj0,
      hj1, hj2, hj3, eq_comm]

private theorem symmetricCubicExpansion_coeff_two {K : Type*} [CommRing K]
    (P : BivariatePolynomial K) (hinner : (P.coeff 2).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P) :
    (symmetricCubicExpansion P).coeff 2 = P.coeff 2 := by
  apply Polynomial.ext
  intro j
  by_cases hj : j ≤ 3
  · interval_cases j <;>
      simp [symmetricCubicExpansion, Polynomial.coeff_monomial,
        coeff_comm_of_swap_eq P hsymm]
  · have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (hinner.trans_lt (lt_of_not_ge hj))
    have hj0 : j ≠ 0 := by lia
    have hj1 : j ≠ 1 := by lia
    have hj2 : j ≠ 2 := by lia
    have hj3 : j ≠ 3 := by lia
    rw [hz]
    simp [symmetricCubicExpansion, Polynomial.coeff_monomial, Polynomial.coeff_C, hj0,
      hj1, hj2, hj3, eq_comm]

private theorem symmetricCubicExpansion_coeff_three {K : Type*} [CommRing K]
    (P : BivariatePolynomial K) (hinner : (P.coeff 3).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P) :
    (symmetricCubicExpansion P).coeff 3 = P.coeff 3 := by
  apply Polynomial.ext
  intro j
  by_cases hj : j ≤ 3
  · interval_cases j <;>
      simp [symmetricCubicExpansion, Polynomial.coeff_monomial,
        coeff_comm_of_swap_eq P hsymm]
  · have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (hinner.trans_lt (lt_of_not_ge hj))
    have hj0 : j ≠ 0 := by lia
    have hj1 : j ≠ 1 := by lia
    have hj2 : j ≠ 2 := by lia
    have hj3 : j ≠ 3 := by lia
    rw [hz]
    simp [symmetricCubicExpansion, Polynomial.coeff_monomial, Polynomial.coeff_C, hj0,
      hj1, hj2, hj3, eq_comm]

private theorem eq_symmetricCubicExpansion {K : Type*} [CommRing K]
    (P : BivariatePolynomial K) (houter : P.natDegree ≤ 3)
    (hinner : ∀ i, (P.coeff i).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P) :
    P = symmetricCubicExpansion P := by
  apply Polynomial.ext
  intro i
  by_cases hi : i ≤ 3
  · interval_cases i
    · exact (symmetricCubicExpansion_coeff_zero P (hinner 0) hsymm).symm
    · exact (symmetricCubicExpansion_coeff_one P (hinner 1) hsymm).symm
    · exact (symmetricCubicExpansion_coeff_two P (hinner 2) hsymm).symm
    · exact (symmetricCubicExpansion_coeff_three P (hinner 3) hsymm).symm
  · have hz : P.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (houter.trans_lt (lt_of_not_ge hi))
    have hi0 : i ≠ 0 := by lia
    have hi1 : i ≠ 1 := by lia
    have hi2 : i ≠ 2 := by lia
    have hi3 : i ≠ 3 := by lia
    rw [hz]
    simp [symmetricCubicExpansion, Polynomial.coeff_monomial, Polynomial.coeff_C, hi0, hi1,
      hi2, hi3, eq_comm]

private def bivariateLaurentEvalHom {K : Type*} [Field K]
    (T J : LaurentSeries K) : BivariatePolynomial K →+* LaurentSeries K :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (HahnSeries.C : K →+* LaurentSeries K) J) T

private def bivariateLaurentEval {K : Type*} [Field K]
    (T J : LaurentSeries K) (P : BivariatePolynomial K) : LaurentSeries K :=
  bivariateLaurentEvalHom T J P

@[simp]
private theorem bivariateLaurentEval_add {K : Type*} [Field K]
    (T J : LaurentSeries K) (P Q : BivariatePolynomial K) :
    bivariateLaurentEval T J (P + Q) =
      bivariateLaurentEval T J P + bivariateLaurentEval T J Q := by
  exact map_add (bivariateLaurentEvalHom T J) P Q

@[simp]
private theorem bivariateLaurentEval_monomial {K : Type*} [Field K]
    (T J : LaurentSeries K) (i j : ℕ) (a : K) :
    bivariateLaurentEval T J (Polynomial.monomial i (Polynomial.monomial j a)) =
      HahnSeries.C a * T ^ i * J ^ j := by
  simp only [bivariateLaurentEval, bivariateLaurentEvalHom,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
  ring

private def symmetricBivariateMonomial {K : Type*} [Field K]
    (i j : ℕ) (a : K) : BivariatePolynomial K :=
  if i = j then Polynomial.monomial i (Polynomial.monomial j a)
  else Polynomial.monomial i (Polynomial.monomial j a) +
    Polynomial.monomial j (Polynomial.monomial i a)

private def cubicWeight (i j : ℕ) : ℤ := 9 * (i : ℤ) + 3 * (j : ℤ)

private theorem laurentMonomial_order {K : Type*} [Field K]
    (T J : LaurentSeries K) (hT : T.order = -(9 : ℤ)) (hJ : J.order = -(3 : ℤ))
    (i j : ℕ) : (T ^ i * J ^ j).order = -(cubicWeight i j) := by
  have hTne : T ≠ 0 := by
    intro hz
    subst T
    simp at hT
  have hJne : J ≠ 0 := by
    intro hz
    subst J
    simp at hJ
  rw [HahnSeries.order_mul (pow_ne_zero _ hTne) (pow_ne_zero _ hJne),
    HahnSeries.order_pow, HahnSeries.order_pow, hT, hJ]
  simp [cubicWeight]
  ring

private theorem laurentMonomial_leadingCoeff {K : Type*} [Field K]
    (T J : LaurentSeries K) (hT : T.leadingCoeff = 1) (hJ : J.leadingCoeff = 1)
    (i j : ℕ) : (T ^ i * J ^ j).leadingCoeff = 1 := by
  rw [HahnSeries.leadingCoeff_mul,
    laurentSeries_pow_leadingCoeff_of_eq_one T hT,
    laurentSeries_pow_leadingCoeff_of_eq_one J hJ, one_mul]

private theorem laurentMonomial_coeff_self {K : Type*} [Field K]
    (T J : LaurentSeries K) (hTorder : T.order = -(9 : ℤ))
    (hJorder : J.order = -(3 : ℤ)) (hTlead : T.leadingCoeff = 1)
    (hJlead : J.leadingCoeff = 1) (i j : ℕ) :
    (T ^ i * J ^ j).coeff (-(cubicWeight i j)) = 1 := by
  rw [← laurentMonomial_order T J hTorder hJorder,
    ← HahnSeries.leadingCoeff_eq,
    laurentMonomial_leadingCoeff T J hTlead hJlead]

private theorem laurentMonomial_coeff_zero_of_weight_lt {K : Type*} [Field K]
    (T J : LaurentSeries K) (hT : T.order = -(9 : ℤ)) (hJ : J.order = -(3 : ℤ))
    (i j r s : ℕ) (hweight : cubicWeight i j < cubicWeight r s) :
    (T ^ i * J ^ j).coeff (-(cubicWeight r s)) = 0 := by
  apply HahnSeries.coeff_eq_zero_of_lt_order
  rw [laurentMonomial_order T J hT hJ]
  exact neg_lt_neg hweight

private def symmetricLaurentMonomial {K : Type*} [Field K]
    (T J : LaurentSeries K) (i j : ℕ) : LaurentSeries K :=
  if i = j then T ^ i * J ^ j else T ^ i * J ^ j + T ^ j * J ^ i

private theorem bivariateLaurentEval_symmetricBivariateMonomial
    {K : Type*} [Field K] (T J : LaurentSeries K) (i j : ℕ) (a : K) :
    bivariateLaurentEval T J (symmetricBivariateMonomial i j a) =
      HahnSeries.C a * symmetricLaurentMonomial T J i j := by
  by_cases hij : i = j
  · subst j
    simp [symmetricBivariateMonomial, symmetricLaurentMonomial,
      bivariateLaurentEval_monomial]
    simp only [← HahnSeries.C_mul_eq_smul]
    ring
  · simp only [symmetricBivariateMonomial, symmetricLaurentMonomial, if_neg hij,
      bivariateLaurentEval_add, bivariateLaurentEval_monomial]
    ring

private theorem symmetricLaurentMonomial_coeff_self {K : Type*} [Field K]
    (T J : LaurentSeries K) (hTorder : T.order = -(9 : ℤ))
    (hJorder : J.order = -(3 : ℤ)) (hTlead : T.leadingCoeff = 1)
    (hJlead : J.leadingCoeff = 1) (i j : ℕ) (hji : j ≤ i) :
    (symmetricLaurentMonomial T J i j).coeff (-(cubicWeight i j)) = 1 := by
  by_cases hij : i = j
  · subst j
    simpa [symmetricLaurentMonomial] using
      laurentMonomial_coeff_self T J hTorder hJorder hTlead hJlead i i
  · rw [symmetricLaurentMonomial, if_neg hij, HahnSeries.coeff_add,
      laurentMonomial_coeff_self T J hTorder hJorder hTlead hJlead]
    rw [laurentMonomial_coeff_zero_of_weight_lt T J hTorder hJorder]
    · simp
    · simp only [cubicWeight]
      lia

private theorem symmetricLaurentMonomial_coeff_zero_of_weight_lt
    {K : Type*} [Field K] (T J : LaurentSeries K)
    (hT : T.order = -(9 : ℤ)) (hJ : J.order = -(3 : ℤ))
    (i j r s : ℕ) (hji : j ≤ i) (hweight : cubicWeight i j < cubicWeight r s) :
    (symmetricLaurentMonomial T J i j).coeff (-(cubicWeight r s)) = 0 := by
  rw [symmetricLaurentMonomial]
  split_ifs
  · exact laurentMonomial_coeff_zero_of_weight_lt T J hT hJ i j r s hweight
  · rw [HahnSeries.coeff_add,
      laurentMonomial_coeff_zero_of_weight_lt T J hT hJ i j r s hweight,
      laurentMonomial_coeff_zero_of_weight_lt T J hT hJ j i r s]
    · simp
    · simp only [cubicWeight] at hweight ⊢
      lia

private def cubicI : Fin 10 → ℕ := ![0, 1, 1, 2, 2, 2, 3, 3, 3, 3]

private def cubicJ : Fin 10 → ℕ := ![0, 0, 1, 0, 1, 2, 0, 1, 2, 3]

private def cubicCoeff {K : Type*} [Field K]
    (P : BivariatePolynomial K) (k : Fin 10) : K :=
  (P.coeff (cubicI k)).coeff (cubicJ k)

private def cubicBasis {K : Type*} [Field K]
    (T J : LaurentSeries K) (k : Fin 10) : LaurentSeries K :=
  symmetricLaurentMonomial T J (cubicI k) (cubicJ k)

private def symmetricCubicLaurentExpansionFin {K : Type*} [Field K]
    (T J : LaurentSeries K) (P : BivariatePolynomial K) : LaurentSeries K :=
  ∑ k : Fin 10, HahnSeries.C (cubicCoeff P k) * cubicBasis T J k

private def symmetricCubicPolynomialExpansionFin {K : Type*} [Field K]
    (P : BivariatePolynomial K) : BivariatePolynomial K :=
  ∑ k : Fin 10, symmetricBivariateMonomial (cubicI k) (cubicJ k) (cubicCoeff P k)

private theorem symmetricCubicExpansion_eq_fin {K : Type*} [Field K]
    (P : BivariatePolynomial K) :
    symmetricCubicExpansion P = symmetricCubicPolynomialExpansionFin P := by
  simp [symmetricCubicExpansion, symmetricCubicPolynomialExpansionFin,
    symmetricBivariateMonomial, cubicCoeff, cubicI, cubicJ, Fin.sum_univ_succ]
  abel

private theorem cubicJ_le_cubicI (k : Fin 10) : cubicJ k ≤ cubicI k := by
  fin_cases k <;> norm_num [cubicI, cubicJ]

private theorem cubicWeight_strictMono :
    StrictMono (fun k : Fin 10 ↦ cubicWeight (cubicI k) (cubicJ k)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro k
  fin_cases k <;> simp [cubicI, cubicJ, cubicWeight]

private theorem cubicBasis_coeff_self {K : Type*} [Field K]
    (T J : LaurentSeries K) (hTorder : T.order = -(9 : ℤ))
    (hJorder : J.order = -(3 : ℤ)) (hTlead : T.leadingCoeff = 1)
    (hJlead : J.leadingCoeff = 1) (k : Fin 10) :
    (cubicBasis T J k).coeff (-(cubicWeight (cubicI k) (cubicJ k))) = 1 := by
  exact symmetricLaurentMonomial_coeff_self T J hTorder hJorder hTlead hJlead
    (cubicI k) (cubicJ k) (cubicJ_le_cubicI k)

private theorem cubicBasis_coeff_zero_of_lt {K : Type*} [Field K]
    (T J : LaurentSeries K) (hT : T.order = -(9 : ℤ))
    (hJ : J.order = -(3 : ℤ)) {k l : Fin 10} (hkl : k < l) :
    (cubicBasis T J k).coeff (-(cubicWeight (cubicI l) (cubicJ l))) = 0 := by
  exact symmetricLaurentMonomial_coeff_zero_of_weight_lt T J hT hJ
    (cubicI k) (cubicJ k) (cubicI l) (cubicJ l) (cubicJ_le_cubicI k)
      (cubicWeight_strictMono hkl)

private theorem symmetricCubicLaurentExpansionFin_coeff_eq
    {K : Type*} [Field K] (T J : LaurentSeries K) (P : BivariatePolynomial K)
    (hTorder : T.order = -(9 : ℤ)) (hJorder : J.order = -(3 : ℤ))
    (hTlead : T.leadingCoeff = 1) (hJlead : J.leadingCoeff = 1) (k : Fin 10)
    (hzero : ∀ l : Fin 10, k < l → cubicCoeff P l = 0) :
    (symmetricCubicLaurentExpansionFin T J P).coeff
        (-(cubicWeight (cubicI k) (cubicJ k))) = cubicCoeff P k := by
  classical
  rw [symmetricCubicLaurentExpansionFin, HahnSeries.coeff_sum]
  rw [Fintype.sum_eq_single k]
  · rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
      cubicBasis_coeff_self T J hTorder hJorder hTlead hJlead]
    simp
  · intro l hl
    rcases lt_or_gt_of_ne hl with hlk | hkl
    · rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
        cubicBasis_coeff_zero_of_lt T J hTorder hJorder hlk]
      simp
    · rw [hzero l hkl]
      simp

private theorem bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin
    {K : Type*} [Field K] (T J : LaurentSeries K) (P : BivariatePolynomial K)
    (houter : P.natDegree ≤ 3) (hinner : ∀ i, (P.coeff i).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P) :
    bivariateLaurentEval T J P = symmetricCubicLaurentExpansionFin T J P := by
  conv_lhs =>
    rw [eq_symmetricCubicExpansion P houter hinner hsymm,
      symmetricCubicExpansion_eq_fin]
  rw [symmetricCubicPolynomialExpansionFin, symmetricCubicLaurentExpansionFin]
  change bivariateLaurentEvalHom T J (∑ k : Fin 10,
    symmetricBivariateMonomial (cubicI k) (cubicJ k) (cubicCoeff P k)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact bivariateLaurentEval_symmetricBivariateMonomial T J
    (cubicI k) (cubicJ k) (cubicCoeff P k)

private theorem cubicCoeff_eq_zero_of_laurent_coeff
    {K : Type*} [Field K] (T J : LaurentSeries K)
    (hTorder : T.order = -(9 : ℤ)) (hJorder : J.order = -(3 : ℤ))
    (hTlead : T.leadingCoeff = 1) (hJlead : J.leadingCoeff = 1)
    (P : BivariatePolynomial K) (houter : P.natDegree ≤ 3)
    (hinner : ∀ i, (P.coeff i).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P)
    (hcoeff : ∀ k : Fin 10,
      (bivariateLaurentEval T J P).coeff
          (-(cubicWeight (cubicI k) (cubicJ k))) = 0) :
    ∀ k, cubicCoeff P k = 0 := by
  have hcurrent (k : Fin 10)
      (hzero : ∀ l : Fin 10, k < l → cubicCoeff P l = 0) : cubicCoeff P k = 0 := by
    have h := hcoeff k
    rw [bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin
        T J P houter hinner hsymm,
      symmetricCubicLaurentExpansionFin_coeff_eq T J P hTorder hJorder hTlead hJlead
        k hzero] at h
    exact h
  have hfrom : ∀ k l : Fin 10, k ≤ l → cubicCoeff P l = 0 := by
    intro k
    induction k using Fin.reverseInduction with
    | last =>
        intro l hle
        have hl : l = Fin.last 9 := le_antisymm (Fin.le_last l) hle
        subst l
        exact hcurrent (Fin.last 9) <| by
          intro l hlt
          exact (not_lt_of_ge (Fin.le_last l) hlt).elim
    | cast i ih =>
        have hk : cubicCoeff P i.castSucc = 0 := hcurrent i.castSucc <| by
          intro l hlt
          exact ih l (Fin.castSucc_lt_iff_succ_le.mp hlt)
        intro l hle
        by_cases hl : l = i.castSucc
        · simpa [hl] using hk
        · exact ih l <| Fin.castSucc_lt_iff_succ_le.mp (lt_of_le_of_ne hle (Ne.symm hl))
  exact fun k ↦ hfrom 0 k (Fin.zero_le k)

private theorem eq_zero_of_cubicCoeff_eq_zero {K : Type*} [Field K]
    (P : BivariatePolynomial K) (houter : P.natDegree ≤ 3)
    (hinner : ∀ i, (P.coeff i).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P)
    (hall : ∀ k, cubicCoeff P k = 0) : P = 0 := by
  have h00 := hall (0 : Fin 10)
  have h10 := hall (1 : Fin 10)
  have h11 := hall (2 : Fin 10)
  have h20 := hall (3 : Fin 10)
  have h21 := hall (4 : Fin 10)
  have h22 := hall (5 : Fin 10)
  have h30 := hall (6 : Fin 10)
  have h31 := hall (7 : Fin 10)
  have h32 := hall (8 : Fin 10)
  have h33 := hall (9 : Fin 10)
  simp [cubicCoeff, cubicI, cubicJ] at h00 h10 h11 h20 h21 h22 h30 h31 h32 h33
  rw [eq_symmetricCubicExpansion P houter hinner hsymm]
  simp [symmetricCubicExpansion, h00, h10, h11, h20, h21, h22, h30, h31, h32, h33]

private theorem symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux
    {K : Type*} [Field K] (T J : LaurentSeries K)
    (hTorder : T.order = -(9 : ℤ)) (hJorder : J.order = -(3 : ℤ))
    (hTlead : T.leadingCoeff = 1) (hJlead : J.leadingCoeff = 1)
    (P : BivariatePolynomial K) (houter : P.natDegree ≤ 3)
    (hinner : ∀ i, (P.coeff i).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P)
    (hcoeff : ∀ k : Fin 10,
      (bivariateLaurentEval T J P).coeff
          (-(cubicWeight (cubicI k) (cubicJ k))) = 0) :
    P = 0 := by
  apply eq_zero_of_cubicCoeff_eq_zero P houter hinner hsymm
  exact cubicCoeff_eq_zero_of_laurent_coeff
    T J hTorder hJorder hTlead hJlead P houter hinner hsymm hcoeff

/-- A symmetric bivariate cubic is detected by its ten triangular Laurent coefficients. -/
theorem symmetric_bidegree_three_eq_zero_of_laurent_coeff
    {K : Type*} [Field K] (T J : LaurentSeries K)
    (hTorder : T.order = -(9 : ℤ)) (hJorder : J.order = -(3 : ℤ))
    (hTlead : T.leadingCoeff = 1) (hJlead : J.leadingCoeff = 1)
    (P : BivariatePolynomial K) (houter : P.natDegree ≤ 3)
    (hinner : ∀ i, (P.coeff i).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P)
    (hcoeff :
      let E := P.eval₂
        (Polynomial.eval₂RingHom (HahnSeries.C : K →+* LaurentSeries K) J) T
      E.coeff 0 = 0 ∧ E.coeff (-9) = 0 ∧ E.coeff (-12) = 0 ∧
      E.coeff (-18) = 0 ∧ E.coeff (-21) = 0 ∧ E.coeff (-24) = 0 ∧
      E.coeff (-27) = 0 ∧ E.coeff (-30) = 0 ∧ E.coeff (-33) = 0 ∧
      E.coeff (-36) = 0) :
    P = 0 := by
  rcases hcoeff with ⟨h0, h9, h12, h18, h21, h24, h27, h30, h33, h36⟩
  apply symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux
    T J hTorder hJorder hTlead hJlead P houter hinner hsymm
  intro k
  fin_cases k <;>
    norm_num [bivariateLaurentEval, bivariateLaurentEvalHom, cubicWeight, cubicI, cubicJ] <;>
    assumption

end Cox
