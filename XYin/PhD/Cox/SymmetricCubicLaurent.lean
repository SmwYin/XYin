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

open scoped Polynomial.Bivariate

noncomputable section

namespace Cox

section CommRing

variable {K : Type*} [CommRing K]

private def symmetricCubicExpansion (P : K[X][Y]) : K[X][Y] :=
  let c (i j : ℕ) : K[X][Y] :=
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

private theorem symmetricCubicExpansion_coeff_aux
    (P : K[X][Y]) (i : ℕ) (hi : i ≤ 3)
    (hinner : (P.coeff i).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P) :
    (symmetricCubicExpansion P).coeff i = P.coeff i := by
  have hcomm (i j : ℕ) : (P.coeff i).coeff j = (P.coeff j).coeff i := by
    rw [← Polynomial.Bivariate.coeff_coeff_swap, hsymm]
  ext j
  by_cases hj : j ≤ 3
  · interval_cases i <;> interval_cases j <;>
      simp [symmetricCubicExpansion, Polynomial.coeff_monomial, hcomm]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hinner.trans_lt (lt_of_not_ge hj))]
    have hj0 : j ≠ 0 := by omega
    have hj1 : j ≠ 1 := by omega
    have hj2 : j ≠ 2 := by omega
    have hj3 : j ≠ 3 := by omega
    interval_cases i <;>
      simp [symmetricCubicExpansion, Polynomial.coeff_monomial,
        Polynomial.coeff_C, hj0, hj1, hj2, hj3, eq_comm]

private theorem eq_symmetricCubicExpansion
    (P : K[X][Y]) (houter : P.natDegree ≤ 3)
    (hinner : ∀ i, (P.coeff i).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P) :
    P = symmetricCubicExpansion P := by
  ext1 i
  by_cases hi : i ≤ 3
  · exact (symmetricCubicExpansion_coeff_aux P i hi (hinner i) hsymm).symm
  · have hz : P.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (houter.trans_lt (lt_of_not_ge hi))
    have hi0 : i ≠ 0 := by lia
    have hi1 : i ≠ 1 := by lia
    have hi2 : i ≠ 2 := by lia
    have hi3 : i ≠ 3 := by lia
    rw [hz]
    simp [symmetricCubicExpansion, Polynomial.coeff_monomial, Polynomial.coeff_C, hi0, hi1,
      hi2, hi3, eq_comm]

private def symmetricBivariateMonomial (i j : ℕ) (a : K) : K[X][Y] :=
  if i = j then Polynomial.monomial i (Polynomial.monomial j a)
  else Polynomial.monomial i (Polynomial.monomial j a) +
    Polynomial.monomial j (Polynomial.monomial i a)

private def cubicI : Fin 10 → ℕ := ![0, 1, 1, 2, 2, 2, 3, 3, 3, 3]

private def cubicJ : Fin 10 → ℕ := ![0, 0, 1, 0, 1, 2, 0, 1, 2, 3]

private def cubicCoeff (P : K[X][Y]) (k : Fin 10) : K :=
  (P.coeff (cubicI k)).coeff (cubicJ k)

private def symmetricCubicPolynomialExpansionFin (P : K[X][Y]) : K[X][Y] :=
  ∑ k : Fin 10, symmetricBivariateMonomial (cubicI k) (cubicJ k) (cubicCoeff P k)

private theorem symmetricCubicExpansion_eq_fin (P : K[X][Y]) :
    symmetricCubicExpansion P = symmetricCubicPolynomialExpansionFin P := by
  simp [symmetricCubicExpansion, symmetricCubicPolynomialExpansionFin,
    symmetricBivariateMonomial, cubicCoeff, cubicI, cubicJ, Fin.sum_univ_succ]
  abel

private theorem eq_zero_of_cubicCoeff_eq_zero
    (P : K[X][Y]) (houter : P.natDegree ≤ 3)
    (hinner : ∀ i, (P.coeff i).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P)
    (hall : ∀ k, cubicCoeff P k = 0) : P = 0 := by
  rw [eq_symmetricCubicExpansion P houter hinner hsymm, symmetricCubicExpansion_eq_fin]
  simp [symmetricCubicPolynomialExpansionFin, hall, symmetricBivariateMonomial]

private def symmetricLaurentMonomial (T J : LaurentSeries K) (i j : ℕ) : LaurentSeries K :=
  if i = j then T ^ i * J ^ j else T ^ i * J ^ j + T ^ j * J ^ i

private theorem bivariateLaurentEvalHom_symmetricBivariateMonomial
    (T J : LaurentSeries K) (i j : ℕ) (a : K) :
    bivariateLaurentEvalHom T J (symmetricBivariateMonomial i j a) =
      HahnSeries.C a * symmetricLaurentMonomial T J i j := by
  by_cases hij : i = j
  · subst j
    simp only [symmetricBivariateMonomial, symmetricLaurentMonomial, if_true,
      bivariateLaurentEvalHom_monomial]
    ring
  · simp only [symmetricBivariateMonomial, symmetricLaurentMonomial, if_neg hij, map_add,
      bivariateLaurentEvalHom_monomial]
    ring

private def cubicBasis (T J : LaurentSeries K) (k : Fin 10) : LaurentSeries K :=
  symmetricLaurentMonomial T J (cubicI k) (cubicJ k)

private def symmetricCubicLaurentExpansionFin (T J : LaurentSeries K)
    (P : K[X][Y]) : LaurentSeries K :=
  ∑ k : Fin 10, HahnSeries.C (cubicCoeff P k) * cubicBasis T J k

private theorem bivariateLaurentEvalHom_eq_symmetricCubicLaurentExpansionFin
    (T J : LaurentSeries K) (P : K[X][Y])
    (houter : P.natDegree ≤ 3) (hinner : ∀ i, (P.coeff i).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P) :
    bivariateLaurentEvalHom T J P = symmetricCubicLaurentExpansionFin T J P := by
  conv_lhs =>
    rw [eq_symmetricCubicExpansion P houter hinner hsymm, symmetricCubicExpansion_eq_fin]
  rw [symmetricCubicPolynomialExpansionFin, symmetricCubicLaurentExpansionFin, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦
    bivariateLaurentEvalHom_symmetricBivariateMonomial T J (cubicI k) (cubicJ k) (cubicCoeff P k)

end CommRing

private def cubicWeight (i j : ℕ) : ℤ := 9 * (i : ℤ) + 3 * (j : ℤ)

private theorem cubicJ_le_cubicI (k : Fin 10) : cubicJ k ≤ cubicI k := by
  fin_cases k <;> norm_num [cubicI, cubicJ]

private theorem cubicI_le_three (k : Fin 10) : cubicI k ≤ 3 := by
  fin_cases k <;> norm_num [cubicI]

private theorem cubicWeight_strictMono :
    StrictMono (fun k : Fin 10 ↦ cubicWeight (cubicI k) (cubicJ k)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro k
  fin_cases k <;> simp [cubicI, cubicJ, cubicWeight]

variable {K : Type*} [CommRing K] [IsDomain K]

private theorem laurentMonomial_order
    (T J : LaurentSeries K) (hT : T.order = -(9 : ℤ)) (hJ : J.order = -(3 : ℤ))
    (i j : ℕ) : (T ^ i * J ^ j).order = -(cubicWeight i j) := by
  have hTne : T ≠ 0 := by
    rintro rfl
    simp at hT
  have hJne : J ≠ 0 := by
    rintro rfl
    simp at hJ
  rw [HahnSeries.order_mul (pow_ne_zero _ hTne) (pow_ne_zero _ hJne),
    HahnSeries.order_pow, HahnSeries.order_pow, hT, hJ]
  simp [cubicWeight]
  ring

private theorem laurentMonomial_coeff_self
    (T J : LaurentSeries K) (hTorder : T.order = -(9 : ℤ))
    (hJorder : J.order = -(3 : ℤ)) (hTlead : T.leadingCoeff = 1)
    (hJlead : J.leadingCoeff = 1) (i j : ℕ) :
    (T ^ i * J ^ j).coeff (-(cubicWeight i j)) = 1 := by
  rw [← laurentMonomial_order T J hTorder hJorder, ← HahnSeries.leadingCoeff_eq]
  simp [hTlead, hJlead]

private theorem laurentMonomial_coeff_zero_of_weight_lt
    (T J : LaurentSeries K) (hT : T.order = -(9 : ℤ)) (hJ : J.order = -(3 : ℤ))
    (i j r s : ℕ) (hweight : cubicWeight i j < cubicWeight r s) :
    (T ^ i * J ^ j).coeff (-(cubicWeight r s)) = 0 := by
  apply HahnSeries.coeff_eq_zero_of_lt_order
  rw [laurentMonomial_order T J hT hJ]
  exact neg_lt_neg hweight

private theorem symmetricLaurentMonomial_coeff_self
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
    (T J : LaurentSeries K)
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

private theorem cubicBasis_coeff_self
    (T J : LaurentSeries K) (hTorder : T.order = -(9 : ℤ))
    (hJorder : J.order = -(3 : ℤ)) (hTlead : T.leadingCoeff = 1)
    (hJlead : J.leadingCoeff = 1) (k : Fin 10) :
    (cubicBasis T J k).coeff (-(cubicWeight (cubicI k) (cubicJ k))) = 1 :=
  symmetricLaurentMonomial_coeff_self T J hTorder hJorder hTlead hJlead
    (cubicI k) (cubicJ k) (cubicJ_le_cubicI k)

private theorem cubicBasis_coeff_zero_of_lt
    (T J : LaurentSeries K) (hT : T.order = -(9 : ℤ))
    (hJ : J.order = -(3 : ℤ)) {k l : Fin 10} (hkl : k < l) :
    (cubicBasis T J k).coeff (-(cubicWeight (cubicI l) (cubicJ l))) = 0 :=
  symmetricLaurentMonomial_coeff_zero_of_weight_lt T J hT hJ
    (cubicI k) (cubicJ k) (cubicI l) (cubicJ l) (cubicJ_le_cubicI k)
      (cubicWeight_strictMono hkl)

private theorem symmetricCubicLaurentExpansionFin_coeff_eq
    (T J : LaurentSeries K) (P : K[X][Y])
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

/-- A symmetric bivariate cubic is detected by its ten triangular Laurent coefficients: if two
Laurent series `T`, `J` of orders `-9`, `-3` with leading coefficients one satisfy
`P(T, J) = O(t^(-(9i + 3j)))` at the ten exponents `0 ≤ j ≤ i ≤ 3`, then `P = 0`. Here
`P(T, J) = bivariateLaurentEvalHom T J P` substitutes `T` for the outer variable `Y` and `J` for
the inner variable `C X`. -/
theorem symmetric_bidegree_three_eq_zero_of_laurent_coeff
    (T J : LaurentSeries K)
    (hTorder : T.order = -(9 : ℤ)) (hJorder : J.order = -(3 : ℤ))
    (hTlead : T.leadingCoeff = 1) (hJlead : J.leadingCoeff = 1)
    (P : K[X][Y]) (houter : P.natDegree ≤ 3)
    (hinner : ∀ i, (P.coeff i).natDegree ≤ 3)
    (hsymm : Polynomial.Bivariate.swap P = P)
    (hcoeff : ∀ i j : ℕ, j ≤ i → i ≤ 3 →
      (bivariateLaurentEvalHom T J P).coeff (-(9 * (i : ℤ) + 3 * j)) = 0) :
    P = 0 := by
  refine eq_zero_of_cubicCoeff_eq_zero P houter hinner hsymm fun k ↦
    wellFounded_gt.induction (C := fun k ↦ cubicCoeff P k = 0) k fun k ih ↦ ?_
  rw [← symmetricCubicLaurentExpansionFin_coeff_eq T J P hTorder hJorder hTlead hJlead k ih,
    ← bivariateLaurentEvalHom_eq_symmetricCubicLaurentExpansionFin T J P houter hinner hsymm]
  exact hcoeff _ _ (cubicJ_le_cubicI k) (cubicI_le_three k)

end Cox
