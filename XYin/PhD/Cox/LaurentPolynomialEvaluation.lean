/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Algebra.Polynomial.Bivariate
import XYin.PhD.Cox.LaurentSeriesAux

/-!
# Polynomial evaluation in Laurent series

This file records the lowest-term argument behind Hasse's q-expansion principle. If a Laurent
series `J` has order `-w`, for `w > 0`, and leading coefficient one, then the lowest coefficient
of `P(J)` is the leading coefficient of `P`. In particular, substitution at `J` is injective.
It also packages the substitution of Laurent series into bivariate polynomials `R[X][Y]` and its
compatibility with coefficientwise base change.
-/

open scoped Polynomial.Bivariate

noncomputable section

namespace HahnSeries

variable {Γ R S : Type*} [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
  [CommSemiring R] [CommSemiring S]

/-- Evaluating a polynomial at a Hahn series commutes with coefficientwise base change. -/
theorem mapRingHom_comp_eval₂RingHom (f : R →+* S) {J : HahnSeries Γ R}
    {J' : HahnSeries Γ S} (hJ : mapRingHom f J = J') :
    (mapRingHom f).comp (Polynomial.eval₂RingHom C J) =
      (Polynomial.eval₂RingHom C J').comp (Polynomial.mapRingHom f) := by
  apply Polynomial.ringHom_ext
  · intro r
    simpa [C] using map_C r f
  · simp [hJ]

end HahnSeries

namespace Cox

section BaseChange

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Substitute a Laurent series for the inner variable `C X` of a bivariate polynomial. -/
def bivariateSpecializeLaurent (J : LaurentSeries R) :
    R[X][Y] →+* Polynomial (LaurentSeries R) :=
  Polynomial.mapRingHom (Polynomial.eval₂RingHom HahnSeries.C J)

/-- Laurent specialization of a bivariate polynomial commutes with coefficientwise base
change. -/
theorem bivariateSpecializeLaurent_map (f : R →+* S) (J : LaurentSeries R) (J' : LaurentSeries S)
    (hJ : HahnSeries.mapRingHom f J = J') :
    (Polynomial.mapRingHom (HahnSeries.mapRingHom f)).comp
        (bivariateSpecializeLaurent J) =
      (bivariateSpecializeLaurent J').comp
        (Polynomial.mapRingHom (Polynomial.mapRingHom f)) := by
  simp only [bivariateSpecializeLaurent, Polynomial.mapRingHom_comp,
    HahnSeries.mapRingHom_comp_eval₂RingHom f hJ]

/-- Pointwise form of `bivariateSpecializeLaurent_map`. -/
theorem bivariateSpecializeLaurent_map_apply (f : R →+* S) (J : LaurentSeries R)
    (J' : LaurentSeries S) (hJ : HahnSeries.mapRingHom f J = J') (P : R[X][Y]) :
    (bivariateSpecializeLaurent J P).map (HahnSeries.mapRingHom f) =
      bivariateSpecializeLaurent J' (P.map (Polynomial.mapRingHom f)) :=
  DFunLike.congr_fun (bivariateSpecializeLaurent_map f J J' hJ) P

/-- Evaluation of a bivariate polynomial at a pair of Laurent series: the outer variable `Y` is
sent to `T` and the inner variable `C X` to `J`. -/
def bivariateLaurentEvalHom (T J : LaurentSeries R) : R[X][Y] →+* LaurentSeries R :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom HahnSeries.C J) T

theorem bivariateLaurentEvalHom_apply (T J : LaurentSeries R) (P : R[X][Y]) :
    bivariateLaurentEvalHom T J P = P.eval₂ (Polynomial.eval₂RingHom HahnSeries.C J) T :=
  rfl

@[simp]
theorem bivariateLaurentEvalHom_monomial (T J : LaurentSeries R) (i j : ℕ) (a : R) :
    bivariateLaurentEvalHom T J (Polynomial.monomial i (Polynomial.monomial j a)) =
      HahnSeries.C a * T ^ i * J ^ j := by
  simp only [bivariateLaurentEvalHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
  ring

@[simp]
theorem bivariateLaurentEvalHom_X (T J : LaurentSeries R) :
    bivariateLaurentEvalHom T J Polynomial.X = T :=
  Polynomial.eval₂_X _ _

@[simp]
theorem bivariateLaurentEvalHom_C_X (T J : LaurentSeries R) :
    bivariateLaurentEvalHom T J (Polynomial.C Polynomial.X) = J := by
  simp [bivariateLaurentEvalHom]

/-- Bivariate Laurent evaluation commutes with coefficientwise base change. -/
theorem bivariateLaurentEvalHom_map (f : R →+* S) {T J : LaurentSeries R}
    {T' J' : LaurentSeries S} (hT : HahnSeries.mapRingHom f T = T')
    (hJ : HahnSeries.mapRingHom f J = J') (P : R[X][Y]) :
    HahnSeries.mapRingHom f (bivariateLaurentEvalHom T J P) =
      bivariateLaurentEvalHom T' J' (P.map (Polynomial.mapRingHom f)) := by
  simp only [bivariateLaurentEvalHom, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂, hT,
    Polynomial.eval₂_map, HahnSeries.mapRingHom_comp_eval₂RingHom f hJ]

end BaseChange

section LowestTerm

variable {K : Type*} [CommSemiring K] [NoZeroDivisors K]

/-- The order of a power of a Laurent series whose principal exponent is negative. -/
theorem laurentSeries_pow_order_of_order_neg (J : LaurentSeries K) (w n : ℕ)
    (horder : J.order = -(w : ℤ)) :
    (J ^ n).order = -((w : ℤ) * (n : ℤ)) := by
  rw [HahnSeries.order_pow, horder]
  simp
  ring

/-- Below `-(w · deg P)`, all Laurent coefficients of `P(J)` vanish. -/
theorem polynomial_eval₂_laurentSeries_coeff_eq_zero_of_lt (J : LaurentSeries K) (w : ℕ)
    (horder : J.order = -(w : ℤ)) (P : Polynomial K) {k : ℤ}
    (hk : k < -((w : ℤ) * (P.natDegree : ℤ))) :
    (P.eval₂ (HahnSeries.C : K →+* LaurentSeries K) J).coeff k = 0 := by
  rw [Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun n hn ↦ ?_
  have hnle : n ≤ P.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have horder : k < (J ^ n).order := by
    rw [laurentSeries_pow_order_of_order_neg J w n horder]
    exact hk.trans_le <| neg_le_neg <| Int.mul_le_mul_of_nonneg_left
      (by exact_mod_cast hnle) (Int.natCast_nonneg w)
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
    HahnSeries.coeff_eq_zero_of_lt_order horder, smul_zero]

/-- The lowest Laurent coefficient of `P(J)` is the leading coefficient of `P`. -/
theorem polynomial_eval₂_laurentSeries_coeff (J : LaurentSeries K) (w : ℕ) (hw : 0 < w)
    (horder : J.order = -(w : ℤ)) (hleading : J.leadingCoeff = 1)
    (P : Polynomial K) :
    (P.eval₂ (HahnSeries.C : K →+* LaurentSeries K) J).coeff
        (-((w : ℤ) * (P.natDegree : ℤ))) = P.leadingCoeff := by
  rw [Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum,
    Finset.sum_eq_single P.natDegree]
  · rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
      ← laurentSeries_pow_order_of_order_neg J w P.natDegree horder,
      ← HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_pow, hleading, one_pow,
      smul_eq_mul, mul_one, Polynomial.coeff_natDegree]
  · intro n hn hne
    have hnlt : n < P.natDegree :=
      lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hn)) hne
    have hlt : -((w : ℤ) * (P.natDegree : ℤ)) < (J ^ n).order := by
      rw [laurentSeries_pow_order_of_order_neg J w n horder]
      exact neg_lt_neg <| by exact_mod_cast Nat.mul_lt_mul_of_pos_left hnlt hw
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
      HahnSeries.coeff_eq_zero_of_lt_order hlt, smul_zero]
  · simp

/-- For `P ≠ 0`, the order of `P(J)` is `-(w · deg P)`. -/
theorem polynomial_eval₂_laurentSeries_order (J : LaurentSeries K) (w : ℕ) (hw : 0 < w)
    (horder : J.order = -(w : ℤ)) (hleading : J.leadingCoeff = 1)
    {P : Polynomial K} (hP : P ≠ 0) :
    (P.eval₂ (HahnSeries.C : K →+* LaurentSeries K) J).order =
      -((w : ℤ) * (P.natDegree : ℤ)) :=
  HahnSeries.order_eq_of_coeff_ne_zero_of_forall_lt
    ((polynomial_eval₂_laurentSeries_coeff J w hw horder hleading P).trans_ne
      (Polynomial.leadingCoeff_ne_zero.mpr hP))
    fun _ hi ↦ polynomial_eval₂_laurentSeries_coeff_eq_zero_of_lt J w horder P hi

/-- The leading coefficient of `P(J)` is the leading coefficient of `P`. -/
theorem polynomial_eval₂_laurentSeries_leadingCoeff (J : LaurentSeries K) (w : ℕ)
    (hw : 0 < w) (horder : J.order = -(w : ℤ)) (hleading : J.leadingCoeff = 1)
    (P : Polynomial K) :
    (P.eval₂ (HahnSeries.C : K →+* LaurentSeries K) J).leadingCoeff = P.leadingCoeff := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  rw [HahnSeries.leadingCoeff_eq, polynomial_eval₂_laurentSeries_order J w hw horder hleading hP,
    polynomial_eval₂_laurentSeries_coeff J w hw horder hleading P]

end LowestTerm

/-- Evaluation at a Laurent series with a pole and unit leading coefficient is injective. -/
theorem polynomial_eval₂_laurentSeries_injective
    {K : Type*} [CommRing K] [NoZeroDivisors K] (J : LaurentSeries K) (w : ℕ) (hw : 0 < w)
    (horder : J.order = -(w : ℤ)) (hleading : J.leadingCoeff = 1) :
    Function.Injective (Polynomial.eval₂RingHom
      (HahnSeries.C : K →+* LaurentSeries K) J) := by
  refine (injective_iff_map_eq_zero _).2 fun P hP ↦ Polynomial.leadingCoeff_eq_zero.mp ?_
  rw [← polynomial_eval₂_laurentSeries_coeff J w hw horder hleading P]
  exact congrArg (HahnSeries.coeff · _) hP |>.trans (HahnSeries.coeff_zero)

end Cox
