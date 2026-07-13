/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.RingTheory.LaurentSeries

/-!
# Polynomial evaluation in Laurent series

This file records the lowest-term argument behind Hasse's q-expansion principle. If a Laurent
series `J` has order `-w`, for `w > 0`, and leading coefficient one, then the lowest coefficient
of `P(J)` is the leading coefficient of `P`. In particular, substitution at `J` is injective.
-/

noncomputable section

namespace Cox

/-- Coefficientwise application of a ring homomorphism to Laurent series, bundled as a ring
homomorphism. -/
def laurentSeriesMapRingHom {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun F := F.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom

@[simp]
theorem laurentSeriesMapRingHom_coeff
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : LaurentSeries R) (k : ℤ) :
    (laurentSeriesMapRingHom f F).coeff k = f (F.coeff k) :=
  rfl

/-- Substitute a Laurent series for the coefficient variable of an iterated polynomial. -/
def bivariateSpecializeLaurent {R : Type*} [CommRing R]
    (J : LaurentSeries R) :
    Polynomial (Polynomial R) →+* Polynomial (LaurentSeries R) :=
  Polynomial.mapRingHom
    (Polynomial.eval₂RingHom HahnSeries.C J)

private theorem polynomialEvalLaurent_map
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (J : LaurentSeries R) (J' : LaurentSeries S)
    (hJ : laurentSeriesMapRingHom f J = J') (P : Polynomial R) :
    laurentSeriesMapRingHom f (P.eval₂ HahnSeries.C J) =
      (P.map f).eval₂ HahnSeries.C J' := by
  have hC :
      (laurentSeriesMapRingHom f).comp
          (HahnSeries.C : R →+* LaurentSeries R) =
        (HahnSeries.C : S →+* LaurentSeries S).comp f := by
    apply DFunLike.ext _ _
    intro r
    exact HahnSeries.map_C r f
  calc
    laurentSeriesMapRingHom f (P.eval₂ HahnSeries.C J) =
        P.eval₂ ((laurentSeriesMapRingHom f).comp HahnSeries.C)
          (laurentSeriesMapRingHom f J) :=
      Polynomial.hom_eval₂ P HahnSeries.C (laurentSeriesMapRingHom f) J
    _ = P.eval₂ ((HahnSeries.C : S →+* LaurentSeries S).comp f) J' := by
      rw [hC, hJ]
    _ = (P.map f).eval₂ HahnSeries.C J' :=
      (Polynomial.eval₂_map f HahnSeries.C J').symm

/-- Laurent specialization of an iterated polynomial commutes with coefficientwise base
change. -/
theorem bivariateSpecializeLaurent_map
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (J : LaurentSeries R) (J' : LaurentSeries S)
    (hJ : laurentSeriesMapRingHom f J = J') :
    (Polynomial.mapRingHom (laurentSeriesMapRingHom f)).comp
        (bivariateSpecializeLaurent J) =
      (bivariateSpecializeLaurent J').comp
        (Polynomial.mapRingHom (Polynomial.mapRingHom f)) := by
  apply Polynomial.ringHom_ext
  · intro P
    simp only [RingHom.comp_apply, bivariateSpecializeLaurent,
      Polynomial.coe_mapRingHom, Polynomial.map_C,
      Polynomial.coe_eval₂RingHom]
    change Polynomial.C
        (laurentSeriesMapRingHom f (P.eval₂ HahnSeries.C J)) =
      Polynomial.C ((P.map f).eval₂ HahnSeries.C J')
    rw [polynomialEvalLaurent_map f J J' hJ P]
  · simp [bivariateSpecializeLaurent, Polynomial.coe_mapRingHom]

/-- Pointwise form of `bivariateSpecializeLaurent_map`. -/
theorem bivariateSpecializeLaurent_map_apply
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (J : LaurentSeries R) (J' : LaurentSeries S)
    (hJ : laurentSeriesMapRingHom f J = J')
    (P : Polynomial (Polynomial R)) :
    (bivariateSpecializeLaurent J P).map
        (laurentSeriesMapRingHom f) =
      bivariateSpecializeLaurent J'
        (P.map (Polynomial.mapRingHom f)) := by
  exact DFunLike.congr_fun (bivariateSpecializeLaurent_map f J J' hJ) P

/-- The order of a power of a Laurent series whose principal exponent is negative. -/
theorem laurentSeries_pow_order_of_order_neg
    {K : Type*} [Field K] (J : LaurentSeries K) (w n : ℕ)
    (horder : J.order = -(w : ℤ)) :
    (J ^ n).order = -((w : ℤ) * (n : ℤ)) := by
  rw [HahnSeries.order_pow, horder]
  simp
  ring

/-- The leading coefficient of every power of a Laurent series with leading coefficient one
remains one. -/
theorem laurentSeries_pow_leadingCoeff_of_eq_one
    {K : Type*} [Field K] (J : LaurentSeries K)
    (hleading : J.leadingCoeff = 1) (n : ℕ) :
    (J ^ n).leadingCoeff = 1 := by
  induction n with
  | zero => simp [HahnSeries.leadingCoeff_one]
  | succ n ih =>
      simp [pow_succ, HahnSeries.leadingCoeff_mul, ih, hleading]

/-- The lowest Laurent coefficient of `P(J)` is the leading coefficient of `P`. -/
theorem polynomial_eval₂_laurentSeries_coeff
    {K : Type*} [Field K] (J : LaurentSeries K) (w : ℕ) (hw : 0 < w)
    (horder : J.order = -(w : ℤ)) (hleading : J.leadingCoeff = 1)
    (P : Polynomial K) :
    (P.eval₂ (HahnSeries.C : K →+* LaurentSeries K) J).coeff
        (-((w : ℤ) * (P.natDegree : ℤ))) = P.leadingCoeff := by
  rw [Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum]
  calc
    ∑ i ∈ Finset.range (P.natDegree + 1),
        (HahnSeries.C (P.coeff i) * J ^ i).coeff
            (-((w : ℤ) * (P.natDegree : ℤ))) =
        (HahnSeries.C (P.coeff P.natDegree) * J ^ P.natDegree).coeff
            (-((w : ℤ) * (P.natDegree : ℤ))) := by
      apply Finset.sum_eq_single P.natDegree
      · intro n hn hne
        rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
        change P.coeff n *
          (J ^ n).coeff (-((w : ℤ) * (P.natDegree : ℤ))) = 0
        have hnlt : n < P.natDegree := by
          have hnle : n ≤ P.natDegree :=
            Nat.le_of_lt_succ (Finset.mem_range.mp hn)
          exact lt_of_le_of_ne hnle hne
        have hwz : (0 : ℤ) < w := by exact_mod_cast hw
        have hlt : -((w : ℤ) * (P.natDegree : ℤ)) < (J ^ n).order := by
          rw [laurentSeries_pow_order_of_order_neg J w n horder]
          exact neg_lt_neg <| Int.mul_lt_mul_of_pos_left (by exact_mod_cast hnlt) hwz
        rw [HahnSeries.coeff_eq_zero_of_lt_order hlt, mul_zero]
      · simp
    _ = P.leadingCoeff := by
      rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
      change P.coeff P.natDegree *
        (J ^ P.natDegree).coeff (-((w : ℤ) * (P.natDegree : ℤ))) = _
      rw [← laurentSeries_pow_order_of_order_neg J w P.natDegree horder,
        ← HahnSeries.leadingCoeff_eq,
        laurentSeries_pow_leadingCoeff_of_eq_one J hleading,
        mul_one, Polynomial.coeff_natDegree]

/-- Evaluation at a Laurent series with a pole and unit leading coefficient is injective. -/
theorem polynomial_eval₂_laurentSeries_injective
    {K : Type*} [Field K] (J : LaurentSeries K) (w : ℕ) (hw : 0 < w)
    (horder : J.order = -(w : ℤ)) (hleading : J.leadingCoeff = 1) :
    Function.Injective (Polynomial.eval₂RingHom
      (HahnSeries.C : K →+* LaurentSeries K) J) := by
  intro P Q hPQ
  apply sub_eq_zero.mp
  let R := P - Q
  have hR : R.eval₂ (HahnSeries.C : K →+* LaurentSeries K) J = 0 := by
    simpa only [R, Polynomial.eval₂_sub, sub_eq_zero] using hPQ
  by_contra hR0
  have hcoeff := polynomial_eval₂_laurentSeries_coeff
    J w hw horder hleading R
  rw [hR] at hcoeff
  simp only [HahnSeries.coeff_zero] at hcoeff
  exact (Polynomial.leadingCoeff_ne_zero.mpr hR0) hcoeff.symm

end Cox
