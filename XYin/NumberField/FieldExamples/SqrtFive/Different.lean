/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.PrimeSplitting
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Different ideal of `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial
open IsDedekindDomain

namespace NumberField.SqrtFive

private theorem goldenIntO_adjoin_eq_top :
    Algebra.adjoin ℤ ({goldenIntO} : Set (𝓞 K)) = ⊤ := by
  apply le_antisymm le_top
  intro x _
  have hxint : (x : K) ∈ integralClosure ℤ K := x.2
  have hfield : (x : K) ∈ Algebra.adjoin ℤ ({goldenRoot} : Set K) := by
    simpa [concreteRingOfIntegers] using (by
      rw [ringOfIntegers_eq] at hxint
      exact hxint)
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hfield
  rcases hfield with ⟨P, hP⟩
  have hx_eq : x = aeval goldenIntO P := by
    apply Subtype.ext
    change (x : K) = ((aeval goldenIntO P : 𝓞 K) : K)
    rw [← hP]
    simpa [goldenIntO] using
      (Polynomial.aeval_algHom_apply (algebraMap (𝓞 K) K).toIntAlgHom goldenIntO P)
  rw [hx_eq]
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨P, rfl⟩

private theorem goldenIntO_minpoly :
    minpoly ℤ goldenIntO = X ^ 2 - X - 1 := by
  letI : IsScalarTower ℤ (𝓞 K) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hint : IsIntegral ℤ goldenIntO := Algebra.IsIntegral.isIntegral goldenIntO
  have hfrac :
      minpoly ℚ ((algebraMap (𝓞 K) K) goldenIntO) =
        map (algebraMap ℤ ℚ) (minpoly ℤ goldenIntO) :=
    @minpoly.isIntegrallyClosed_eq_field_fractions ℤ (𝓞 K)
      inferInstance inferInstance inferInstance inferInstance
      ℚ K inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance this inferInstance inferInstance
      goldenIntO hint
  apply (Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective)
  rw [← hfrac]
  change minpoly ℚ goldenRoot = map (algebraMap ℤ ℚ) (X ^ 2 - X - 1 : ℤ[X])
  have hminQ : minpoly ℚ goldenRoot = (X ^ 2 - X - 1 : ℚ[X]) := by
    exact (minpoly.eq_of_irreducible_of_monic
      (Polynomial.X_pow_sub_X_sub_one_irreducible_rat (n := 2)
        (by norm_num : (2 : ℕ) ≠ 1))
      (by
        simp
        linear_combination goldenRoot_sq) (by
        rw [show (X ^ 2 - X - 1 : ℚ[X]) = X ^ 2 - (X + 1) by ring]
        apply monic_X_pow_sub
        simpa using (show degree (X + C (1 : ℚ)) < (2 : WithBot ℕ) by
          rw [degree_X_add_C]
          norm_num))).symm
  rw [hminQ]
  simp [sub_eq_add_neg]

theorem differentIdeal_eq_span_sqrtFive :
    differentIdeal ℤ (𝓞 K) = Ideal.span {sqrtFiveIntO} := by
  have hcond : conductor ℤ goldenIntO = ⊤ :=
    conductor_eq_top_of_adjoin_eq_top goldenIntO_adjoin_eq_top
  have hadjoin : Algebra.adjoin ℚ ({algebraMap (𝓞 K) K goldenIntO} : Set K) = ⊤ := by
    simpa [goldenIntO] using adjoin_goldenRoot_eq_top
  have hdiff := conductor_mul_differentIdeal ℤ ℚ K (B := 𝓞 K) goldenIntO hadjoin
  rw [hcond, Ideal.top_mul] at hdiff
  have hae : aeval goldenIntO (derivative (minpoly ℤ goldenIntO)) = sqrtFiveIntO := by
    rw [goldenIntO_minpoly]
    rw [show derivative (X ^ 2 - X - (1 : ℤ[X])) = (2 : ℤ[X]) * X - 1 by
      simp]
    calc
      aeval goldenIntO ((2 : ℤ[X]) * X - 1) =
          aeval goldenIntO (C (2 : ℤ)) * aeval goldenIntO X - aeval goldenIntO 1 := by
        rw [show (2 : ℤ[X]) = C (2 : ℤ) by rfl, map_sub, map_mul]
      _ = sqrtFiveIntO := by
        rw [aeval_C, aeval_X, map_one]
        simp [sqrtFiveIntO]
  rw [hdiff, hae]

theorem absNorm_differentIdeal_eq_five :
    Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = 5 := by
  rw [NumberField.absNorm_differentIdeal (K := K), numberField_discr_eq]
  norm_num

theorem prime_dvd_differentIdeal_iff_eq_span_sqrtFive
    (P : Ideal (𝓞 K)) (_hP : P.IsPrime) (_hP0 : P ≠ ⊥) :
    P ∣ differentIdeal ℤ (𝓞 K) ↔ P = Ideal.span {sqrtFiveIntO} := by
  constructor
  · intro hdiv
    haveI : P.IsPrime := _hP
    have hle : Ideal.span {sqrtFiveIntO} ≤ P := by
      rw [← differentIdeal_eq_span_sqrtFive]
      exact Ideal.le_of_dvd hdiv
    have hI0 : Ideal.span ({sqrtFiveIntO} : Set (𝓞 K)) ≠ ⊥ := by
      intro hbot
      have hzero : sqrtFiveIntO = 0 := Ideal.span_singleton_eq_bot.mp hbot
      have hsqrt : sqrtFiveIntO ^ 2 = (5 : 𝓞 K) := by
        apply Subtype.ext
        change (2 * goldenRoot - 1) ^ 2 = (5 : K)
        exact sqrtFiveRoot_sq
      rw [hzero] at hsqrt
      norm_num at hsqrt
    exact ((isPrime_span_sqrtFiveIntO.isMaximal hI0).eq_of_le _hP.ne_top hle).symm
  · intro h
    rw [h, differentIdeal_eq_span_sqrtFive]

end NumberField.SqrtFive
