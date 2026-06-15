/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.Units
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Adeles of `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

/-- The adele ring of `ℚ(√5)`. -/
abbrev SqrtFiveAdeleRing : Type :=
  NumberField.AdeleRing (𝓞 K) K

abbrev principalAdele_goldenRoot : SqrtFiveAdeleRing :=
  algebraMap K SqrtFiveAdeleRing goldenRoot

abbrev principalAdele_fundamentalUnit : SqrtFiveAdeleRing :=
  algebraMap K SqrtFiveAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

theorem principalAdele_goldenRoot_ne_zero : principalAdele_goldenRoot ≠ 0 := by
  intro h
  have hroot : goldenRoot = 0 :=
    NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K) h
  have hsq := goldenRoot_sq
  rw [hroot] at hsq
  norm_num at hsq

theorem principalAdele_fundamentalUnit_is_unit_everywhere :
    ∀ v : NumberField.FinitePlace K,
      v (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) = 1 := by
  intro v
  rw [← NumberField.FinitePlace.norm_embedding_eq v
    (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))]
  rw [NumberField.FinitePlace.norm_eq_one_iff_notMem (K := K)
    (v := NumberField.FinitePlace.maximalIdeal v)]
  intro hmem
  have hmul : (fundamentalUnit : 𝓞 K) * ((fundamentalUnit⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
    exact fundamentalUnit.val_inv
  have h_mem_mul :
      (fundamentalUnit : 𝓞 K) * ((fundamentalUnit⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ∈
        (NumberField.FinitePlace.maximalIdeal v).asIdeal :=
    Ideal.mul_mem_right ((fundamentalUnit⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
      (NumberField.FinitePlace.maximalIdeal v).asIdeal hmem
  have h_one : (1 : 𝓞 K) ∈ (NumberField.FinitePlace.maximalIdeal v).asIdeal := by
    rwa [hmul] at h_mem_mul
  exact (NumberField.FinitePlace.maximalIdeal v).isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr h_one)

end NumberField.SqrtFive
