/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.PrimeSplitting
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Different ideal of `ℚ(√-6)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open IsDedekindDomain

namespace NumberField.SqrtNegSix

theorem absNorm_differentIdeal_eq_twentyFour :
    Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = 24 := by
  sorry

theorem prime_dvd_differentIdeal_iff_eq_ramifiedPrime
    (P : Ideal (𝓞 K)) (_hP : P.IsPrime) (_hP0 : P ≠ ⊥) :
    P ∣ differentIdeal ℤ (𝓞 K) ↔ P = primeAboveTwo ∨ P = primeAboveThree := by
  sorry

end NumberField.SqrtNegSix
