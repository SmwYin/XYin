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

open IsDedekindDomain

namespace NumberField.SqrtFive

theorem differentIdeal_eq_span_sqrtFive :
    differentIdeal ℤ (𝓞 K) = Ideal.span {sqrtFiveIntO} := by
  sorry

theorem absNorm_differentIdeal_eq_five :
    Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = 5 := by
  sorry

theorem prime_dvd_differentIdeal_iff_eq_span_sqrtFive
    (P : Ideal (𝓞 K)) (_hP : P.IsPrime) (_hP0 : P ≠ ⊥) :
    P ∣ differentIdeal ℤ (𝓞 K) ↔ P = Ideal.span {sqrtFiveIntO} := by
  sorry

end NumberField.SqrtFive
