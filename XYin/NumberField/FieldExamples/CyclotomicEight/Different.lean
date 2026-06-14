/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicEight.PrimeSplitting
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Different ideal of `ℚ(ζ₈)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open IsDedekindDomain

namespace NumberField.CyclotomicEight

theorem absNorm_differentIdeal_eq_twoHundredFiftySix :
    Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = 256 := by
  sorry

theorem prime_dvd_differentIdeal_iff_eq_span_one_sub_zeta
    (P : Ideal (𝓞 K)) (_hP : P.IsPrime) (_hP0 : P ≠ ⊥) :
    P ∣ differentIdeal ℤ (𝓞 K) ↔ P = Ideal.span {1 - zetaInt} := by
  sorry

end NumberField.CyclotomicEight
