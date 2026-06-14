/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicThree.PrimeSplitting
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Different ideal of `ℚ(ζ₃)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open IsDedekindDomain

namespace NumberField.CyclotomicThree

theorem absNorm_differentIdeal_eq_three :
    Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = 3 := by
  sorry

theorem prime_dvd_differentIdeal_iff_eq_span_zeta_sub_one
    (P : Ideal (𝓞 K)) (_hP : P.IsPrime) (_hP0 : P ≠ ⊥) :
    P ∣ differentIdeal ℤ (𝓞 K) ↔ P = Ideal.span {zetaInt - 1} := by
  sorry

end NumberField.CyclotomicThree
