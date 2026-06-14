/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.PrimeSplitting
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Different ideal of `ℚ(∛3)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open IsDedekindDomain

namespace NumberField.CubeRootThree

theorem absNorm_differentIdeal_eq_twoHundredFortyThree :
    Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = 243 := by
  sorry

theorem prime_dvd_differentIdeal_iff_eq_span_theta
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    P ∣ differentIdeal ℤ (𝓞 K) ↔ P = Ideal.span {thetaInt} := by
  sorry

end NumberField.CubeRootThree
