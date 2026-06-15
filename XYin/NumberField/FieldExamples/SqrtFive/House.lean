/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.House

/-!
# House examples in `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

theorem house_goldenRoot_pos :
    0 < NumberField.house goldenRoot := by
  exact lt_of_lt_of_le zero_lt_one
    (NumberField.one_le_house_of_isIntegral goldenRoot_isIntegral (by
      intro h
      have hsq := goldenRoot_sq
      rw [h] at hsq
      norm_num at hsq))

theorem house_fundamentalUnit :
    NumberField.house (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) =
      (1 + Real.sqrt 5) / 2 := by
  sorry

end NumberField.SqrtFive
