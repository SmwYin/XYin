/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.House

/-!
# House examples in `ℚ(√-6)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

theorem house_theta_pos :
    0 < NumberField.house θ := by
  exact lt_of_lt_of_le zero_lt_one
    (NumberField.one_le_house_of_isIntegral theta_integral (by
      intro h
      have hsq := theta_sq
      rw [h] at hsq
      norm_num at hsq))

theorem house_torsionGenerator :
    NumberField.house (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K)) = 1 := by
  simpa [torsionGenerator] using (NumberField.house_intCast (K := K) (-1 : ℤ))

end NumberField.SqrtNegSix
