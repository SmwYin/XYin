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
  sorry

theorem house_torsionGenerator :
    NumberField.house (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K)) = 1 := by
  sorry

end NumberField.SqrtNegSix
