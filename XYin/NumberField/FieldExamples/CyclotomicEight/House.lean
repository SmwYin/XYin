/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicEight.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.House

/-!
# House examples in `ℚ(ζ₈)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

theorem house_zeta :
    NumberField.house ζ = 1 := by
  sorry

theorem house_fundamentalUnit_pos :
    0 < NumberField.house (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) := by
  sorry

end NumberField.CyclotomicEight
