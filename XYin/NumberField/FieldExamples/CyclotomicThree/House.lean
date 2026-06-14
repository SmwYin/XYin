/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicThree.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.House

/-!
# House examples in `ℚ(ζ₃)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicThree

theorem house_zeta :
    NumberField.house ζ = 1 := by
  sorry

theorem house_etaUnit :
    NumberField.house (algebraMap (𝓞 K) K (etaUnit : 𝓞 K)) = 1 := by
  sorry

end NumberField.CyclotomicThree
