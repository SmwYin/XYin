/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.House

/-!
# House examples in `ℚ(∛3)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

theorem house_cubeRootThree_pos :
    0 < NumberField.house cubeRootThree := by
  sorry

theorem house_thetaInt_pos :
    0 < NumberField.house (algebraMap (𝓞 K) K thetaInt) := by
  sorry

end NumberField.CubeRootThree
