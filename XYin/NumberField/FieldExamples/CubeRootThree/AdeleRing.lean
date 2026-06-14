/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.Units
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Adeles of `ℚ(∛3)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

/-- The adele ring of `ℚ(∛3)`. -/
abbrev CubeRootThreeAdeleRing : Type :=
  NumberField.AdeleRing (𝓞 K) K

abbrev principalAdele_cubeRootThree : CubeRootThreeAdeleRing :=
  algebraMap K CubeRootThreeAdeleRing cubeRootThree

abbrev principalAdele_fundamentalUnit : CubeRootThreeAdeleRing :=
  algebraMap K CubeRootThreeAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

theorem principalAdele_cubeRootThree_ne_zero : principalAdele_cubeRootThree ≠ 0 := by
  sorry

theorem principalAdele_fundamentalUnit_is_unit_everywhere :
    ∀ v : NumberField.FinitePlace K,
      v (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) = 1 := by
  sorry

end NumberField.CubeRootThree
