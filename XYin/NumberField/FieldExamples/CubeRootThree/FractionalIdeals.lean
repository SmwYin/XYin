/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.PrimeSplitting
import Mathlib.NumberTheory.NumberField.FractionalIdeal

/-!
# Fractional ideals of `ℚ(∛3)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

abbrev cubeRootThreeFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.spanSingleton (𝓞 K)⁰ cubeRootThree

abbrev ramifiedPrimeFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  (Ideal.span {thetaInt} : FractionalIdeal (𝓞 K)⁰ K)

theorem cubeRootThree_mem_fractionalIdeal :
    cubeRootThree ∈ cubeRootThreeFractionalIdeal := by
  sorry

theorem cubeRootThreeFractionalIdeal_absNorm :
    FractionalIdeal.absNorm cubeRootThreeFractionalIdeal = |Algebra.norm ℚ cubeRootThree| := by
  sorry

theorem ramifiedPrimeFractionalIdeal_ne_zero :
    ramifiedPrimeFractionalIdeal ≠ 0 := by
  sorry

end NumberField.CubeRootThree
