/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.PrimeSplitting
import Mathlib.NumberTheory.NumberField.FractionalIdeal

/-!
# Fractional ideals of `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

abbrev goldenRootFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.spanSingleton (𝓞 K)⁰ goldenRoot

abbrev ramifiedPrimeFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  (Ideal.span {sqrtFiveIntO} : FractionalIdeal (𝓞 K)⁰ K)

theorem goldenRoot_mem_fractionalIdeal :
    goldenRoot ∈ goldenRootFractionalIdeal := by
  sorry

theorem goldenRootFractionalIdeal_absNorm :
    FractionalIdeal.absNorm goldenRootFractionalIdeal = |Algebra.norm ℚ goldenRoot| := by
  sorry

theorem ramifiedPrimeFractionalIdeal_ne_zero :
    ramifiedPrimeFractionalIdeal ≠ 0 := by
  sorry

end NumberField.SqrtFive
