/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicEight.PrimeSplitting
import Mathlib.NumberTheory.NumberField.FractionalIdeal

/-!
# Fractional ideals of `ℚ(ζ₈)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

abbrev zetaFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.spanSingleton (𝓞 K)⁰ ζ

abbrev ramifiedPrimeFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  (Ideal.span {1 - zetaInt} : FractionalIdeal (𝓞 K)⁰ K)

theorem zeta_mem_fractionalIdeal :
    ζ ∈ zetaFractionalIdeal := by
  sorry

theorem zetaFractionalIdeal_absNorm :
    FractionalIdeal.absNorm zetaFractionalIdeal = |Algebra.norm ℚ ζ| := by
  sorry

theorem ramifiedPrimeFractionalIdeal_ne_zero :
    ramifiedPrimeFractionalIdeal ≠ 0 := by
  sorry

end NumberField.CyclotomicEight
