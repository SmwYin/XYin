/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicFive.Units
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Adeles of `ℚ(ζ₅)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

/-- The adele ring of `ℚ(ζ₅)`. -/
abbrev CyclotomicFiveAdeleRing : Type :=
  NumberField.AdeleRing (𝓞 K) K

abbrev principalAdele_zeta : CyclotomicFiveAdeleRing :=
  algebraMap K CyclotomicFiveAdeleRing ζ

abbrev principalAdele_fundamentalUnit : CyclotomicFiveAdeleRing :=
  algebraMap K CyclotomicFiveAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

theorem principalAdele_zeta_ne_zero : principalAdele_zeta ≠ 0 := by
  sorry

theorem principalAdele_fundamentalUnit_is_unit_everywhere :
    ∀ v : NumberField.FinitePlace K,
      v (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) = 1 := by
  sorry

end NumberField.CyclotomicFive
