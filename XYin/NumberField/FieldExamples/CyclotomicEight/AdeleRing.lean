/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicEight.Units
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Adeles of `ℚ(ζ₈)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

/-- The adele ring of `ℚ(ζ₈)`. -/
abbrev CyclotomicEightAdeleRing : Type :=
  NumberField.AdeleRing (𝓞 K) K

abbrev principalAdele_zeta : CyclotomicEightAdeleRing :=
  algebraMap K CyclotomicEightAdeleRing ζ

abbrev principalAdele_fundamentalUnit : CyclotomicEightAdeleRing :=
  algebraMap K CyclotomicEightAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

theorem principalAdele_zeta_ne_zero : principalAdele_zeta ≠ 0 := by
  sorry

theorem principalAdele_fundamentalUnit_is_unit_everywhere :
    ∀ v : NumberField.FinitePlace K,
      v (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) = 1 := by
  sorry

end NumberField.CyclotomicEight
