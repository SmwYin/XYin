/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicThree.Units
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Adeles of `ℚ(ζ₃)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicThree

/-- The adele ring of `ℚ(ζ₃)`. -/
abbrev CyclotomicThreeAdeleRing : Type :=
  NumberField.AdeleRing (𝓞 K) K

abbrev principalAdele_zeta : CyclotomicThreeAdeleRing :=
  algebraMap K CyclotomicThreeAdeleRing ζ

abbrev principalAdele_etaUnit : CyclotomicThreeAdeleRing :=
  algebraMap K CyclotomicThreeAdeleRing (algebraMap (𝓞 K) K (etaUnit : 𝓞 K))

theorem principalAdele_zeta_ne_zero : principalAdele_zeta ≠ 0 := by
  sorry

theorem principalAdele_etaUnit_is_unit_everywhere :
    ∀ v : NumberField.FinitePlace K,
      v (algebraMap (𝓞 K) K (etaUnit : 𝓞 K)) = 1 := by
  sorry

end NumberField.CyclotomicThree
