/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.Units
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Adeles of `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

/-- The adele ring of `ℚ(√5)`. -/
abbrev SqrtFiveAdeleRing : Type :=
  NumberField.AdeleRing (𝓞 K) K

abbrev principalAdele_goldenRoot : SqrtFiveAdeleRing :=
  algebraMap K SqrtFiveAdeleRing goldenRoot

abbrev principalAdele_fundamentalUnit : SqrtFiveAdeleRing :=
  algebraMap K SqrtFiveAdeleRing (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))

theorem principalAdele_goldenRoot_ne_zero : principalAdele_goldenRoot ≠ 0 := by
  sorry

theorem principalAdele_fundamentalUnit_is_unit_everywhere :
    ∀ v : NumberField.FinitePlace K,
      v (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) = 1 := by
  sorry

end NumberField.SqrtFive
