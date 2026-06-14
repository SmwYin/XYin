/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.Units
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Adeles of `ℚ(√-6)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

/-- The adele ring of `ℚ(√-6)`. -/
abbrev SqrtNegSixAdeleRing : Type :=
  NumberField.AdeleRing (𝓞 K) K

abbrev principalAdele_theta : SqrtNegSixAdeleRing :=
  algebraMap K SqrtNegSixAdeleRing θ

abbrev principalAdele_torsionGenerator : SqrtNegSixAdeleRing :=
  algebraMap K SqrtNegSixAdeleRing (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K))

theorem principalAdele_theta_ne_zero : principalAdele_theta ≠ 0 := by
  sorry

theorem principalAdele_torsionGenerator_is_unit_everywhere :
    ∀ v : NumberField.FinitePlace K,
      v (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K)) = 1 := by
  sorry

end NumberField.SqrtNegSix
