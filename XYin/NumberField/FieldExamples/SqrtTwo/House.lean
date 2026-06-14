/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.CanonicalEmbedding
import XYin.NumberField.FieldExamples.SqrtTwo.Units
import Mathlib.NumberTheory.NumberField.House

/-!
# House computations in `ℚ(√2)`

These statements specialize mathlib's `NumberField.house` API to the standard
generator and fundamental unit of `ℚ(√2)`.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtTwo

/-- The house of `√2` is `√2`. -/
theorem house_sqrtTwoRoot :
    NumberField.house sqrtTwoRoot = Real.sqrt 2 := by
  rw [NumberField.house, canonicalEmbedding_norm_sqrtTwoRoot]

/-- The house of the integral generator `√2 ∈ 𝓞 K` is `√2`. -/
theorem house_sqrtTwoInteger :
    NumberField.house (algebraMap (𝓞 K) K sqrtTwoInteger) = Real.sqrt 2 := by
  simpa [sqrtTwoInteger] using house_sqrtTwoRoot

/-- The house of the fundamental unit `1 + √2` is `1 + √2`. -/
theorem house_sqrtTwoFundamentalUnit :
    NumberField.house (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K)) =
      1 + Real.sqrt 2 := by
  change NumberField.house (sqrtTwoRoot + 1) = 1 + Real.sqrt 2
  apply le_antisymm
  · rw [NumberField.house, NumberField.canonicalEmbedding.norm_le_iff]
    intro φ
    have hnorm : ‖φ sqrtTwoRoot‖ = Real.sqrt 2 := by
      simpa using infinitePlace_apply_sqrtTwoRoot (NumberField.InfinitePlace.mk φ)
    calc
      ‖φ (sqrtTwoRoot + 1)‖ ≤ ‖φ sqrtTwoRoot‖ + ‖φ 1‖ := by
        simpa [map_add] using norm_add_le (φ sqrtTwoRoot) (φ 1)
      _ = 1 + Real.sqrt 2 := by rw [hnorm, map_one, norm_one, add_comm]
  · obtain ⟨σ, _, hσ, _⟩ := canonicalEmbedding_fundamentalUnit_coordinates
    calc
      1 + Real.sqrt 2 =
          ‖σ (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K))‖ := by
        rw [hσ, Complex.norm_of_nonneg]
        positivity
      _ = ‖σ (sqrtTwoRoot + 1)‖ := by rfl
      _ = ‖NumberField.canonicalEmbedding K (sqrtTwoRoot + 1) σ‖ := by
        rw [NumberField.canonicalEmbedding.apply_at]
      _ ≤ ‖NumberField.canonicalEmbedding K (sqrtTwoRoot + 1)‖ := norm_le_pi_norm _ σ

end NumberField.SqrtTwo
