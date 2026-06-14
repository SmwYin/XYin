/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.PolarCoord

/-!
# Canonical embedding geometry for `ℚ(√2)`

This file records the geometry-of-numbers layer around the canonical / mixed embedding.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open MeasureTheory NumberField

namespace NumberField.SqrtTwo

/-- The mixed embedding of the generator `√2`. -/
abbrev mixedEmbedding_sqrtTwoRoot : NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.mixedEmbedding K sqrtTwoRoot

theorem mixedEmbedding_sqrtTwoRoot_mem_convexBodyLT
    (f : NumberField.InfinitePlace K → NNReal)
    (hf : ∀ w : NumberField.InfinitePlace K, w sqrtTwoRoot < f w) :
    mixedEmbedding_sqrtTwoRoot ∈ NumberField.mixedEmbedding.convexBodyLT K f := by
  sorry

theorem measurableSet_fundamentalCone :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone K) := by
  sorry

theorem measurableSet_normLeOne :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone.normLeOne K) := by
  sorry

theorem polarSpace_nonempty :
    Nonempty (NumberField.mixedEmbedding.polarSpace K) := by
  sorry

theorem fundamentalUnit_smul_mem_fundamentalCone
    {x : NumberField.mixedEmbedding.mixedSpace K}
    (hx : x ∈ NumberField.mixedEmbedding.fundamentalCone K) :
    (sqrtTwoFundamentalUnit : (𝓞 K)ˣ) • x ∈ NumberField.mixedEmbedding.fundamentalCone K := by
  sorry

end NumberField.SqrtTwo
