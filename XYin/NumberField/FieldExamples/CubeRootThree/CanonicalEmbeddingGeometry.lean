/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.PolarCoord

/-!
# Canonical embedding geometry for `ℚ(∛3)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open MeasureTheory

namespace NumberField.CubeRootThree

abbrev mixedEmbedding_cubeRootThree : NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.mixedEmbedding K cubeRootThree

theorem mixedEmbedding_cubeRootThree_mem_convexBodyLT
    (f : NumberField.InfinitePlace K → NNReal)
    (hf : ∀ w : NumberField.InfinitePlace K, w cubeRootThree < f w) :
    mixedEmbedding_cubeRootThree ∈ NumberField.mixedEmbedding.convexBodyLT K f := by
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

end NumberField.CubeRootThree
