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
  exact (NumberField.mixedEmbedding.convexBodyLT_mem (K := K) (f := f) (x := sqrtTwoRoot)).2 hf

theorem measurableSet_fundamentalCone :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone K) := by
  exact NumberField.mixedEmbedding.measurableSet_fundamentalCone K

theorem measurableSet_normLeOne :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone.normLeOne K) := by
  exact NumberField.mixedEmbedding.fundamentalCone.measurableSet_normLeOne K

theorem polarSpace_nonempty :
    Nonempty (NumberField.mixedEmbedding.polarSpace K) := by
  infer_instance

/-- In `ℚ(√2)`, a unit sends a point of the fundamental cone back into the same
fundamental cone iff it is one of the two roots of unity `±1`. -/
theorem unit_smul_mem_fundamentalCone_iff_eq_one_or_neg_one
    {x : NumberField.mixedEmbedding.mixedSpace K}
    (hx : x ∈ NumberField.mixedEmbedding.fundamentalCone K)
    (u : (𝓞 K)ˣ) :
    u • x ∈ NumberField.mixedEmbedding.fundamentalCone K ↔ u = 1 ∨ u = -1 := by
  rw [NumberField.mixedEmbedding.fundamentalCone.unit_smul_mem_iff_mem_torsion hx u]
  exact mem_torsion_iff_eq_one_or_neg_one u

end NumberField.SqrtTwo
