/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.PolarCoord

/-!
# Canonical embedding geometry for `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open MeasureTheory

namespace NumberField.SqrtFive

abbrev mixedEmbedding_goldenRoot : NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.mixedEmbedding K goldenRoot

theorem mixedEmbedding_goldenRoot_mem_convexBodyLT
    (f : NumberField.InfinitePlace K → NNReal)
    (hf : ∀ w : NumberField.InfinitePlace K, w goldenRoot < f w) :
    mixedEmbedding_goldenRoot ∈ NumberField.mixedEmbedding.convexBodyLT K f := by
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ,
    NumberField.mixedEmbedding.mixedEmbedding_apply_isReal, Metric.mem_ball,
    dist_zero_right, Real.norm_eq_abs, forall_const, Subtype.forall,
    NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
  constructor
  · intro a ha
    simpa [← NumberField.InfinitePlace.norm_embedding_of_isReal ha goldenRoot] using hf a
  · intro a ha
    have hreal := infinitePlace_isReal a
    have hnot : ¬ NumberField.InfinitePlace.IsReal a :=
      NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr ha
    exact False.elim (hnot hreal)

theorem measurableSet_fundamentalCone :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone K) := by
  exact NumberField.mixedEmbedding.measurableSet_fundamentalCone K

theorem measurableSet_normLeOne :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone.normLeOne K) := by
  exact NumberField.mixedEmbedding.fundamentalCone.measurableSet_normLeOne K

theorem polarSpace_nonempty :
    Nonempty (NumberField.mixedEmbedding.polarSpace K) := by
  infer_instance

end NumberField.SqrtFive
