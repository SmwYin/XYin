/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.PolarCoord

/-!
# Canonical embedding geometry for `ℚ(√-6)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open MeasureTheory

namespace NumberField.SqrtNegSix

abbrev mixedEmbedding_theta : NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.mixedEmbedding K θ

theorem mixedEmbedding_theta_mem_convexBodyLT
    (f : NumberField.InfinitePlace K → NNReal)
    (hf : ∀ w : NumberField.InfinitePlace K, w θ < f w) :
    mixedEmbedding_theta ∈ NumberField.mixedEmbedding.convexBodyLT K f := by
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ,
    NumberField.mixedEmbedding.mixedEmbedding_apply_isReal, Metric.mem_ball, dist_zero_right,
    Real.norm_eq_abs, forall_const, Subtype.forall,
    NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
  constructor
  · intro a ha
    exact False.elim ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr ha)
      (infinitePlace_isComplex a))
  · intro a _ha
    simpa [NumberField.InfinitePlace.norm_embedding_eq a θ] using hf a

theorem measurableSet_fundamentalCone :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone K) := by
  exact NumberField.mixedEmbedding.measurableSet_fundamentalCone K

theorem measurableSet_normLeOne :
    MeasurableSet (NumberField.mixedEmbedding.fundamentalCone.normLeOne K) := by
  exact NumberField.mixedEmbedding.fundamentalCone.measurableSet_normLeOne K

theorem polarSpace_nonempty :
    Nonempty (NumberField.mixedEmbedding.polarSpace K) := by
  infer_instance

end NumberField.SqrtNegSix
