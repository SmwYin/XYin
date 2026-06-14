/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.Embeddings
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Canonical embedding of `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

theorem canonicalEmbedding_apply_goldenRoot (σ : K →+* ℂ) :
    NumberField.canonicalEmbedding K goldenRoot σ = σ goldenRoot := by
  rfl

theorem canonicalEmbedding_goldenIntO_mem_integerLattice :
    NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K goldenIntO) ∈
      NumberField.canonicalEmbedding.integerLattice K := by
  sorry

theorem canonicalEmbedding_fundamentalUnit_coordinates :
    ∃ x : (K →+* ℂ) → ℂ,
      x = NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) := by
  sorry

end NumberField.SqrtFive
