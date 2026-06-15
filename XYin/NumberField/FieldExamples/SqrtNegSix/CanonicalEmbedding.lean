/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.Embeddings
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Canonical embedding of `ℚ(√-6)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

theorem canonicalEmbedding_apply_theta (σ : K →+* ℂ) :
    NumberField.canonicalEmbedding K θ σ = σ θ := by
  rfl

theorem canonicalEmbedding_thetaInt_mem_integerLattice :
    NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K thetaInt) ∈
      NumberField.canonicalEmbedding.integerLattice K := by
  simp [NumberField.canonicalEmbedding.integerLattice]

end NumberField.SqrtNegSix
