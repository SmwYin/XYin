/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CubeRootThree.Embeddings
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Canonical embedding of `ℚ(∛3)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CubeRootThree

theorem canonicalEmbedding_apply_cubeRootThree (σ : K →+* ℂ) :
    NumberField.canonicalEmbedding K cubeRootThree σ = σ cubeRootThree := by
  rfl

theorem canonicalEmbedding_thetaInt_mem_integerLattice :
    NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K thetaInt) ∈
      NumberField.canonicalEmbedding.integerLattice K := by
  sorry

end NumberField.CubeRootThree
