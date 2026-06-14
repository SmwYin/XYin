/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicEight.Embeddings
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Canonical embedding of `ℚ(ζ₈)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

theorem canonicalEmbedding_apply_zeta (σ : K →+* ℂ) :
    NumberField.canonicalEmbedding K ζ σ = σ ζ := by
  rfl

theorem canonicalEmbedding_zetaInt_mem_integerLattice :
    NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K zetaInt) ∈
      NumberField.canonicalEmbedding.integerLattice K := by
  sorry

end NumberField.CyclotomicEight
