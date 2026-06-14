/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtNegSix.Embeddings
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# Product formula examples in `ℚ(√-6)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtNegSix

theorem product_formula_theta :
    ((∏ w : NumberField.InfinitePlace K, w θ ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K, v θ) = 1 := by
  sorry

theorem product_formula_torsionGenerator :
    ((∏ w : NumberField.InfinitePlace K,
          w (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K)) ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K,
          v (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K))) = 1 := by
  sorry

end NumberField.SqrtNegSix
