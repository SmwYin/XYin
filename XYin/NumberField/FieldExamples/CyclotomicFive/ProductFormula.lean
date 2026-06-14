/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicFive.Embeddings
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# Product formula examples in `ℚ(ζ₅)`
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicFive

theorem product_formula_zeta :
    ((∏ w : NumberField.InfinitePlace K, w ζ ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K, v ζ) = 1 := by
  sorry

theorem product_formula_fundamentalUnit :
    ((∏ w : NumberField.InfinitePlace K,
          w (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K,
          v (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))) = 1 := by
  sorry

end NumberField.CyclotomicFive
