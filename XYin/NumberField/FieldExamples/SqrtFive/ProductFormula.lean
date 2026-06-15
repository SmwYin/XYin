/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtFive.Embeddings
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# Product formula examples in `ℚ(√5)`
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

namespace NumberField.SqrtFive

theorem product_formula_goldenRoot :
    ((∏ w : NumberField.InfinitePlace K, w goldenRoot ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K, v goldenRoot) = 1 := by
  exact NumberField.prod_abs_eq_one (K := K) (x := goldenRoot) (by
    intro h
    have hsq := goldenRoot_sq
    rw [h] at hsq
    norm_num at hsq)

theorem product_formula_fundamentalUnit :
    ((∏ w : NumberField.InfinitePlace K,
          w (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K,
          v (algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K))) = 1 := by
  exact NumberField.prod_abs_eq_one (K := K)
    (x := algebraMap (𝓞 K) K (fundamentalUnit : 𝓞 K)) (by
      intro h
      exact Units.ne_zero fundamentalUnit (RingOfIntegers.coe_injective h))

end NumberField.SqrtFive
