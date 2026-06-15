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
  exact NumberField.prod_abs_eq_one (K := K) (x := θ) (by
    intro h
    have hsq := theta_sq
    rw [h] at hsq
    norm_num at hsq)

theorem product_formula_torsionGenerator :
    ((∏ w : NumberField.InfinitePlace K,
          w (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K)) ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace K,
          v (algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K))) = 1 := by
  exact NumberField.prod_abs_eq_one (K := K)
    (x := algebraMap (𝓞 K) K (torsionGenerator : 𝓞 K)) (by
      intro h
      exact Units.ne_zero torsionGenerator (RingOfIntegers.coe_injective h))

end NumberField.SqrtNegSix
