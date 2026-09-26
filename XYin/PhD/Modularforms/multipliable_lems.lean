/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Infinite products of nonnegative reals

Mathlib's comparison lemmas `hasProd_le`, `tprod_le_one` need an ordered monoid, which `(ℝ, *)` is
not. Here we compare infinite products of nonnegative real factors.
-/

@[expose] public section

variable {ι : Type*} {a a₁ a₂ : ℝ}

/-- Infinite products of nonnegative reals are monotone in the factors. -/
theorem hasProd_le_nonneg (f g : ι → ℝ) (h : ∀ i, f i ≤ g i) (h0 : ∀ i, 0 ≤ f i)
    (hf : HasProd f a₁) (hg : HasProd g a₂) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto' hf hg fun _ ↦ Finset.prod_le_prod (fun i _ ↦ h0 i) (fun i _ ↦ h i)

/-- An infinite product of factors in `[0, 1]` is at most `1`. -/
theorem HasProd.le_one_nonneg (g : ι → ℝ) (h : ∀ i, g i ≤ 1) (h0 : ∀ i, 0 ≤ g i)
    (ha : HasProd g a) : a ≤ 1 :=
  hasProd_le_nonneg g (fun _ ↦ 1) h h0 ha hasProd_one

/-- An infinite product of factors in `[0, 1]` is at most `1`. -/
theorem tprod_le_one_of_nonneg (g : ι → ℝ) (h : ∀ i, g i ≤ 1) (h0 : ∀ i, 0 ≤ g i) :
    ∏' i, g i ≤ 1 := by
  by_cases hg : Multipliable g
  · exact hg.hasProd.le_one_nonneg g h h0
  · rw [tprod_eq_one_of_not_multipliable hg]
