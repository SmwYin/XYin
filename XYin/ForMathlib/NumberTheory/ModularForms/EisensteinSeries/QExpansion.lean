/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# q-expansions of the normalized level-one Eisenstein series

The coefficient formulas for `E₄` and `E₆`, with the Bernoulli value needed for weight six.
Copied from `XYin.PhD.Modularforms.Eisenstein`.
-/

@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane ArithmeticFunction
open scoped ArithmeticFunction.sigma

noncomputable section

/-- The `q`-expansion of `E₄`: `E₄ = 1 + 240 ∑ σ₃(m) qᵐ`. -/
lemma E₄_q_exp : (fun m ↦ (qExpansion 1 E₄).coeff m) =
    fun m ↦ if m = 0 then 1 else (240 : ℂ) * (σ 3 m) := by
  funext m
  convert E_qExpansion_coeff (show 3 ≤ 4 by decide) (show Even 4 from ⟨2, rfl⟩) m using 1
  norm_num [E₄, ModularForm.E, show bernoulli 4 = -1 / 30 by
    norm_num [bernoulli_eq_bernoulli'_of_ne_one], div_eq_mul_inv]

/-- The Bernoulli number `B'₆ = 1/42` (mathlib stops at `bernoulli'_four`). -/
@[simp]
theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_eq_zero_of_odd (show Odd 5 by decide),
    show Nat.choose 6 2 = 15 by decide, show Nat.choose 6 4 = 15 by decide]

/-- The `q`-expansion of `E₆`: `E₆ = 1 - 504 ∑ σ₅(m) qᵐ`. -/
lemma E₆_q_exp : (fun m ↦ (qExpansion 1 E₆).coeff m) =
    fun m ↦ if m = 0 then 1 else -(504 : ℂ) * (σ 5 m) := by
  funext m
  convert E_qExpansion_coeff (show 3 ≤ 6 by decide) (show Even 6 from ⟨3, rfl⟩) m using 1
  norm_num [E₆, ModularForm.E, show bernoulli 6 = 1 / 42 by
    norm_num [bernoulli_eq_bernoulli'_of_ne_one], div_eq_mul_inv]

