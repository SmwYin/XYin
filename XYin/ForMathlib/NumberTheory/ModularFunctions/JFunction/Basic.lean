/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

/-!
# The modular j-function

This file defines the classical modular invariant `j = E₄ ^ 3 / Δ` and proves its holomorphy,
invariance under `SL₂(ℤ)`, and one-periodicity.

Its regularization, integral coefficients, pole at infinity, and Laurent q-expansion are developed
in `XYin.ForMathlib.NumberTheory.ModularFunctions.JFunction.QExpansion`.
-/

open Complex Function MatrixGroups ModularForm ModularFormClass SlashInvariantFormClass
  UpperHalfPlane
open scoped Manifold

noncomputable section

/-- The classical modular invariant `j = E₄ ^ 3 / Δ`. -/
def j : ℍ → ℂ := fun τ ↦ E₄ τ ^ 3 / discriminant τ

/-- The modular invariant is holomorphic on the upper half-plane. -/
lemma j_mdifferentiable : MDiff j := by
  change MDiff ((⇑E₄) ^ 3 / ⇑CuspForm.discriminant)
  exact ((ModularFormClass.holo E₄).pow 3).div
    (ModularFormClass.holo CuspForm.discriminant) discriminant_ne_zero

/-- The modular invariant `j` is invariant under the weight-zero slash action of `SL₂(ℤ)`. -/
lemma j_slash_invariant (γ : SL(2, ℤ)) : j ∣[(0 : ℤ)] γ = j := by
  let f := E₄.mul (E₄.mul E₄)
  have hj : j = (f : ℍ → ℂ) / discriminant := by
    simp only [f, ModularForm.coe_mul]
    ext z
    simp [j, pow_three]
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  rw [hj]
  change ((f : ℍ → ℂ) / CuspForm.discriminant) ∣[(12 - 12 : ℤ)] γ = _
  rw [div_slash_SL2, SL_slash, SL_slash]
  exact congrArg₂ (· / ·) (f.slash_action_eq' γ hγ) (CuspForm.discriminant.slash_action_eq' γ hγ)

/-- The modular invariant `j` is unchanged by the action of `SL₂(ℤ)`. -/
lemma j_modularGroup_smul (γ : SL(2, ℤ)) (z : ℍ) : j (γ • z) = j z := by
  have h := congrFun (j_slash_invariant γ) z
  simpa only [SL_slash_apply, neg_zero, zpow_zero, mul_one] using h

/-- The complex extension of the modular invariant is one-periodic. -/
lemma j_periodic : Periodic (j ∘ UpperHalfPlane.ofComplex) 1 := by
  simpa [j, Periodic, Function.comp_def] using
    ((SlashInvariantFormClass.periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL).comp
      (fun z : ℂ ↦ z ^ 3)).div
      (SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
        one_mem_strictPeriods_SL)

end
