/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Meromorphy at a cusp via at most exponential growth

A meromorphic function on the upper half-plane which is periodic descends to a function `G` on a
punctured disc via the parameter `q = exp (2 * π * I * τ / h)`.  This file characterises when `G`
extends meromorphically to `q = 0` by a growth condition which does not mention `q` at all:

* `UpperHalfPlane.HasAtMostExpGrowthAtImInfty`: `g` is holomorphic on a half-plane `Y ≤ im τ`
  (for a meromorphic function, the assertion that it has no poles high up) and satisfies
  `‖g τ‖ ≤ C * exp (ρ * im τ)` there, for some `ρ ≥ 0`, `C > 0`, `Y > 0`.

* `UpperHalfPlane.meromorphicAt_cuspFunction_iff_hasAtMostExpGrowthAtImInfty`: for `h`-periodic
  `g`, the cusp function of `g` is meromorphic at `q = 0` iff `g` has at most exponential growth
  at `∞`.  The intermediate condition, that `τ ↦ 𝕢 h τ ^ N * g τ` is bounded at `∞` for some
  natural `N`, is recorded in `meromorphicAt_cuspFunction_iff_exists_isBoundedAtImInfty` and
  `hasAtMostExpGrowthAtImInfty_iff_exists_isBoundedAtImInfty`.

* `UpperHalfPlane.HasAtMostExpGrowthAtCusp`: a weakly modular function `f` has at most
  exponential growth at the cusp represented by `γ` if `f ∣[k] γ` has at most exponential growth
  at `∞`; this is independent of the representative `γ` of the cusp
  (`hasAtMostExpGrowthAtCusp_congr`), so it characterises meromorphy at the cusp without
  reference to the cusp width (`meromorphicAt_cuspFunction_slash_iff_hasAtMostExpGrowthAtCusp`).

The statements are phrased for arbitrary functions `g : ℍ → ℂ`: each condition carries its own
holomorphy-near-`∞` clause, so no global meromorphy hypothesis on `ℍ` is needed, and the informal
statements for meromorphic functions are special cases.
-/

@[expose] public section

open Complex Filter Function Asymptotics ModularForm
open scoped Real Topology Manifold MatrixGroups

noncomputable section

local notation "𝕢" => Function.Periodic.qParam

namespace UpperHalfPlane

/-- A function `g : ℍ → ℂ` has **at most exponential growth at `∞`** if there are constants
`ρ ≥ 0`, `C > 0` and `Y > 0` such that `g` is holomorphic on the half-plane `Y ≤ im τ` and
satisfies `‖g τ‖ ≤ C * Real.exp (ρ * im τ)` there.

For a meromorphic function the holomorphy clause is the assertion that the function has no poles
on a sufficiently high half-plane, which is part of the informal definition. -/
def HasAtMostExpGrowthAtImInfty (g : ℍ → ℂ) : Prop :=
  ∃ ρ C Y : ℝ, 0 ≤ ρ ∧ 0 < C ∧ 0 < Y ∧ (∀ τ : ℍ, Y ≤ τ.im → MDiffAt g τ) ∧
    ∀ τ : ℍ, Y ≤ τ.im → ‖g τ‖ ≤ C * Real.exp (ρ * τ.im)

/-- `g` has at most exponential growth at `∞` iff it is eventually holomorphic and satisfies
`g = O (exp (ρ * im τ))` along `atImInfty` for some `ρ ≥ 0`.  This is the `Asymptotics.IsBigO`
form of the definition; the estimate is uniform in `re τ` because `atImInfty` only constrains
the imaginary part. -/
lemma hasAtMostExpGrowthAtImInfty_iff {g : ℍ → ℂ} :
    HasAtMostExpGrowthAtImInfty g ↔
      (∀ᶠ τ in atImInfty, MDiffAt g τ) ∧
        ∃ ρ : ℝ, 0 ≤ ρ ∧ g =O[atImInfty] fun τ ↦ Real.exp (ρ * τ.im) := by
  constructor
  · rintro ⟨ρ, C, Y, hρ, hC, hY, hd, hb⟩
    refine ⟨(atImInfty_mem _).mpr ⟨Y, hd⟩, ρ, hρ, isBigO_iff.mpr ⟨C, ?_⟩⟩
    refine (atImInfty_mem _).mpr ⟨Y, fun τ hτ ↦ ?_⟩
    simpa [Real.norm_of_nonneg (Real.exp_pos _).le] using hb τ hτ
  · rintro ⟨hev, ρ, hρ, hO⟩
    obtain ⟨Y₁, hY₁⟩ := (atImInfty_mem _).mp hev
    obtain ⟨C, hC⟩ := hO.bound
    obtain ⟨Y₂, hY₂⟩ := (atImInfty_mem _).mp hC
    refine ⟨ρ, max C 1, max (max Y₁ Y₂) 1, hρ, lt_of_lt_of_le one_pos (le_max_right _ _),
      lt_of_lt_of_le one_pos (le_max_right _ _), fun τ hτ ↦ ?_, fun τ hτ ↦ ?_⟩
    · exact hY₁ τ ((le_max_left Y₁ Y₂).trans ((le_max_left _ 1).trans hτ))
    · have h1 : ‖g τ‖ ≤ C * ‖Real.exp (ρ * τ.im)‖ :=
        hY₂ τ ((le_max_right Y₁ Y₂).trans ((le_max_left _ 1).trans hτ))
      rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.exp_pos _).le)

end UpperHalfPlane
