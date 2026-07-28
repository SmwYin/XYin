/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Tactic.TFAE

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

variable {h : ℝ} {g : ℍ → ℂ}

/-- Conditions (2) and (3) of the proposition are equivalent: `g` has at most exponential growth
at `∞` iff it is holomorphic on a sufficiently high half-plane and `τ ↦ 𝕢 h τ ^ N * g τ` is
bounded at `∞` for some natural `N`.  This equivalence requires no periodicity assumption. -/
theorem hasAtMostExpGrowthAtImInfty_iff_exists_isBoundedAtImInfty (hh : 0 < h) :
    HasAtMostExpGrowthAtImInfty g ↔
      (∀ᶠ τ in atImInfty, MDiffAt g τ) ∧
        ∃ N : ℕ, IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 h τ ^ N * g τ := by
  constructor
  · rintro ⟨ρ, C, Y, hρ, hC, hY, hd, hb⟩
    refine ⟨(atImInfty_mem _).mpr ⟨Y, hd⟩, ⌈ρ * h / (2 * π)⌉₊,
      isBoundedAtImInfty_iff.mpr ⟨C, Y, fun τ hτ ↦ ?_⟩⟩
    set N : ℕ := ⌈ρ * h / (2 * π)⌉₊ with hN
    have h1 : ρ * h ≤ N * (2 * π) := by
      have := Nat.le_ceil (ρ * h / (2 * π))
      rwa [div_le_iff₀ (by positivity), ← hN] at this
    have hexp_le : ρ * τ.im + (N : ℝ) * (-2 * π * τ.im / h) ≤ 0 := by
      have h2 : (N : ℝ) * (-2 * π * τ.im / h) = -((N * (2 * π)) * (τ.im / h)) := by ring
      have h3 : ρ * τ.im = (ρ * h) * (τ.im / h) := by field_simp
      have h4 : (0 : ℝ) ≤ τ.im / h := by positivity
      rw [h2, h3]
      have := mul_le_mul_of_nonneg_right h1 h4
      linarith
    calc ‖𝕢 h τ ^ N * g τ‖
        = Real.exp ((N : ℝ) * (-2 * π * τ.im / h)) * ‖g τ‖ := by
          rw [norm_mul, norm_pow, Periodic.norm_qParam, coe_im, ← Real.exp_nat_mul]
      _ ≤ Real.exp ((N : ℝ) * (-2 * π * τ.im / h)) * (C * Real.exp (ρ * τ.im)) :=
          mul_le_mul_of_nonneg_left (hb τ hτ) (Real.exp_pos _).le
      _ = C * Real.exp (ρ * τ.im + (N : ℝ) * (-2 * π * τ.im / h)) := by
          rw [Real.exp_add]; ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left
          (by simpa using Real.exp_le_exp.mpr hexp_le) hC.le
      _ = C := mul_one C
  · rintro ⟨hev, N, hbdd⟩
    obtain ⟨Y₁, hY₁⟩ := (atImInfty_mem _).mp hev
    obtain ⟨M, A, hMA⟩ := isBoundedAtImInfty_iff.mp hbdd
    refine ⟨2 * π * N / h, max M 1, max (max Y₁ A) 1, div_nonneg (by positivity) hh.le,
      lt_of_lt_of_le one_pos (le_max_right _ _), lt_of_lt_of_le one_pos (le_max_right _ _),
      fun τ hτ ↦ hY₁ τ ((le_max_left Y₁ A).trans ((le_max_left _ 1).trans hτ)),
      fun τ hτ ↦ ?_⟩
    have hA : A ≤ τ.im := (le_max_right Y₁ A).trans ((le_max_left _ 1).trans hτ)
    have h1 : ‖𝕢 h τ ^ N * g τ‖ ≤ M := hMA τ hA
    have h2 : ‖𝕢 h τ ^ N * g τ‖ = Real.exp ((N : ℝ) * (-2 * π * τ.im / h)) * ‖g τ‖ := by
      rw [norm_mul, norm_pow, Periodic.norm_qParam, coe_im, ← Real.exp_nat_mul]
    rw [h2] at h1
    have hexp_pos := Real.exp_pos ((N : ℝ) * (-2 * π * τ.im / h))
    rw [← le_div_iff₀' hexp_pos] at h1
    have h3 : M / Real.exp ((N : ℝ) * (-2 * π * τ.im / h)) =
        M * Real.exp (2 * π * N / h * τ.im) := by
      rw [div_eq_mul_inv, ← Real.exp_neg,
        show -((N : ℝ) * (-2 * π * τ.im / h)) = 2 * π * N / h * τ.im by ring]
    rw [h3] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left M 1) (Real.exp_pos _).le)

/-- Conditions (1) and (2) of the proposition are equivalent: for an `h`-periodic function `g`,
the cusp function of `g` extends meromorphically to `q = 0` iff `g` is holomorphic on a
sufficiently high half-plane and `τ ↦ 𝕢 h τ ^ N * g τ` is bounded at `∞` for some natural
`N`. -/
theorem meromorphicAt_cuspFunction_iff_exists_isBoundedAtImInfty (hh : 0 < h)
    (hper : Periodic (g ∘ ofComplex) h) :
    MeromorphicAt (cuspFunction h g) 0 ↔
      (∀ᶠ τ in atImInfty, MDiffAt g τ) ∧
        ∃ N : ℕ, IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 h τ ^ N * g τ := by
  have hq : Tendsto (fun τ : ℍ ↦ 𝕢 h ↑τ) atImInfty (𝓝[≠] (0 : ℂ)) :=
    (Periodic.qParam_tendsto hh).comp tendsto_coe_atImInfty
  constructor
  · intro hmero
    constructor
    · filter_upwards [hq.eventually hmero.eventually_analyticAt] with τ hτ
      rw [mdifferentiableAt_iff]
      have hcomp : DifferentiableAt ℂ (cuspFunction h g ∘ 𝕢 h) ↑τ :=
        hτ.differentiableAt.comp (↑τ : ℂ) Periodic.differentiable_qParam.differentiableAt
      refine hcomp.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
      simpa only [comp_apply, ofComplex_apply_of_im_pos hz] using
        (eq_cuspFunction (⟨z, hz⟩ : ℍ) hh.ne' hper).symm
    · obtain ⟨n, hn⟩ := hmero
      obtain ⟨M, hM⟩ := (hn.continuousAt.tendsto.isBigO_one ℝ).bound
      refine ⟨n, ?_⟩
      have hev2 : ∀ᶠ (τ : ℍ) in atImInfty, ‖𝕢 h τ ^ n * g τ‖ ≤ M * 1 := by
        filter_upwards [(hq.mono_right nhdsWithin_le_nhds).eventually hM] with τ hτ
        simpa only [sub_zero, smul_eq_mul, eq_cuspFunction τ hh.ne' hper, Pi.one_apply,
          norm_one] using hτ
      obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hev2
      exact isBoundedAtImInfty_iff.mpr ⟨M * 1, A, hA⟩
  · rintro ⟨hev, N, hbdd⟩
    obtain ⟨Y₁, hY₁⟩ := (atImInfty_mem _).mp hev
    have hI : ∀ᶠ z in comap Complex.im atTop, DifferentiableAt ℂ (g ∘ ofComplex) z := by
      refine eventually_of_mem (preimage_mem_comap (Ici_mem_atTop (max Y₁ 1))) fun z hz ↦ ?_
      have h0 : 0 < z.im := lt_of_lt_of_le one_pos ((le_max_right Y₁ 1).trans hz)
      exact mdifferentiableAt_iff.mp (hY₁ ⟨z, h0⟩ ((le_max_left Y₁ 1).trans hz))
    have hGdiff : ∀ᶠ q in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (cuspFunction h g) q :=
      Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hper hI
    obtain ⟨M, A, hMA⟩ := isBoundedAtImInfty_iff.mp hbdd
    have hbound : ∀ᶠ q in 𝓝[≠] (0 : ℂ), ‖q ^ N * cuspFunction h g q‖ ≤ M := by
      have hr : (0 : ℝ) < min (Real.exp (-2 * π * A / h)) 1 := lt_min (Real.exp_pos _) one_pos
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
        self_mem_nhdsWithin] with q hqball hq0'
      have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq0'
      rw [mem_ball_zero_iff] at hqball
      have hq1 : ‖q‖ < 1 := hqball.trans_le (min_le_right _ _)
      have him : 0 < (Periodic.invQParam h q).im :=
        Periodic.im_invQParam_pos_of_norm_lt_one hh hq1 hq0
      have hqA : A < (Periodic.invQParam h q).im := by
        refine (Periodic.norm_qParam_lt_iff hh A _).mp ?_
        rw [Periodic.qParam_right_inv hh.ne' hq0]
        exact hqball.trans_le (min_le_left _ _)
      set τ' : ℍ := ⟨Periodic.invQParam h q, him⟩ with hτ'
      have hqτ : 𝕢 h ↑τ' = q := Periodic.qParam_right_inv hh.ne' hq0
      have hGq : cuspFunction h g q = g τ' := by
        conv_lhs => rw [← hqτ]
        exact eq_cuspFunction τ' hh.ne' hper
      have h1 := hMA τ' hqA.le
      rw [hqτ] at h1
      rwa [hGq]
    have hcont : ContinuousAt (fun q : ℂ ↦ q ^ (N + 1) * cuspFunction h g q) 0 := by
      have hev0 : ∀ᶠ q in 𝓝 (0 : ℂ), ‖q ^ (N + 1) * cuspFunction h g q‖ ≤ ‖q‖ * M := by
        rw [eventually_nhdsWithin_iff] at hbound
        filter_upwards [hbound] with q hq
        rcases eq_or_ne q 0 with rfl | hq0
        · simp
        · have h1 : ‖q ^ N * cuspFunction h g q‖ ≤ M :=
            hq (Set.mem_compl_singleton_iff.mpr hq0)
          calc ‖q ^ (N + 1) * cuspFunction h g q‖
              = ‖q‖ * ‖q ^ N * cuspFunction h g q‖ := by
                rw [pow_succ', mul_assoc, norm_mul]
            _ ≤ ‖q‖ * M := mul_le_mul_of_nonneg_left h1 (norm_nonneg q)
      have htend : Tendsto (fun q : ℂ ↦ q ^ (N + 1) * cuspFunction h g q) (𝓝 0) (𝓝 0) := by
        refine squeeze_zero_norm' hev0 ?_
        simpa using tendsto_norm_zero.mul_const M
      have h00 : (0 : ℂ) ^ (N + 1) * cuspFunction h g 0 = 0 := by simp
      rw [ContinuousAt, h00]
      exact htend
    have hdiff' : ∀ᶠ q in 𝓝[≠] (0 : ℂ),
        DifferentiableAt ℂ (fun q : ℂ ↦ q ^ (N + 1) * cuspFunction h g q) q := by
      filter_upwards [hGdiff] with q hq
      exact (differentiableAt_pow (N + 1)).mul hq
    have han : AnalyticAt ℂ (fun q : ℂ ↦ q ^ (N + 1) * cuspFunction h g q) 0 :=
      Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff' hcont
    exact ⟨N + 1, by simpa only [sub_zero, smul_eq_mul] using han⟩

/-- **Meromorphy at `∞` via growth.**  For an `h`-periodic function `g` on the upper half-plane,
the cusp function of `g` extends meromorphically to `q = 0` iff `g` has at most exponential
growth at `∞`.  This is the equivalence (1) ↔ (3) of the informal proposition; note that the
right-hand side does not mention the period `h`. -/
theorem meromorphicAt_cuspFunction_iff_hasAtMostExpGrowthAtImInfty (hh : 0 < h)
    (hper : Periodic (g ∘ ofComplex) h) :
    MeromorphicAt (cuspFunction h g) 0 ↔ HasAtMostExpGrowthAtImInfty g := by
  rw [meromorphicAt_cuspFunction_iff_exists_isBoundedAtImInfty hh hper,
    ← hasAtMostExpGrowthAtImInfty_iff_exists_isBoundedAtImInfty hh]

/-- The three conditions of the proposition, packaged as a `TFAE`:  (1) the cusp function of `g`
extends meromorphically to `q = 0`;  (2) `g` is holomorphic high up and `τ ↦ 𝕢 h τ ^ N * g τ`
is bounded at `∞` for some natural `N`;  (3) `g` has at most exponential growth at `∞`. -/
theorem meromorphicAt_cuspFunction_tfae (hh : 0 < h) (hper : Periodic (g ∘ ofComplex) h) :
    [MeromorphicAt (cuspFunction h g) 0,
      (∀ᶠ τ in atImInfty, MDiffAt g τ) ∧
        ∃ N : ℕ, IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 h τ ^ N * g τ,
      HasAtMostExpGrowthAtImInfty g].TFAE := by
  tfae_have 1 ↔ 2 := meromorphicAt_cuspFunction_iff_exists_isBoundedAtImInfty hh hper
  tfae_have 3 ↔ 2 := hasAtMostExpGrowthAtImInfty_iff_exists_isBoundedAtImInfty hh
  tfae_finish

end UpperHalfPlane
