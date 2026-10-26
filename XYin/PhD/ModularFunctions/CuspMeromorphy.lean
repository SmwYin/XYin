/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
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

/-- A function `f : ℍ → ℂ` has **at most exponential growth at the cusp** represented by
`γ ∈ SL(2, ℤ)`, with respect to the weight-`k` slash action, if `f ∣[k] γ` has at most
exponential growth at `∞`.

The informal definition is for `f` meromorphic and weakly modular with respect to a congruence
subgroup `Γ` and a cusp `c = [γ ∞]` of `Γ`; by `hasAtMostExpGrowthAtCusp_congr` the property
depends only on the cusp `c` and not on the chosen representative `γ`, and no meromorphy
hypothesis is needed to state it. -/
def HasAtMostExpGrowthAtCusp (k : ℤ) (γ : SL(2, ℤ)) (f : ℍ → ℂ) : Prop :=
  HasAtMostExpGrowthAtImInfty (f ∣[k] γ)

/-- **Meromorphy at a cusp via growth.**  Let `γ` represent a cusp and let `h` be a period of
`f ∣[k] γ` (for `f` weakly modular for `Γ` and a cusp of width `h`, weak modularity supplies
this periodicity).  Then `f` is meromorphic at the cusp in the usual local `q`-coordinate sense
iff `f` has at most exponential growth at the cusp.  The growth condition does not involve the
width `h`, so it characterises meromorphy at the cusp without reference to the width. -/
theorem meromorphicAt_cuspFunction_slash_iff_hasAtMostExpGrowthAtCusp {k : ℤ} {f : ℍ → ℂ}
    {γ : SL(2, ℤ)} (hh : 0 < h) (hper : Periodic ((f ∣[k] γ) ∘ ofComplex) h) :
    MeromorphicAt (cuspFunction h (f ∣[k] γ)) 0 ↔ HasAtMostExpGrowthAtCusp k γ f :=
  meromorphicAt_cuspFunction_iff_hasAtMostExpGrowthAtImInfty hh hper

/-- The three conditions of the corollary, packaged as a `TFAE`:  (1) `f` is meromorphic at the
cusp represented by `γ` in the local `q`-coordinate sense;  (2) `f ∣[k] γ` is holomorphic high
up and `τ ↦ 𝕢 h τ ^ N * (f ∣[k] γ) τ` is bounded at `∞` for some natural `N`;  (3) `f` has at
most exponential growth at the cusp. -/
theorem meromorphicAt_cusp_tfae {k : ℤ} {f : ℍ → ℂ} {γ : SL(2, ℤ)} (hh : 0 < h)
    (hper : Periodic ((f ∣[k] γ) ∘ ofComplex) h) :
    [MeromorphicAt (cuspFunction h (f ∣[k] γ)) 0,
      (∀ᶠ τ in atImInfty, MDiffAt (f ∣[k] γ) τ) ∧
        ∃ N : ℕ, IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 h τ ^ N * (f ∣[k] γ) τ,
      HasAtMostExpGrowthAtCusp k γ f].TFAE :=
  meromorphicAt_cuspFunction_tfae hh hper

section RepresentativeIndependence

/-- Slashing by `T ^ n` is horizontal translation by `n`: the automorphy factor is trivial. -/
lemma slash_T_zpow (g : ℍ → ℂ) (k n : ℤ) :
    g ∣[k] (ModularGroup.T ^ n : SL(2, ℤ)) = fun τ ↦ g (ModularGroup.T ^ n • τ) := by
  funext τ
  rw [SL_slash_apply]
  have hden : denom ((ModularGroup.T ^ n : SL(2, ℤ))) τ = 1 := by
    rw [ModularGroup.denom_apply]
    simp [ModularGroup.coe_T_zpow]
  rw [hden]
  simp

/-- Slashing by `-T ^ n` is horizontal translation by `n` up to the nonzero constant
`(-1) ^ k`. -/
lemma slash_neg_T_zpow (g : ℍ → ℂ) (k n : ℤ) :
    g ∣[k] (-ModularGroup.T ^ n : SL(2, ℤ)) = fun τ ↦ (-1) ^ k * g (ModularGroup.T ^ n • τ) := by
  funext τ
  rw [SL_slash_apply, ModularGroup.SL_neg_smul]
  have hden : denom ((-ModularGroup.T ^ n : SL(2, ℤ))) τ = -1 := by
    rw [ModularGroup.denom_apply]
    simp [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, ModularGroup.coe_T_zpow]
  rw [hden, mul_comm]
  congr 1
  rw [zpow_neg, ← inv_zpow, inv_neg_one]

/-- At most exponential growth at `∞` is preserved by multiplication by a constant. -/
lemma HasAtMostExpGrowthAtImInfty.const_mul {g : ℍ → ℂ}
    (hg : HasAtMostExpGrowthAtImInfty g) (c : ℂ) :
    HasAtMostExpGrowthAtImInfty fun τ ↦ c * g τ := by
  obtain ⟨ρ, C, Y, hρ, hC, hY, hd, hb⟩ := hg
  refine ⟨ρ, (‖c‖ + 1) * C, Y, hρ, mul_pos (by positivity) hC, hY, fun τ hτ ↦ ?_,
    fun τ hτ ↦ ?_⟩
  · rw [mdifferentiableAt_iff]
    exact (mdifferentiableAt_iff.mp (hd τ hτ)).const_mul c
  · rw [norm_mul]
    calc ‖c‖ * ‖g τ‖ ≤ (‖c‖ + 1) * (C * Real.exp (ρ * τ.im)) :=
        mul_le_mul (by linarith) (hb τ hτ) (norm_nonneg _) (by positivity)
      _ = (‖c‖ + 1) * C * Real.exp (ρ * τ.im) := by ring

/-- At most exponential growth at `∞` is invariant under multiplication by a nonzero
constant. -/
lemma hasAtMostExpGrowthAtImInfty_const_mul_iff {g : ℍ → ℂ} {c : ℂ} (hc : c ≠ 0) :
    HasAtMostExpGrowthAtImInfty (fun τ ↦ c * g τ) ↔ HasAtMostExpGrowthAtImInfty g := by
  refine ⟨fun hg ↦ ?_, fun hg ↦ hg.const_mul c⟩
  have h1 := hg.const_mul c⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using h1

/-- At most exponential growth at `∞` is preserved by horizontal translation, in the form of
precomposition with the action of `T ^ n`. -/
lemma HasAtMostExpGrowthAtImInfty.comp_T_zpow {g : ℍ → ℂ}
    (hg : HasAtMostExpGrowthAtImInfty g) (n : ℤ) :
    HasAtMostExpGrowthAtImInfty fun τ ↦ g (ModularGroup.T ^ n • τ) := by
  obtain ⟨ρ, C, Y, hρ, hC, hY, hd, hb⟩ := hg
  have him : ∀ τ : ℍ, (ModularGroup.T ^ n • τ).im = τ.im := fun τ ↦ by
    rw [modular_T_zpow_smul, vadd_im]
  refine ⟨ρ, C, Y, hρ, hC, hY, fun τ hτ ↦ ?_, fun τ hτ ↦ ?_⟩
  · have h1 : MDiffAt g (ModularGroup.T ^ n • τ) := hd _ (by rw [him]; exact hτ)
    have h2 : MDiffAt (fun z : ℍ ↦ ModularGroup.T ^ n • z) τ := by
      have h3 := mdifferentiable_smul
        (g := ((ModularGroup.T ^ n : SL(2, ℤ)) : GL (Fin 2) ℝ)) (by simp)
      simpa only [← ModularGroup.sl_moeb] using h3 τ
    exact h1.comp τ h2
  · have h1 := hb (ModularGroup.T ^ n • τ) (by rw [him]; exact hτ)
    rwa [him] at h1

/-- At most exponential growth at `∞` is invariant under horizontal translation. -/
lemma hasAtMostExpGrowthAtImInfty_comp_T_zpow_iff (g : ℍ → ℂ) (n : ℤ) :
    HasAtMostExpGrowthAtImInfty (fun τ ↦ g (ModularGroup.T ^ n • τ)) ↔
      HasAtMostExpGrowthAtImInfty g := by
  refine ⟨fun hg ↦ ?_, fun hg ↦ hg.comp_T_zpow n⟩
  have h1 := hg.comp_T_zpow (-n)
  simpa only [← mul_smul, ← zpow_add, add_neg_cancel, zpow_zero, one_smul] using h1

/-- **Well-definedness at the cusp.**  Let `f` be weakly modular of weight `k` for a subgroup
`Γ ≤ SL(2, ℤ)`.  If `γ' = δ * γ * η` with `δ ∈ Γ` and `η = ± T ^ n` (so that `γ'` and `γ`
represent the same cusp `[γ ∞]` of `Γ`), then `f` has at most exponential growth at the cusp
represented by `γ'` iff it has at most exponential growth at the cusp represented by `γ`.
Hence at most exponential growth at a cusp is independent of the chosen representative. -/
theorem hasAtMostExpGrowthAtCusp_congr {k : ℤ} {f : ℍ → ℂ} {Γ : Subgroup SL(2, ℤ)}
    (hf : ∀ δ ∈ Γ, f ∣[k] δ = f) {γ γ' δ η : SL(2, ℤ)} (hδ : δ ∈ Γ) {n : ℤ}
    (hη : η = ModularGroup.T ^ n ∨ η = -ModularGroup.T ^ n) (hγ' : γ' = δ * γ * η) :
    HasAtMostExpGrowthAtCusp k γ' f ↔ HasAtMostExpGrowthAtCusp k γ f := by
  have hslash : f ∣[k] γ' = (f ∣[k] γ) ∣[k] η := by
    rw [hγ', SlashAction.slash_mul, SlashAction.slash_mul, hf δ hδ]
  unfold HasAtMostExpGrowthAtCusp
  rw [hslash]
  rcases hη with rfl | rfl
  · rw [slash_T_zpow]
    exact hasAtMostExpGrowthAtImInfty_comp_T_zpow_iff _ n
  · rw [slash_neg_T_zpow,
      hasAtMostExpGrowthAtImInfty_const_mul_iff (zpow_ne_zero _ (by norm_num))]
    exact hasAtMostExpGrowthAtImInfty_comp_T_zpow_iff _ n

end RepresentativeIndependence

end UpperHalfPlane
