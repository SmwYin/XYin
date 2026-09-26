/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
module

public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Behaviour at all cusps from behaviour at `i∞`

For an arithmetic subgroup `𝒢`, a function is zero (resp. bounded) at every cusp of `𝒢` as soon as
all its `SL(2, ℤ)`-translates are zero (resp. bounded) at `i∞`.

The limit at `i∞` is read off from the cusp function
(`UpperHalfPlane.tendsto_atImInfty_of_continuousAt_cuspFunction`); a modular form tends to the
constant coefficient of its `q`-expansion
(`ModularFormClass.tendsto_atImInfty_qExpansion_coeff_zero`).
-/

@[expose] public section

open scoped MatrixGroups ModularForm UpperHalfPlane Topology
open Filter

/-- If every `SL(2, ℤ)`-translate of `f` vanishes at `i∞`, then `f` vanishes at every cusp of an
arithmetic subgroup. -/
theorem zero_at_cusps_of_zero_at_infty {f : ℍ → ℂ} {c : OnePoint ℝ} {k : ℤ}
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic]
    (hc : IsCusp c 𝒢) (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsZeroAtImInfty (f ∣[k] A)) :
    c.IsZeroAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  exact (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr fun A _ ↦ hb A ⟨A, rfl⟩

/-- If every `SL(2, ℤ)`-translate of `f` is bounded at `i∞`, then `f` is bounded at every cusp of
an arithmetic subgroup. -/
theorem bounded_at_cusps_of_bounded_at_infty {f : ℍ → ℂ} {c : OnePoint ℝ} {k : ℤ}
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic]
    (hc : IsCusp c 𝒢) (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsBoundedAtImInfty (f ∣[k] A)) :
    c.IsBoundedAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  exact (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun A _ ↦ hb A ⟨A, rfl⟩

/-- A periodic function whose cusp function is continuous at `0` tends at `i∞` to the value of
its cusp function at `0`. -/
theorem UpperHalfPlane.tendsto_atImInfty_of_continuousAt_cuspFunction {h : ℝ} {f : ℍ → ℂ}
    (hh : 0 < h) (hper : Function.Periodic (f ∘ ofComplex) h)
    (hf : ContinuousAt (cuspFunction h f) 0) :
    Tendsto f atImInfty (𝓝 (cuspFunction h f 0)) := by
  simpa only [Function.comp_def, eq_cuspFunction _ hh.ne' hper] using
    hf.tendsto.comp (qParam_tendsto_atImInfty hh)

/-- A modular form tends at `i∞` to the constant coefficient of its `q`-expansion. -/
theorem ModularFormClass.tendsto_atImInfty_qExpansion_coeff_zero {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) :
    Tendsto f UpperHalfPlane.atImInfty (𝓝 ((UpperHalfPlane.qExpansion h f).coeff 0)) := by
  simpa [UpperHalfPlane.qExpansion_coeff] using
    UpperHalfPlane.tendsto_atImInfty_of_continuousAt_cuspFunction hh
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
      (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
