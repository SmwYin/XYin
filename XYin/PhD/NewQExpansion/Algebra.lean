/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
module

public import XYin.PhD.NewQExpansion.Basic

/-!
# Algebra of q-expansions at cusp representatives

The q-expansion of a product of slash-invariant forms of different weights is the product
of their q-expansions, provided their cusp functions are analytic at zero.
For a fixed weight and representative, the q-expansion determines a form whose slash
transform is holomorphic on the upper half-plane and bounded at infinity.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm
open scoped MatrixGroups Manifold

namespace SlashInvariantForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k₁ k₂ : ℤ} {γ : SL(2, ℤ)}

/-- Multiplication of forms, with weights added, multiplies their q-expansions. -/
lemma qExpansionAt_mul [Γ.HasDetPlusMinusOne]
    (f : SlashInvariantForm Γ k₁) (g : SlashInvariantForm Γ k₂)
    (hf : AnalyticAt ℂ (cuspFunction (Γ.strictWidthAt γ) (f ∣[k₁] γ)) 0)
    (hg : AnalyticAt ℂ (cuspFunction (Γ.strictWidthAt γ) (g ∣[k₂] γ)) 0) :
    (f.mul g).qExpansionAt γ = f.qExpansionAt γ * g.qExpansionAt γ := by
  simpa only [qExpansionAt, coe_mul, mul_slash_SL2] using qExpansion_mul hf hg

/-- Holomorphy and boundedness of the slash transforms imply multiplicativity. -/
lemma qExpansionAt_mul_of_mdifferentiable [Γ.HasDetPlusMinusOne]
    (f : SlashInvariantForm Γ k₁) (g : SlashInvariantForm Γ k₂)
    (hh : 0 < Γ.strictWidthAt γ)
    (hfhol : MDiff ((f : ℍ → ℂ) ∣[k₁] γ))
    (hfbdd : IsBoundedAtImInfty (f ∣[k₁] γ))
    (hghol : MDiff ((g : ℍ → ℂ) ∣[k₂] γ))
    (hgbdd : IsBoundedAtImInfty (g ∣[k₂] γ)) :
    (f.mul g).qExpansionAt γ = f.qExpansionAt γ * g.qExpansionAt γ :=
  f.qExpansionAt_mul g
    (analyticAt_cuspFunction_zero hh (f.periodic_slash_strictWidthAt γ) hfhol hfbdd)
    (analyticAt_cuspFunction_zero hh (g.periodic_slash_strictWidthAt γ) hghol hgbdd)

/-- A q-expansion determines a form of a fixed weight when its slash transform is
holomorphic on the upper half-plane and bounded at infinity. -/
lemma qExpansionAt_inj {k : ℤ} (f g : SlashInvariantForm Γ k)
    (hh : 0 < Γ.strictWidthAt γ)
    (hfhol : MDiff ((f : ℍ → ℂ) ∣[k] γ))
    (hfbdd : IsBoundedAtImInfty (f ∣[k] γ))
    (hghol : MDiff ((g : ℍ → ℂ) ∣[k] γ))
    (hgbdd : IsBoundedAtImInfty (g ∣[k] γ)) :
    f.qExpansionAt γ = g.qExpansionAt γ ↔ f = g := by
  constructor
  · intro hfg
    have hslash : (f : ℍ → ℂ) ∣[k] γ = (g : ℍ → ℂ) ∣[k] γ := by
      funext τ
      have hg := g.hasSum_qExpansionAt hh hghol hgbdd τ
      rw [← hfg] at hg
      exact (f.hasSum_qExpansionAt hh hfhol hfbdd τ).unique hg
    apply DFunLike.coe_injective
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using
      congrArg (fun u : ℍ → ℂ ↦ u ∣[k] γ⁻¹) hslash
  · rintro rfl
    rfl

end SlashInvariantForm
