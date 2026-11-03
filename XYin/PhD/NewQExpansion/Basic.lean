/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
module

public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Power series q-expansions at cusp representatives

For a weakly modular form `f` of weight `k`, the q-expansion at the cusp point
`γ∞` with respect to `γ` and width `h` is `UpperHalfPlane.qExpansion h (f ∣[k] γ)`.
The parameter is `q_h = exp (2πiτ/h)` and the result is a `PowerSeries ℂ`.

`Subgroup.strictWidthAt Γ γ` is the strict width at `γ∞`, computed in `γ⁻¹ Γ γ`.
`SlashInvariantForm.qExpansionAt` uses this width automatically.
This definition requires no holomorphy, boundedness, or periodicity hypotheses. Without suitable
analytic hypotheses the resulting power series need not represent the function.
In particular, holomorphy on a high half-plane alone does not rule out a pole at the cusp.

We use strict width because mathlib's ordinary `widthInfty` allows `±T^h`, whereas
`strictWidthInfty` requires `T^h`. For odd weights the former need not be a period.
The strict width always gives a period of the slash transform. Analytic hypotheses are
imposed only in the relevant API lemmas.
The choice of `γ` is part of the data: even matrices representing the same cusp point
can give different series. Left multiplication by an element of the level group does
preserve the series.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm
open scoped MatrixGroups Manifold Pointwise

namespace Subgroup

variable (Γ : Subgroup (GL (Fin 2) ℝ))

/-- The strict width of the cusp represented by `γ∞`, computed after transport to infinity. -/
def strictWidthAt (γ : SL(2, ℤ)) : ℝ :=
  (ConjAct.toConjAct (γ : GL (Fin 2) ℝ)⁻¹ • Γ).strictWidthInfty

@[simp]
lemma strictWidthAt_one : Γ.strictWidthAt 1 = Γ.strictWidthInfty := by
  simp [strictWidthAt]

lemma strictWidthAt_nonneg (γ : SL(2, ℤ)) : 0 ≤ Γ.strictWidthAt γ :=
  strictWidthInfty_nonneg _

lemma strictWidthAt_mul_left (γ δ : SL(2, ℤ)) (hδ : (δ : GL (Fin 2) ℝ) ∈ Γ) :
    Γ.strictWidthAt (δ * γ) = Γ.strictWidthAt γ := by
  unfold strictWidthAt
  apply congrArg Subgroup.strictWidthInfty
  change ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ (δ * γ))⁻¹ • Γ = _
  rw [map_mul, mul_inv_rev, map_mul, mul_smul]
  congr 1
  exact Γ.conjAct_pointwise_smul_eq_self (Γ.le_normalizer (Γ.inv_mem hδ))

lemma strictWidthAt_pos [Γ.IsArithmetic] (γ : SL(2, ℤ)) : 0 < Γ.strictWidthAt γ := by
  have : (ConjAct.toConjAct (γ : GL (Fin 2) ℝ)⁻¹ • Γ).IsArithmetic := by
    change (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ • Γ).IsArithmetic
    simpa only [← (Rat.castHom ℝ).algebraMap_toAlgebra,
      Matrix.SpecialLinearGroup.map_mapGL, map_inv] using
      Subgroup.IsArithmetic.conj Γ (Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹)
  exact Subgroup.strictWidthInfty_pos _

end Subgroup

namespace SlashInvariantForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
  (f : SlashInvariantForm Γ k) (γ : SL(2, ℤ))

/-- The power series q-expansion at the cusp point `γ∞`, with respect to the representative `γ`
and the strict cusp width. No analytic hypotheses are required to define it. -/
def qExpansionAt : PowerSeries ℂ :=
  qExpansion (Γ.strictWidthAt γ) (f ∣[k] γ)

lemma qExpansionAt_coeff (n : ℕ) :
    (f.qExpansionAt γ).coeff n =
      (↑n.factorial)⁻¹ *
        iteratedDeriv n (cuspFunction (Γ.strictWidthAt γ) (f ∣[k] γ)) 0 :=
  qExpansion_coeff _ n

@[simp]
lemma qExpansionAt_one : f.qExpansionAt 1 = qExpansion Γ.strictWidthInfty f := by
  simp [qExpansionAt]

@[simp]
lemma qExpansionAt_zero : (0 : SlashInvariantForm Γ k).qExpansionAt γ = 0 := by
  simp [qExpansionAt, qExpansion_zero]

/-- Left multiplication by the level group preserves the chosen q-expansion. -/
lemma qExpansionAt_mul_left (δ : SL(2, ℤ)) (hδ : (δ : GL (Fin 2) ℝ) ∈ Γ) :
    f.qExpansionAt (δ * γ) = f.qExpansionAt γ := by
  simp only [qExpansionAt, Γ.strictWidthAt_mul_left γ δ hδ,
    SlashAction.slash_mul, SL_slash f δ,
    slash_action_eqn f _ hδ]

lemma qExpansionAt_of_mem (hγ : (γ : GL (Fin 2) ℝ) ∈ Γ) :
    f.qExpansionAt γ = qExpansion Γ.strictWidthInfty f := by
  simpa using f.qExpansionAt_mul_left 1 γ hγ

/-- The strict cusp width is a period of the transformed function. -/
lemma periodic_slash_strictWidthAt :
    Function.Periodic ((f ∣[k] γ) ∘ ofComplex) (Γ.strictWidthAt γ) :=
  SlashInvariantFormClass.periodic_comp_ofComplex
    (translate f (γ : GL (Fin 2) ℝ))
    (Subgroup.strictWidthInfty_mem_strictPeriods _)

variable {γ}

lemma qExpansionAt_coeff_zero
    (hh : 0 < Γ.strictWidthAt γ)
    (hf : AnalyticAt ℂ (cuspFunction (Γ.strictWidthAt γ) (f ∣[k] γ)) 0) :
    (f.qExpansionAt γ).coeff 0 = valueAtInfty (f ∣[k] γ) :=
  qExpansion_coeff_zero hh hf (f.periodic_slash_strictWidthAt γ)

/-- With holomorphy and boundedness at infinity, the series sums to the slash transform. -/
lemma hasSum_qExpansionAt
    (hh : 0 < Γ.strictWidthAt γ)
    (hfhol : MDiff ((f : ℍ → ℂ) ∣[k] γ))
    (hfbdd : IsBoundedAtImInfty (f ∣[k] γ)) (τ : ℍ) :
    HasSum (fun n : ℕ ↦
      (f.qExpansionAt γ).coeff n • Function.Periodic.qParam (Γ.strictWidthAt γ) τ ^ n)
      (((f : ℍ → ℂ) ∣[k] γ) τ) :=
  hasSum_qExpansion hh (f.periodic_slash_strictWidthAt γ) hfhol hfbdd τ

lemma qExpansionAt_eq_zero_iff
    (hh : 0 < Γ.strictWidthAt γ)
    (hfhol : MDiff ((f : ℍ → ℂ) ∣[k] γ))
    (hfbdd : IsBoundedAtImInfty (f ∣[k] γ)) :
    f.qExpansionAt γ = 0 ↔ f = 0 := by
  rw [qExpansionAt,
    qExpansion_eq_zero_iff hh (f.periodic_slash_strictWidthAt γ) hfhol hfbdd,
    SlashAction.slash_eq_zero_iff]
  exact DFunLike.coe_injective.eq_iff' rfl

lemma qExpansionAt_add (g : SlashInvariantForm Γ k)
    (hf : AnalyticAt ℂ (cuspFunction (Γ.strictWidthAt γ) (f ∣[k] γ)) 0)
    (hg : AnalyticAt ℂ (cuspFunction (Γ.strictWidthAt γ) (g ∣[k] γ)) 0) :
    (f + g).qExpansionAt γ = f.qExpansionAt γ + g.qExpansionAt γ := by
  simpa [qExpansionAt] using qExpansion_add hf hg

lemma qExpansionAt_neg
    (hf : AnalyticAt ℂ (cuspFunction (Γ.strictWidthAt γ) (f ∣[k] γ)) 0) :
    (-f).qExpansionAt γ = -f.qExpansionAt γ := by
  simpa [qExpansionAt] using qExpansion_neg hf

lemma qExpansionAt_sub (g : SlashInvariantForm Γ k)
    (hf : AnalyticAt ℂ (cuspFunction (Γ.strictWidthAt γ) (f ∣[k] γ)) 0)
    (hg : AnalyticAt ℂ (cuspFunction (Γ.strictWidthAt γ) (g ∣[k] γ)) 0) :
    (f - g).qExpansionAt γ = f.qExpansionAt γ - g.qExpansionAt γ := by
  simpa [qExpansionAt, sub_eq_add_neg] using qExpansion_sub hf hg

lemma qExpansionAt_smul [Γ.HasDetOne] (a : ℂ)
    (hf : AnalyticAt ℂ (cuspFunction (Γ.strictWidthAt γ) (f ∣[k] γ)) 0) :
    (a • f).qExpansionAt γ = a • f.qExpansionAt γ := by
  simpa [qExpansionAt, SL_smul_slash] using qExpansion_smul hf a

end SlashInvariantForm
