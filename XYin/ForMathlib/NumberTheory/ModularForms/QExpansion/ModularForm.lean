/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
module

public import XYin.ForMathlib.NumberTheory.ModularForms.QExpansion.Algebra
public import XYin.ForMathlib.NumberTheory.ModularForms.QExpansion.Order

/-!
# Q-expansions of modular forms at cusps

For modular forms on arithmetic subgroups, holomorphy and boundedness supply the
analytic hypotheses for the q-expansion at every integral cusp representative.
We use the q-expansion of the underlying slash-invariant form. For cusp forms,
the constant coefficient vanishes at every cusp.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm
open scoped MatrixGroups Manifold Pointwise

namespace ModularFormClass

variable {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
  [FunLike F ℍ ℂ] [ModularFormClass F Γ k] [Γ.IsArithmetic]

/-- The cusp function of a modular form in an integral cusp chart is analytic at zero. -/
lemma analyticAt_cuspFunction_slash_zero (f : F) (γ : SL(2, ℤ)) :
    AnalyticAt ℂ (cuspFunction (Γ.strictWidthAt γ) ((f : ℍ → ℂ) ∣[k] γ)) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero (Γ.strictWidthAt_pos γ)
    ((f : SlashInvariantForm Γ k).periodic_slash_strictWidthAt γ)
    ((holo f).slash k (γ : GL (Fin 2) ℝ)) (bdd_at_infty_slash f γ)

end ModularFormClass

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

/-- The constant coefficient is the value of the slash transform at infinity. -/
lemma qExpansionAt_coeff_zero (f : ModularForm Γ k) (γ : SL(2, ℤ)) :
    (f.toSlashInvariantForm.qExpansionAt γ).coeff 0 = valueAtInfty (f ∣[k] γ) :=
  f.toSlashInvariantForm.qExpansionAt_coeff_zero (Γ.strictWidthAt_pos γ)
    (ModularFormClass.analyticAt_cuspFunction_slash_zero f γ)

/-- At every integral cusp representative, a modular form is the sum of its q-expansion. -/
lemma hasSum_qExpansionAt (f : ModularForm Γ k) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasSum (fun n : ℕ ↦
      (f.toSlashInvariantForm.qExpansionAt γ).coeff n •
        Function.Periodic.qParam (Γ.strictWidthAt γ) τ ^ n)
      (((f : ℍ → ℂ) ∣[k] γ) τ) :=
  f.toSlashInvariantForm.hasSum_qExpansionAt (Γ.strictWidthAt_pos γ)
    ((ModularFormClass.holo f).slash k (γ : GL (Fin 2) ℝ))
    (ModularFormClass.bdd_at_infty_slash f γ) τ

/-- The q-expansion at any cusp representative determines a modular form of a fixed weight. -/
lemma qExpansionAt_inj (f g : ModularForm Γ k) (γ : SL(2, ℤ)) :
    f.toSlashInvariantForm.qExpansionAt γ = g.toSlashInvariantForm.qExpansionAt γ ↔ f = g := by
  rw [f.toSlashInvariantForm.qExpansionAt_inj g.toSlashInvariantForm (Γ.strictWidthAt_pos γ)
    ((ModularFormClass.holo f).slash k (γ : GL (Fin 2) ℝ))
    (ModularFormClass.bdd_at_infty_slash f γ)
    ((ModularFormClass.holo g).slash k (γ : GL (Fin 2) ℝ))
    (ModularFormClass.bdd_at_infty_slash g γ)]
  constructor
  · intro h
    ext τ
    exact DFunLike.congr_fun h τ
  · rintro rfl
    rfl

/-- Multiplication of modular forms multiplies their q-expansions at a fixed representative. -/
lemma qExpansionAt_mul {k₁ k₂ : ℤ}
    (f : ModularForm Γ k₁) (g : ModularForm Γ k₂) (γ : SL(2, ℤ)) :
    (f.mul g).toSlashInvariantForm.qExpansionAt γ =
      f.toSlashInvariantForm.qExpansionAt γ * g.toSlashInvariantForm.qExpansionAt γ :=
  f.toSlashInvariantForm.qExpansionAt_mul g.toSlashInvariantForm
    (ModularFormClass.analyticAt_cuspFunction_slash_zero f γ)
    (ModularFormClass.analyticAt_cuspFunction_slash_zero g γ)

end ModularForm

namespace CuspForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

/-- The q-expansion of a cusp form has zero constant coefficient at every cusp. -/
@[simp]
lemma qExpansionAt_coeff_zero (f : CuspForm Γ k) (γ : SL(2, ℤ)) :
    (f.toSlashInvariantForm.qExpansionAt γ).coeff 0 = 0 := by
  rw [f.toSlashInvariantForm.qExpansionAt_coeff_zero (Γ.strictWidthAt_pos γ)
    (ModularFormClass.analyticAt_cuspFunction_slash_zero f γ)]
  exact (CuspFormClass.zero_at_infty_slash f γ).valueAtInfty_eq_zero

/-- A cusp form has positive q-expansion order at every cusp, including infinite order for zero. -/
lemma qExpansionAt_order_pos (f : CuspForm Γ k) (γ : SL(2, ℤ)) :
    0 < (f.toSlashInvariantForm.qExpansionAt γ).order :=
  f.toSlashInvariantForm.qExpansionAt_order_pos_iff.mpr (f.qExpansionAt_coeff_zero γ)

end CuspForm
