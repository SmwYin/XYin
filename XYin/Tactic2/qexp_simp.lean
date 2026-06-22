import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne
import XYin.Tactic2.QExpSimpAttr

/-!
Experimental q-expansion simplifier.

Everything in this file is deliberately sandboxed under `XYin/Tactic2`.
-/

open Filter Function UpperHalfPlane

open scoped CongruenceSubgroup Manifold

namespace QExpSimp

variable {h : ℝ} {f g : ℍ → ℂ}
variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

@[qexp_simps]
lemma one_mem_strictPeriods_gamma1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma 1).strictPeriods := by
  simp

@[qexp_simps]
lemma periodic_comp_ofComplex_of_slashInvariantFormClass [SlashInvariantFormClass F Γ k]
    (f : F) (hΓ : h ∈ Γ.strictPeriods) : Periodic (f ∘ UpperHalfPlane.ofComplex) h :=
  SlashInvariantFormClass.periodic_comp_ofComplex f hΓ

@[qexp_simps]
lemma mdiff_of_modularFormClass [ModularFormClass F Γ k] (f : F) : MDiff f :=
  ModularFormClass.holo f

@[qexp_simps]
lemma isBoundedAtImInfty_of_modularFormClass [ModularFormClass F Γ k]
    [Fact (IsCusp OnePoint.infty Γ)] (f : F) : IsBoundedAtImInfty f :=
  ModularFormClass.bdd_at_infty f

@[qexp_simps]
lemma isZeroAtImInfty_of_cuspFormClass [CuspFormClass F Γ k]
    [Fact (IsCusp OnePoint.infty Γ)] (f : F) : IsZeroAtImInfty f :=
  CuspFormClass.zero_at_infty f

@[qexp_simps]
lemma analyticAt_cuspFunction_of_modularFormClass [ModularFormClass F Γ k] (f : F)
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    AnalyticAt ℂ (cuspFunction h f) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ

@[qexp_simps]
lemma cuspFunction_apply_zero_of_cuspFormClass [CuspFormClass F Γ k] (f : F)
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) : cuspFunction h f 0 = 0 :=
  CuspFormClass.cuspFunction_apply_zero f hh hΓ

@[qexp_simps]
lemma analyticAt_cuspFunction_mul (hf : AnalyticAt ℂ (cuspFunction h f) 0)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    AnalyticAt ℂ (cuspFunction h (f * g)) 0 := by
  simpa [cuspFunction_mul hf.continuousAt hg.continuousAt] using hf.mul hg

@[qexp_simps]
lemma analyticAt_cuspFunction_add (hf : AnalyticAt ℂ (cuspFunction h f) 0)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    AnalyticAt ℂ (cuspFunction h (f + g)) 0 := by
  simpa [cuspFunction_add hf.continuousAt hg.continuousAt] using hf.add hg

@[qexp_simps]
lemma analyticAt_cuspFunction_sub (hf : AnalyticAt ℂ (cuspFunction h f) 0)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    AnalyticAt ℂ (cuspFunction h (f - g)) 0 := by
  simpa [cuspFunction_sub hf.continuousAt hg.continuousAt] using hf.sub hg

@[qexp_simps]
lemma analyticAt_cuspFunction_neg (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    AnalyticAt ℂ (cuspFunction h (-f)) 0 := by
  simpa [cuspFunction_neg hf.continuousAt] using hf.neg

@[qexp_simps]
lemma analyticAt_cuspFunction_smul (a : ℂ)
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    AnalyticAt ℂ (cuspFunction h (a • f)) 0 := by
  simpa [cuspFunction_smul hf.continuousAt a] using hf.const_smul

@[qexp_simps]
lemma periodic_comp_ofComplex_mul (hf : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hg : Periodic (g ∘ UpperHalfPlane.ofComplex) h) :
    Periodic ((f * g) ∘ UpperHalfPlane.ofComplex) h := by
  simpa [Pi.mul_apply, Function.comp_def] using hf.mul hg

@[qexp_simps]
lemma periodic_comp_ofComplex_add (hf : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hg : Periodic (g ∘ UpperHalfPlane.ofComplex) h) :
    Periodic ((f + g) ∘ UpperHalfPlane.ofComplex) h := by
  simpa [Pi.add_apply, Function.comp_def] using hf.add hg

@[qexp_simps]
lemma periodic_comp_ofComplex_sub (hf : Periodic (f ∘ UpperHalfPlane.ofComplex) h)
    (hg : Periodic (g ∘ UpperHalfPlane.ofComplex) h) :
    Periodic ((f - g) ∘ UpperHalfPlane.ofComplex) h := by
  simpa [Pi.sub_apply, Function.comp_def] using hf.sub hg

@[qexp_simps]
lemma periodic_comp_ofComplex_neg (hf : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    Periodic ((-f) ∘ UpperHalfPlane.ofComplex) h := by
  simpa [Pi.neg_apply, Function.comp_def] using hf.comp (fun z : ℂ => -z)

@[qexp_simps]
lemma periodic_comp_ofComplex_smul (a : ℂ)
    (hf : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    Periodic ((a • f) ∘ UpperHalfPlane.ofComplex) h := by
  simpa [Pi.smul_apply, Function.comp_def] using hf.smul a

@[qexp_simps]
lemma mdiff_mul (hf : MDiff f) (hg : MDiff g) : MDiff (f * g) :=
  hf.mul hg

@[qexp_simps]
lemma mdiff_add (hf : MDiff f) (hg : MDiff g) : MDiff (f + g) :=
  hf.add hg

@[qexp_simps]
lemma mdiff_sub (hf : MDiff f) (hg : MDiff g) : MDiff (f - g) :=
  hf.sub hg

@[qexp_simps]
lemma mdiff_neg (hf : MDiff f) : MDiff (-f) :=
  hf.neg

@[qexp_simps]
lemma mdiff_smul (a : ℂ) (hf : MDiff f) : MDiff (a • f) :=
  hf.const_smul a

@[qexp_simps]
lemma isBoundedAtImInfty_mul (hf : IsBoundedAtImInfty f) (hg : IsBoundedAtImInfty g) :
    IsBoundedAtImInfty (f * g) :=
  hf.mul hg

@[qexp_simps]
lemma isBoundedAtImInfty_add (hf : IsBoundedAtImInfty f) (hg : IsBoundedAtImInfty g) :
    IsBoundedAtImInfty (f + g) :=
  hf.add hg

@[qexp_simps]
lemma isBoundedAtImInfty_sub (hf : IsBoundedAtImInfty f) (hg : IsBoundedAtImInfty g) :
    IsBoundedAtImInfty (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

@[qexp_simps]
lemma isBoundedAtImInfty_neg (hf : IsBoundedAtImInfty f) : IsBoundedAtImInfty (-f) :=
  hf.neg

@[qexp_simps]
lemma isBoundedAtImInfty_smul (a : ℂ) (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (a • f) :=
  Filter.BoundedAtFilter.smul a hf

end QExpSimp

attribute [qexp_simps] one_pos pow_zero pow_one pow_succ one_mul mul_one sub_eq_add_neg
attribute [qexp_simps] one_mem_strictPeriods_SL
attribute [qexp_simps] analyticAt_cuspFunction_zero differentiableAt_cuspFunction
  differentiableOn_cuspFunction_ball
attribute [qexp_simps] qExpansion_zero qExpansion_one qExpansion_mul qExpansion_add qExpansion_sub
  qExpansion_neg qExpansion_smul

macro "qexp_simp" : tactic =>
  `(tactic|
    first
    | simp (config := { maxDischargeDepth := 20 }) only [qexp_simps]
    | (apply QExpSimp.periodic_comp_ofComplex_of_slashInvariantFormClass <;>
        simp (config := { maxDischargeDepth := 20 }) only [qexp_simps])
    | apply QExpSimp.mdiff_of_modularFormClass
    | apply QExpSimp.isBoundedAtImInfty_of_modularFormClass
    | apply QExpSimp.isZeroAtImInfty_of_cuspFormClass
    | (apply QExpSimp.cuspFunction_apply_zero_of_cuspFormClass <;>
        simp (config := { maxDischargeDepth := 20 }) only [qexp_simps])
    | (apply hasSum_qExpansion <;>
        simp (config := { maxDischargeDepth := 20 }) only [qexp_simps])
    | (apply hasSum_qExpansion_of_norm_lt <;>
        simp (config := { maxDischargeDepth := 20 }) only [qexp_simps])
    | (apply qExpansion_coeff_zero <;>
        simp (config := { maxDischargeDepth := 20 }) only [qexp_simps])
    | (apply qExpansion_coeff_eq_circleIntegral <;>
        simp (config := { maxDischargeDepth := 20 }) only [qexp_simps])
    | (apply qExpansion_coeff_eq_intervalIntegral <;>
        simp (config := { maxDischargeDepth := 20 }) only [qexp_simps]))

macro "qexp_simp" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    first
    | simp (config := { maxDischargeDepth := 20 }) only [$args,*, qexp_simps]
    | (apply QExpSimp.periodic_comp_ofComplex_of_slashInvariantFormClass <;>
        simp (config := { maxDischargeDepth := 20 }) only [$args,*, qexp_simps])
    | apply QExpSimp.mdiff_of_modularFormClass
    | apply QExpSimp.isBoundedAtImInfty_of_modularFormClass
    | apply QExpSimp.isZeroAtImInfty_of_cuspFormClass
    | (apply QExpSimp.cuspFunction_apply_zero_of_cuspFormClass <;>
        simp (config := { maxDischargeDepth := 20 }) only [$args,*, qexp_simps])
    | (apply hasSum_qExpansion <;>
        simp (config := { maxDischargeDepth := 20 }) only [$args,*, qexp_simps])
    | (apply hasSum_qExpansion_of_norm_lt <;>
        simp (config := { maxDischargeDepth := 20 }) only [$args,*, qexp_simps])
    | (apply qExpansion_coeff_zero <;>
        simp (config := { maxDischargeDepth := 20 }) only [$args,*, qexp_simps])
    | (apply qExpansion_coeff_eq_circleIntegral <;>
        simp (config := { maxDischargeDepth := 20 }) only [$args,*, qexp_simps])
    | (apply qExpansion_coeff_eq_intervalIntegral <;>
        simp (config := { maxDischargeDepth := 20 }) only [$args,*, qexp_simps]))
