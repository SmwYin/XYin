/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import XYin.PhD.Tactic2.QExpSimpAttr

/-!
# An experimental `q`-expansion simplifier

The simp set `qexp_simps` collects closure lemmas for the side conditions of mathlib's
`q`-expansion API (periodicity, holomorphy, boundedness at `i∞`, analyticity of the cusp
function at `0`) for pointwise combinations of functions on the upper half-plane and of modular
forms. The tactic `qexp_simp` (or `qexp_simp [h₁, …]` with extra simp lemmas) runs this simp
set, falling back to applying the basic `q`-expansion lemmas.

## Main declarations

* `QExpSimp.analyticAt_cuspFunction_mul`, `_add`, `_sub`, `_neg`, `_smul`: analyticity of the
  cusp function at `0` is closed under pointwise operations.
* `QExpSimp.periodic_comp_ofComplex_mul`, …, `QExpSimp.isBoundedAtImInfty_mul`, …: the same
  closure properties for periodicity and boundedness at `i∞`.
* `qexp_simp`: the tactic.
-/

open Filter Function UpperHalfPlane

open scoped Manifold

namespace QExpSimp

variable {h : ℝ} {f g : ℍ → ℂ}

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
  simpa [Pi.neg_apply, Function.comp_def] using hf.comp (fun z : ℂ ↦ -z)

@[qexp_simps]
lemma periodic_comp_ofComplex_smul (a : ℂ)
    (hf : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    Periodic ((a • f) ∘ UpperHalfPlane.ofComplex) h := by
  simpa [Pi.smul_apply, Function.comp_def] using hf.smul a

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

attribute [qexp_simps] one_pos pow_zero pow_one pow_succ one_mul mul_one
attribute [qexp_simps] one_mem_strictPeriods_SL
attribute [qexp_simps] SlashInvariantFormClass.periodic_comp_ofComplex ModularFormClass.holo
  ModularFormClass.bdd_at_infty CuspFormClass.zero_at_infty
  ModularFormClass.analyticAt_cuspFunction_zero CuspFormClass.cuspFunction_apply_zero
attribute [qexp_simps] MDifferentiable.mul MDifferentiable.add MDifferentiable.sub
  MDifferentiable.neg MDifferentiable.const_smul
attribute [qexp_simps] analyticAt_cuspFunction_zero differentiableAt_cuspFunction
  differentiableOn_cuspFunction_ball
attribute [qexp_simps] qExpansion_zero qExpansion_one qExpansion_mul qExpansion_add qExpansion_sub
  qExpansion_neg qExpansion_smul

/-- The simp call behind `qexp_simp`: `simp only` with the `qexp_simps` set and the given extra
lemmas, with a deep discharger. -/
syntax (name := qexpSimpCore) "qexp_simp_core" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| qexp_simp_core [$args,*]) =>
    `(tactic| simp (maxDischargeDepth := 20) only [qexp_simps, $args,*])

/-- `qexp_simp` (or `qexp_simp [h₁, …]` with extra simp lemmas, typically the hypotheses on the
functions involved) closes side conditions of mathlib's `q`-expansion API: it runs the
`qexp_simps` simp set, and otherwise applies one of the basic `q`-expansion lemmas and
discharges its hypotheses with that simp set. -/
syntax (name := qexpSimp) "qexp_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| qexp_simp) => `(tactic| qexp_simp [])
  | `(tactic| qexp_simp [$args,*]) => `(tactic|
    first
    | qexp_simp_core [$args,*]
    | (apply SlashInvariantFormClass.periodic_comp_ofComplex <;> qexp_simp_core [$args,*])
    | apply ModularFormClass.holo
    | apply ModularFormClass.bdd_at_infty
    | apply CuspFormClass.zero_at_infty
    | (apply CuspFormClass.cuspFunction_apply_zero <;> qexp_simp_core [$args,*])
    | (apply hasSum_qExpansion <;> qexp_simp_core [$args,*])
    | (apply hasSum_qExpansion_of_norm_lt <;> qexp_simp_core [$args,*])
    | (apply qExpansion_coeff_zero <;> qexp_simp_core [$args,*])
    | (apply qExpansion_coeff_eq_circleIntegral <;> qexp_simp_core [$args,*])
    | (apply qExpansion_coeff_eq_intervalIntegral <;> qexp_simp_core [$args,*]))
