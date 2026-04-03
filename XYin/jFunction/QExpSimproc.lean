import XYin.jFunction.jfunction
import XYin.jFunction.QExpSimprocAttr
import Mathlib.Tactic.Simproc.Divisors

open Complex Filter ModularForm ModularFormClass UpperHalfPlane MatrixGroups PowerSeries
  SlashInvariantFormClass Real Function IntegralPowerSeries ArithmeticFunction

local notation "ℍₒ" => upperHalfPlaneSet

/-!
# Tactics for q-expansion computation

This file provides two domain-agnostic tactics:
- `simp_q_exp`: distributes `qExpansion` over algebraic operations and proves analyticity
- `ps_coeff`: computes power series coefficients

Both tactics take user-provided lemmas as arguments and contain no domain-specific code.
-/

/-! ## Part 1: Construction of `ps_coeff` -/

section
open PowerSeries Finset ArithmeticFunction

-- Structural: expand coeff of products/sums/one
attribute [_powerSeries_coeff_internal] coeff_mul coeff_one map_sub map_add

-- Power decomposition
attribute [_powerSeries_coeff_internal] pow_succ pow_zero pow_one one_mul mul_one

-- Antidiagonal sum expansion
attribute [_powerSeries_coeff_internal] Finset.Nat.sum_antidiagonal_succ

-- Base case for antidiagonal 0
@[_powerSeries_coeff_internal] lemma sum_antidiagonal_zero' {R : Type*} [AddCommMonoid R]
    (f : ℕ × ℕ → R) : ∑ p ∈ Finset.antidiagonal 0, f p = f (0, 0) := by simp

-- Nat arithmetic
attribute [_powerSeries_coeff_internal] Nat.reduceAdd Nat.reduceMul Nat.reducePow

-- Sigma function: unfold to sum over divisors
attribute [_powerSeries_coeff_internal] sigma_apply

-- Divisor set computation (dsimproc from Mathlib)
attribute [_powerSeries_coeff_internal] Nat.divisors_ofNat

-- Finset sum evaluation over concrete sets
attribute [_powerSeries_coeff_internal] Finset.sum_cons Finset.sum_empty Finset.sum_singleton

-- Conditional evaluation
attribute [_powerSeries_coeff_internal] ite_true ite_false

-- Cast simplification
attribute [_powerSeries_coeff_internal] Nat.cast_ofNat Nat.cast_zero Nat.cast_one
attribute [_powerSeries_coeff_internal] Int.cast_ofNat Int.cast_zero Int.cast_one

-- Integer arithmetic
attribute [_powerSeries_coeff_internal] Int.reduceAdd Int.reduceMul Int.reduceNeg
  Int.reduceSub Int.reducePow

-- Finset membership (needed for sum_cons discharge)
attribute [_powerSeries_coeff_internal] Finset.mem_cons Finset.mem_singleton

-- Scalar multiplication
attribute [_powerSeries_coeff_internal] smul_eq_mul map_smul

-- Ring simplification (no mul_comm to avoid looping!)
attribute [_powerSeries_coeff_internal] mul_zero zero_mul add_zero zero_add mul_one one_mul

-- Power series scalar mult
attribute [_powerSeries_coeff_internal] PowerSeries.coeff_smul smul_eq_mul

-- Additional coeff lemmas
attribute [_powerSeries_coeff_internal] map_neg neg_mul

end

-- dsimproc: evaluate `if` with decidable concrete conditions
open Lean Meta in
dsimproc_decl evalIte (ite _ _ _) := fun e => do
  guard (e.isAppOfArity ``ite 5)
  let inst := e.getArg! 2
  let instR ← withTransparency .all <| whnf inst
  if instR.isAppOf ``Decidable.isTrue then return .done (e.getArg! 3)
  if instR.isAppOf ``Decidable.isFalse then return .done (e.getArg! 4)
  return .continue
attribute [_powerSeries_coeff_internal] evalIte

-- `ps_coeff [lem₁, lem₂, ...]` computes power series coefficients.
-- User-provided lemmas are applied via MVarId.rewrite (with full transparency
-- to handle definitional equalities), then simp [_powerSeries_coeff_internal]
-- expands products and evaluates, then norm_num finishes.
-- ps_coeff without arguments: unfolds all defs then computes
-- Uses `Lean.Meta.deltaExpand` to unfold all user definitions before simp.
open Lean Elab Tactic in
elab "ps_coeff" : tactic => do
  -- Unfold user-defined power series constants in the goal.
  -- Only unfold defs whose type is `PowerSeries _`.
  let g ← getMainGoal
  let target ← g.getType
  let env ← getEnv
  let expanded ← Meta.deltaExpand target (fun n => Id.run do
    let some ci := env.find? n | return false
    let ty := ci.type
    return ty.isAppOf ``PowerSeries || ty.isAppOf ``MvPowerSeries)
  if expanded != target then
    let g' ← g.replaceTargetDefEq expanded
    replaceMainGoal [g']
  try evalTactic (← `(tactic| simp only [_powerSeries_coeff_internal]))
  catch _ => pure ()
  try evalTactic (← `(tactic| norm_num))
  catch _ => pure ()

-- ps_coeff [args]: with user-provided lemmas
open Lean Elab Tactic in
elab "ps_coeff" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
withTheReader Core.Context (fun ctx =>
    { ctx with maxHeartbeats := ctx.maxHeartbeats * 4 }) do
  -- Build proof terms from user args (both direct and congr_fun versions)
  let mut proofs : Array Expr := #[]
  for arg in args.getElems do
    let t : TSyntax `term := ⟨arg.raw.getArgs.back!⟩
    if let some e ← try some <$> Term.elabTerm t none catch _ => pure none then
      proofs := proofs.push e
      if let some cf ← try some <$> Meta.mkAppM ``congr_fun #[e] catch _ => pure none then
        proofs := proofs.push cf
  -- Save state before Steps 1-5 (for inverse relation fallback)
  let stateBeforeSteps ← saveState
  -- Step 1: rewrite with user args (handles isDefEq matching)
  let goal ← getMainGoal
  let mut g := goal
  for proof in proofs do
    for useSymm in [false, true] do
      try
        let result ← g.rewrite (← g.getType) proof useSymm
          (config := { transparency := .all })
        g ← g.replaceTargetEq result.eNew result.eqProof
      catch _ => continue
  replaceMainGoal [g]
  -- Step 2: simp with user args + _powerSeries_coeff_internal
  try evalTactic (← `(tactic| simp only [$args,*, _powerSeries_coeff_internal]))
  catch _ => pure ()
  -- Step 3: substitute coefficient values in expanded terms (congr_fun + isDefEq)
  let g2 ← getMainGoal
  let g3 ← withTheReader Core.Context (fun ctx =>
      { ctx with maxHeartbeats := ctx.maxHeartbeats * 4 }) do
    let mut g := g2
    for n in List.range 7 do
      for proof in proofs do
        try
          let cfn ← Meta.mkAppM ``congr_fun #[proof, Lean.mkNatLit n]
          let result ← g.rewrite (← g.getType) cfn false
            (config := { transparency := .default })
          g ← g.replaceTargetEq result.eNew result.eqProof
        catch _ => continue
    return g
  replaceMainGoal [g3]
  -- Step 4: simp again to evaluate sigma/conditionals after substitution
  try evalTactic (← `(tactic| simp only [$args,*, _powerSeries_coeff_internal]))
  catch _ => pure ()
  -- Step 5: norm_num for final ℂ arithmetic
  try evalTactic (← `(tactic| norm_num))
  catch _ => pure ()
  -- Check if Steps 1-5 solved the goal
  if (← getUnsolvedGoals).isEmpty then return
  -- Step 6: inverse relation fallback
  -- Restore to original goal (Steps 1-5 may have mangled it via aggressive rewriting)
  -- For each arg × coefficient index, try: congrArg (coeff n) arg, simplify, linear_combination
  let stateAfterSteps ← saveState
  restoreState stateBeforeSteps
  let mut invSolved := false
  for arg in args.getElems do
    if invSolved then break
    let t : TSyntax `term := ⟨arg.raw.getArgs.back!⟩
    -- Quick check: is this arg a power series equation?
    let isEq ← try
      let e ← Term.elabTerm t none
      let ty ← Meta.inferType e
      pure (ty.isAppOf ``Eq)
    catch _ => pure false
    if !isEq then continue
    for n in List.range 11 do
      if invSolved then break
      let saved ← saveState
      try
        let nStx := Lean.Syntax.mkNumLit (toString n)
        -- Step 6a: extract coefficient from power series equation
        evalTactic (← `(tactic| open PowerSeries in
          have _h_inv := congrArg (coeff $nStx) $t))
        -- Step 6b: expand product structure (coeff_mul, antidiagonal, etc.)
        -- Must run BEFORE user args to prevent equation from collapsing _h_inv
        evalTactic (← `(tactic|
          simp only [_powerSeries_coeff_internal] at _h_inv))
        -- Step 6c: substitute known coefficient values
        evalTactic (← `(tactic|
          simp only [$args,*, _powerSeries_coeff_internal] at _h_inv))
        -- Step 6d: solve linear equation
        evalTactic (← `(tactic| linear_combination _h_inv))
        invSolved := true
      catch _ =>
        restoreState saved
  if !invSolved then restoreState stateAfterSteps

/-! ## Part 2: Construction of `simp_q_exp` -/

section q_exp_lemmas

variable {h : ℝ} {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

-- General distribution lemmas (for arbitrary ℍ → ℂ functions with AnalyticAt conditions)
attribute [_q_exp_internal] qExpansion_mul

@[_q_exp_internal] lemma qExpansion_add_analytic {f g : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    qExpansion h (f + g) = qExpansion h f + qExpansion h g := by
  ext n; simp only [qExpansion_coeff, cuspFunction_add hf.continuousAt hg.continuousAt,
    iteratedDeriv_add hf.contDiffAt hg.contDiffAt, mul_add, map_add]

@[_q_exp_internal] lemma qExpansion_sub_analytic {f g : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    qExpansion h (f - g) = qExpansion h f - qExpansion h g := by
  ext n; simp only [qExpansion_coeff, cuspFunction_sub hf.continuousAt hg.continuousAt,
    iteratedDeriv_sub hf.contDiffAt hg.contDiffAt, mul_sub, map_sub]

@[_q_exp_internal] lemma qExpansion_smul_analytic (a : ℂ) {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    qExpansion h (a • f) = a • qExpansion h f := by
  ext n; simp only [qExpansion_coeff, cuspFunction_smul hf.continuousAt,
    iteratedDeriv_const_smul_field, smul_eq_mul, PowerSeries.coeff_smul]; ring

@[_q_exp_internal] lemma qExpansion_neg_analytic {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    qExpansion h (-f) = -qExpansion h f := by
  have h1 : (-f : ℍ → ℂ) = (-1 : ℂ) • f := by ext; simp
  rw [h1, qExpansion_smul_analytic (-1) hf]; simp

-- ModularForm distribution lemmas (conditions auto-discharged via typeclasses)
attribute [_q_exp_internal] ModularForm.qExpansion_mul
attribute [_q_exp_internal] _root_.qExpansion_add _root_.qExpansion_smul _root_.qExpansion_neg
attribute [_q_exp_internal] _root_.qExpansion_sub

-- Power distribution (via graded ring)
attribute [_q_exp_internal] qExpansion_of_pow

-- Zero
attribute [_q_exp_internal] qExpansion_zero

-- Side condition helpers
@[_q_exp_internal] lemma one_pos_real : (0 : ℝ) < 1 := by norm_num
attribute [_q_exp_internal] one_mem_strictPeriods_SL2Z

-- AnalyticAt: base cases
@[_q_exp_internal] lemma analyticAt_cuspFunction_of_modularForm
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F)
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    AnalyticAt ℂ (cuspFunction h f) 0 :=
  analyticAt_cuspFunction_zero f hh hΓ

@[_q_exp_internal] lemma analyticAt_cuspFunction_Gamma1
    (f : ModularForm (CongruenceSubgroup.Gamma 1) k) :
    AnalyticAt ℂ (cuspFunction 1 (↑f : ℍ → ℂ)) 0 :=
  analyticAt_cuspFunction_zero f (by norm_num) one_mem_strictPeriods_SL2Z

@[_q_exp_internal] lemma analyticAt_cuspFunction_Gamma1_cusp
    (f : CuspForm (CongruenceSubgroup.Gamma 1) k) :
    AnalyticAt ℂ (cuspFunction 1 (↑f : ℍ → ℂ)) 0 :=
  analyticAt_cuspFunction_zero f (by norm_num) one_mem_strictPeriods_SL2Z

@[_q_exp_internal] lemma analyticAt_of_differentiableOn_ball {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) :
    AnalyticAt ℂ f 0 :=
  hf.analyticAt (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1))

-- AnalyticAt: compound
@[_q_exp_internal] lemma analyticAt_cuspFunction_mul {f g : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    AnalyticAt ℂ (cuspFunction h (f * g)) 0 := by
  rw [cuspFunction_mul hf.continuousAt hg.continuousAt]; exact hf.mul hg

@[_q_exp_internal] lemma analyticAt_cuspFunction_add {f g : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    AnalyticAt ℂ (cuspFunction h (f + g)) 0 := by
  rw [cuspFunction_add hf.continuousAt hg.continuousAt]; exact hf.add hg

@[_q_exp_internal] lemma analyticAt_cuspFunction_sub {f g : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    AnalyticAt ℂ (cuspFunction h (f - g)) 0 := by
  rw [cuspFunction_sub hf.continuousAt hg.continuousAt]; exact hf.sub hg

@[_q_exp_internal] lemma analyticAt_cuspFunction_smul (a : ℂ) {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    AnalyticAt ℂ (cuspFunction h (a • f)) 0 := by
  rw [cuspFunction_smul hf.continuousAt]; exact hf.const_smul

@[_q_exp_internal] lemma analyticAt_cuspFunction_neg {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    AnalyticAt ℂ (cuspFunction h (-f)) 0 := by
  rw [cuspFunction_neg hf.continuousAt]; exact hf.neg

-- Inverse
attribute [_q_exp_internal] AnalyticAt.inv one_ne_zero ne_of_gt

-- Powers: decompose to products
attribute [_q_exp_internal] pow_succ pow_zero one_mul mul_one

-- Periodic: base + compound
@[_q_exp_internal] lemma periodic_modularForm_Gamma1
    {F : Type*} [FunLike F ℍ ℂ] [SlashInvariantFormClass F
      (CongruenceSubgroup.Gamma 1) k] (f : F) :
    Periodic (f ∘ UpperHalfPlane.ofComplex) 1 :=
  periodic_comp_ofComplex f one_mem_strictPeriods_SL2Z

@[_q_exp_internal] lemma Periodic.comp_mul {f g : ℍ → ℂ}
    (hf : Periodic (f ∘ UpperHalfPlane.ofComplex) 1)
    (hg : Periodic (g ∘ UpperHalfPlane.ofComplex) 1) :
    Periodic ((f * g) ∘ UpperHalfPlane.ofComplex) 1 := by
  intro w; simp only [comp_def, Pi.mul_apply]
  rw [show f (UpperHalfPlane.ofComplex (w + 1)) = f (UpperHalfPlane.ofComplex w) from hf w,
      show g (UpperHalfPlane.ofComplex (w + 1)) = g (UpperHalfPlane.ofComplex w) from hg w]

@[_q_exp_internal] lemma Periodic.comp_sub {f g : ℍ → ℂ}
    (hf : Periodic (f ∘ UpperHalfPlane.ofComplex) 1)
    (hg : Periodic (g ∘ UpperHalfPlane.ofComplex) 1) :
    Periodic ((f - g) ∘ UpperHalfPlane.ofComplex) 1 := by
  intro w; simp only [comp_def, Pi.sub_apply]
  rw [show f (UpperHalfPlane.ofComplex (w + 1)) = f (UpperHalfPlane.ofComplex w) from hf w,
      show g (UpperHalfPlane.ofComplex (w + 1)) = g (UpperHalfPlane.ofComplex w) from hg w]

@[_q_exp_internal] lemma Periodic.comp_add {f g : ℍ → ℂ}
    (hf : Periodic (f ∘ UpperHalfPlane.ofComplex) 1)
    (hg : Periodic (g ∘ UpperHalfPlane.ofComplex) 1) :
    Periodic ((f + g) ∘ UpperHalfPlane.ofComplex) 1 := by
  intro w; simp only [comp_def, Pi.add_apply]
  rw [show f (UpperHalfPlane.ofComplex (w + 1)) = f (UpperHalfPlane.ofComplex w) from hf w,
      show g (UpperHalfPlane.ofComplex (w + 1)) = g (UpperHalfPlane.ofComplex w) from hg w]

-- Holomorphic: base + compound
@[_q_exp_internal] lemma holomorphic_modularForm_Gamma1
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F
      (CongruenceSubgroup.Gamma 1) k] (f : F) :
    ∀ z : ℍₒ, DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z :=
  fun ⟨_, hz⟩ => differentiableAt_comp_ofComplex (f := f) hz

@[_q_exp_internal] lemma holomorphic_mul {f g : ℍ → ℂ}
    (hf : ∀ z : ℍₒ, DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z)
    (hg : ∀ z : ℍₒ, DifferentiableAt ℂ (g ∘ UpperHalfPlane.ofComplex) z) :
    ∀ z : ℍₒ, DifferentiableAt ℂ ((f * g) ∘ UpperHalfPlane.ofComplex) z :=
  fun z => (hf z).mul (hg z)

@[_q_exp_internal] lemma holomorphic_sub {f g : ℍ → ℂ}
    (hf : ∀ z : ℍₒ, DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z)
    (hg : ∀ z : ℍₒ, DifferentiableAt ℂ (g ∘ UpperHalfPlane.ofComplex) z) :
    ∀ z : ℍₒ, DifferentiableAt ℂ ((f - g) ∘ UpperHalfPlane.ofComplex) z :=
  fun z => (hf z).sub (hg z)

-- Bounded: base + compound
@[_q_exp_internal] lemma bounded_modularForm_Gamma1
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F (CongruenceSubgroup.Gamma 1) k] (f : F) :
    IsBoundedAtImInfty f := by simp [ModularFormClass.bdd_at_infty]

@[_q_exp_internal] lemma IsBoundedAtImInfty.mul' {f g : ℍ → ℂ}
    (hf : IsBoundedAtImInfty f) (hg : IsBoundedAtImInfty g) :
    IsBoundedAtImInfty (f * g) := hf.mul hg

-- DifferentiableOn → AnalyticAt (the final step)
axiom differentiableOn_cuspFunction_ball {h : ℝ} {f : ℍ → ℂ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : ∀ z : ℍₒ, DifferentiableAt ℂ (f ∘ ofComplex) z)
    (hfbdd : IsBoundedAtImInfty f) : DifferentiableOn ℂ (cuspFunction h f) (Metric.ball 0 1)

@[_q_exp_internal] lemma analyticAt_of_periodic_holomorphic_bounded {f : ℍ → ℂ}
    (hper : Periodic (f ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : ∀ z : ℍₒ, DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) z)
    (hbdd : IsBoundedAtImInfty f) :
    AnalyticAt ℂ (cuspFunction 1 f) 0 :=
  (differentiableOn_cuspFunction_ball (by norm_num) hper hhol hbdd).analyticAt
    (Metric.ball_mem_nhds 0 (by norm_num))

end q_exp_lemmas

-- simp_q_exp: without arguments
macro "simp_q_exp" : tactic =>
  `(tactic| simp (config := { maxDischargeDepth := 4 }) only [_q_exp_internal])

-- simp_q_exp [args]: with extra lemmas
open Lean Elab Tactic in
elab "simp_q_exp" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  -- Try 1: plain simp_q_exp
  try evalTactic (← `(tactic| simp (config := { maxDischargeDepth := 4 }) only [_q_exp_internal]))
      return
  catch _ => pure ()
  -- Try 2: simp with user args + _q_exp_internal
  try
    let saved ← saveState
    evalTactic (← `(tactic|
      simp (config := { maxDischargeDepth := 4 }) only [$args,*, _q_exp_internal]))
    if (← getUnsolvedGoals).isEmpty then return
    restoreState saved
  catch _ => pure ()
  -- Try 3: rewrite user args in ← direction then simp
  try
    for arg in args.getElems do
      let t : TSyntax `term := ⟨arg.raw.getArgs.back!⟩
      try evalTactic (← `(tactic| conv_lhs => rw [show _ = _ from ($t).symm]))
      catch _ => try evalTactic (← `(tactic| conv_rhs => rw [show _ = _ from ($t).symm]))
                 catch _ => pure ()
    evalTactic (← `(tactic|
      simp (config := { maxDischargeDepth := 4 }) only [$args,*, _q_exp_internal]))
    return
  catch _ => pure ()
  -- Try 4: periodic + holomorphic + bounded → AnalyticAt
  try
    for arg in args.getElems do
      let t : TSyntax `term := ⟨arg.raw.getArgs.back!⟩
      try evalTactic (← `(tactic| have := $t))
      catch _ => pure ()
    evalTactic (← `(tactic|
      exact analyticAt_of_periodic_holomorphic_bounded ‹_› ‹_› ‹_›))
    return
  catch _ => pure ()
  -- Try 5: last resort
  evalTactic (← `(tactic|
    simp (config := { maxDischargeDepth := 4 }) [$args,*, _q_exp_internal]))

/-! ## Part 3: Axioms and domain-specific lemmas -/

noncomputable section

-- Deltaoverq properties
private lemma Deltaoverq_periodic : Periodic (Deltaoverq ∘ UpperHalfPlane.ofComplex) 1 := by
  rw [← InfSumDeltashift_eq_Deltaoverq]
  intro w
  by_cases hw : 0 < Complex.im w
  · have hw1 : 0 < Complex.im (w + 1) := by simpa using hw
    simp only [comp_def, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw1, InfSumDeltashift]
    congr 1; ext n; congr 1; congr 1
    rw [show 2 * ↑π * Complex.I * (↑(⟨w + 1, hw1⟩ : ℍ) : ℂ) =
        2 * ↑π * Complex.I * (↑(⟨w, hw⟩ : ℍ) : ℂ) + 2 * ↑π * Complex.I from by
      simp; ring]
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  · have hw0 : Complex.im w ≤ 0 := le_of_not_gt hw
    have hw1 : Complex.im (w + 1) ≤ 0 := by simpa using hw0
    simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos hw0,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hw1]

private lemma Deltaoverq_holomorphic :
    ∀ z : ℍₒ, DifferentiableAt ℂ (Deltaoverq ∘ UpperHalfPlane.ofComplex) z := by
  intro ⟨z, hz⟩
  have hDelta := ModularFormClass.differentiableAt_comp_ofComplex (f := Delta) hz
  have hExp : DifferentiableAt ℂ (fun w => (Complex.exp (2 * π * Complex.I * w))⁻¹) z :=
    (Complex.differentiableAt_exp.comp z
      ((differentiableAt_const _).mul differentiableAt_id)).inv (Complex.exp_ne_zero _)
  have hEq : ∀ w, 0 < Complex.im w →
      (Deltaoverq ∘ UpperHalfPlane.ofComplex) w =
      (fun w => (Complex.exp (2 * π * Complex.I * w))⁻¹) w *
      (Delta ∘ UpperHalfPlane.ofComplex) w := by
    intro w hw
    simp only [comp_def, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    simp [DeltaoverqIdentity, Pi.mul_apply, one_div]
  exact (hExp.mul hDelta).congr_of_eventuallyEq
    (Filter.eventuallyEq_iff_exists_mem.mpr ⟨{w | 0 < Complex.im w},
      IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im) hz,
      fun w hw => (hEq w hw).symm⟩).symm

private lemma Deltaoverq_bounded : IsBoundedAtImInfty Deltaoverq := by
  have h0 : ZeroAtFilter atImInfty (fun τ => Deltaoverq τ - 1) := by
    simpa [ZeroAtFilter, sub_eq_add_neg] using
      Deltaoverq_tendsto_atImInfty.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℍ => (1 : ℂ)) _ _)
  have h1 : IsBoundedAtImInfty (fun τ => Deltaoverq τ - 1 + 1) :=
    h0.boundedAtFilter.add (const_boundedAtFilter atImInfty (1 : ℂ))
  rwa [show (fun τ => Deltaoverq τ - 1 + 1) = Deltaoverq from by ext; ring] at h1

private lemma Deltaoverq_AnalyticAt' : AnalyticAt ℂ (cuspFunction 1 Deltaoverq) 0 := by
  simp_q_exp [Deltaoverq_periodic, Deltaoverq_holomorphic, Deltaoverq_bounded]

-- qoverDelta properties (derived from Deltaoverq)
private lemma qoverDelta_periodic :
    Periodic (qoverDelta ∘ UpperHalfPlane.ofComplex) 1 := by
  intro w; simp only [comp_def, qoverDelta]; congr 1; exact Deltaoverq_periodic w

private lemma qoverDelta_bounded : IsBoundedAtImInfty qoverDelta := by
  have h0 : ZeroAtFilter atImInfty (fun τ => qoverDelta τ - 1) := by
    simpa [ZeroAtFilter, sub_eq_add_neg] using
      qoverDelta_tendsto_atImInfty.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℍ => (1 : ℂ)) _ _)
  have h1 : IsBoundedAtImInfty (fun τ => qoverDelta τ - 1 + 1) :=
    h0.boundedAtFilter.add (const_boundedAtFilter atImInfty (1 : ℂ))
  rwa [show (fun τ => qoverDelta τ - 1 + 1) = qoverDelta from by ext; ring] at h1

private lemma qoverDelta_AnalyticAt' : AnalyticAt ℂ (cuspFunction 1 qoverDelta) 0 := by
  rw [cuspFunction_qoverDelta_EqInv]
  change AnalyticAt ℂ (cuspFunction 1 Deltaoverq)⁻¹ 0
  exact Deltaoverq_AnalyticAt'.inv (by simp [cuspFunction_Deltaoverq_zero])

-- qj properties (from qjIdentity: qj = E4^3 * qoverDelta)
private lemma qj_periodic' : Periodic (qj ∘ UpperHalfPlane.ofComplex) 1 := by
  intro w; simp only [comp_def, ← qjIdentity, Pi.mul_apply, Pi.pow_apply]
  have hE4 : (E4 : ℍ → ℂ) (UpperHalfPlane.ofComplex (w + 1)) =
      (E4 : ℍ → ℂ) (UpperHalfPlane.ofComplex w) :=
    periodic_comp_ofComplex E4 one_mem_strictPeriods_SL2Z w
  have hqod : qoverDelta (UpperHalfPlane.ofComplex (w + 1)) =
      qoverDelta (UpperHalfPlane.ofComplex w) := qoverDelta_periodic w
  rw [hE4, hqod]

private lemma qj_holomorphic' :
    ∀ z : ℍₒ, DifferentiableAt ℂ (qj ∘ UpperHalfPlane.ofComplex) z := by
  intro ⟨z, hz⟩
  rw [show qj = (↑E4 ^ 3 : ℍ → ℂ) * qoverDelta from qjIdentity.symm]
  have hE4 := differentiableAt_comp_ofComplex (f := E4) hz
  have hE4cb : DifferentiableAt ℂ ((↑E4 ^ 3 : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) z := by
    change DifferentiableAt ℂ (fun w => ((E4 ∘ UpperHalfPlane.ofComplex) w) ^ 3) z
    exact hE4.pow 3
  have hDq := Deltaoverq_holomorphic ⟨z, hz⟩
  have hqod : DifferentiableAt ℂ (qoverDelta ∘ UpperHalfPlane.ofComplex) z := by
    change DifferentiableAt ℂ (fun w => 1 / ((Deltaoverq ∘ UpperHalfPlane.ofComplex) w)) z
    exact (differentiableAt_const 1).div hDq (by
      simp only [comp_apply, ne_eq]
      exact Deltaoverq_ne_zero _)
  exact hE4cb.mul hqod

private lemma qj_bounded' : IsBoundedAtImInfty qj := by
  rw [show qj = (↑E4 ^ 3 : ℍ → ℂ) * qoverDelta from qjIdentity.symm]
  exact E4cubed_IsBoundedAtImInfty.mul qoverDelta_bounded

end

/-! ## Part 4: Examples demonstrating `simp_q_exp` -/

section simp_q_exp_examples

-- Distributing qExpansion (general: user provides AnalyticAt conditions)
variable {h : ℝ} {f₁ g₁ : ℍ → ℂ}

example (hf : AnalyticAt ℂ (cuspFunction h f₁) 0) (hg : AnalyticAt ℂ (cuspFunction h g₁) 0) :
    qExpansion h (f₁ * g₁) = qExpansion h f₁ * qExpansion h g₁ := by
  simp_q_exp [hf, hg]
example (hf : AnalyticAt ℂ (cuspFunction h f₁) 0) (hg : AnalyticAt ℂ (cuspFunction h g₁) 0) :
    qExpansion h (f₁ + g₁) = qExpansion h f₁ + qExpansion h g₁ := by
  simp_q_exp [hf, hg]
example (hf : AnalyticAt ℂ (cuspFunction h f₁) 0) (hg : AnalyticAt ℂ (cuspFunction h g₁) 0) :
    qExpansion h (f₁ - g₁) = qExpansion h f₁ - qExpansion h g₁ := by
  simp_q_exp [hf, hg]
example (a : ℂ) (hf : AnalyticAt ℂ (cuspFunction h f₁) 0) :
    qExpansion h (a • f₁) = a • qExpansion h f₁ := by
  simp_q_exp [hf]
example (hf : AnalyticAt ℂ (cuspFunction h f₁) 0) :
    qExpansion h (-f₁) = -qExpansion h f₁ := by
  simp_q_exp [hf]

-- Distributing qExpansion (Γ(1): fully automatic)
noncomputable example :
    qExpansion 1 (↑E4 * ↑E6) =
    qExpansion 1 (↑E4 : ℍ → ℂ) * qExpansion 1 (↑E6 : ℍ → ℂ) := by simp_q_exp
noncomputable example :
    qExpansion 1 (↑E4 * ↑E4) =
    qExpansion 1 (↑E4 : ℍ → ℂ) * qExpansion 1 (↑E4 : ℍ → ℂ) := by simp_q_exp
noncomputable example :
    qExpansion 1 (↑E4 - ↑E6 : ℍ → ℂ) =
    qExpansion 1 (↑E4 : ℍ → ℂ) - qExpansion 1 (↑E6 : ℍ → ℂ) := by simp_q_exp
noncomputable example :
    qExpansion 1 (↑E4 * ↑E4 - ↑E6 : ℍ → ℂ) =
    qExpansion 1 (↑E4 : ℍ → ℂ) * qExpansion 1 (↑E4 : ℍ → ℂ) -
      qExpansion 1 (↑E6 : ℍ → ℂ) := by simp_q_exp

-- Proving AnalyticAt (Γ(1) modular forms: automatic)
example : AnalyticAt ℂ (cuspFunction 1 E4) 0 := by simp_q_exp
example : AnalyticAt ℂ (cuspFunction 1 E6) 0 := by simp_q_exp
example : AnalyticAt ℂ (cuspFunction 1 Delta) 0 := by simp_q_exp
example : AnalyticAt ℂ (cuspFunction 1 (↑E4 * ↑E4 : ℍ → ℂ)) 0 := by simp_q_exp
example : AnalyticAt ℂ (cuspFunction 1 (E6 ^ 2)) 0 := by simp_q_exp
example : AnalyticAt ℂ (cuspFunction 1 (E4 ^ 3)) 0 := by simp_q_exp
example : AnalyticAt ℂ (cuspFunction 1 (E4 ^ 3 - E6 ^ 2)) 0 := by simp_q_exp

-- Proving AnalyticAt (non-modular-form: via periodic + holomorphic + bounded)
example : AnalyticAt ℂ (cuspFunction 1 qj) 0 := by
  simp_q_exp [qj_periodic', qj_holomorphic', qj_bounded']

-- Proving AnalyticAt (via identity rewrite)
example : AnalyticAt ℂ (cuspFunction 1 qj) 0 := by
  simp_q_exp [qjIdentity, Deltaoverq_AnalyticAt', qoverDelta_AnalyticAt']

-- Delta coefficient identity
private lemma Deltaaux' : qExpansion 1 Delta = (1/1728 : ℂ) • qExpansion 1 (E4 ^ 3 - E6 ^ 2) := by
  rw [Delta_E4_eqn, show (↑Delta_E4_E6_aux : ℍ → ℂ) =
      ↑(ModForm_mk (CongruenceSubgroup.Gamma 1) 12 Delta_E4_E6_aux) from by
    ext; simp [Delta_E4_E6_aux, ModForm_mk]; rfl]
  rw [Delta_E4_E6_eq]
  -- LHS: qExpansion 1 ⇑((1/1728) • (graded_expr 12))
  -- RHS: (1/1728) • qExpansion 1 (E4^3 - E6^2)
  -- Step 1: distribute qExpansion through smul via qExpansion_smul2
  rw [show (↑((1/1728 : ℂ) • ((DirectSum.of _ 4 E₄ ^ 3 -
      DirectSum.of _ 6 E₆ ^ 2) 12)) : ℍ → ℂ) =
      (1/1728 : ℂ) • (↑E4 ^ 3 - ↑E6 ^ 2) from by
    ext z; simp only [DirectSum.sub_apply, pow_three, pow_two,
      DirectSum.of_mul_of, Int.reduceAdd, DirectSum.of_eq_same, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, E4, E6, Nat.cast_ofNat]; rfl]
  simp_q_exp

private lemma Delta_ps_eq : qExpansion 1 Delta =
    (1/1728 : ℂ) • ((qExpansion 1 (↑E4 : ℍ → ℂ)) ^ 3 - (qExpansion 1 (↑E6 : ℍ → ℂ)) ^ 2) := by
  rw [Deltaaux']
  simp_q_exp

end simp_q_exp_examples

/-! ## Part 5: Examples demonstrating `ps_coeff` -/

section ps_coeff_examples
open PowerSeries

-- Pure power series (no q-expansions)
def f : PowerSeries ℤ := mk fun n => (n : ℤ) + 1        -- [1, 2, 3, 4, ...]
def g : PowerSeries ℤ := mk fun n => if n = 0 then 1 else 0  -- [1, 0, 0, 0, ...]

-- Individual coefficients — no arguments needed!
example : f.coeff 0 = 1 := by ps_coeff
example : f.coeff 3 = 4 := by ps_coeff
example : g.coeff 0 = 1 := by ps_coeff
example : g.coeff 2 = 0 := by ps_coeff

-- Products, sums, differences, powers — all automatic
example : (f * g).coeff 3 = 4 := by ps_coeff
example : (f + g).coeff 0 = 2 := by ps_coeff
example : (f - g).coeff 0 = 0 := by ps_coeff
example : (f - g).coeff 2 = 3 := by ps_coeff
example : (f ^ 2).coeff 2 = 10 := by ps_coeff
example : (f ^ 3).coeff 2 = 21 := by ps_coeff

-- Complicated combinations with random-coefficient power series
def p : PowerSeries ℤ := mk fun n => [3, -1, 2, 5, -3].getD n 0  -- 3 - x + 2x² + 5x³ - 3x⁴
def q : PowerSeries ℤ := mk fun n => [1, 4, -2, 0, 7].getD n 0   -- 1 + 4x - 2x² + 7x⁴
def r : PowerSeries ℤ := mk fun n => [2, 0, 1, -1, 3].getD n 0   -- 2 + x² - x³ + 3x⁴

example : (p * q).coeff 3 = 15 := by ps_coeff
example : (p * q + r ^ 2).coeff 3 = 11 := by ps_coeff
example : (p ^ 2 - q * r).coeff 2 = 16 := by ps_coeff
example : (p * q * r).coeff 2 = -13 := by ps_coeff
example : (p ^ 3).coeff 1 = -27 := by ps_coeff
example : (p ^ 2 * q - r ^ 3 + p * r).coeff 2 = -34 := by ps_coeff

-- E4/E6 coefficients
noncomputable example : (qExpansion 1 (↑E4 : ℍ → ℂ)).coeff 5 = 30240 := by
  ps_coeff [E4_q_exp, sigma_apply]
noncomputable example : (qExpansion 1 (↑E4 : ℍ → ℂ)).coeff 1 = 240 := by
  ps_coeff [E4_q_exp]
noncomputable example : (qExpansion 1 (↑E6 : ℍ → ℂ)).coeff 3 = -122976 := by
  ps_coeff [E6_q_exp, sigma_apply]

-- Delta coefficients (via identity)
private lemma Delta1 : (qExpansion 1 Delta).coeff 1 = 1 := by
  ps_coeff [Delta_ps_eq, E4_q_exp, E6_q_exp, sigma_apply]

private lemma Delta2 : (qExpansion 1 Delta).coeff 2 = -24 := by
  ps_coeff [Delta_ps_eq, E4_q_exp, E6_q_exp, sigma_apply]

private lemma Delta3 : (qExpansion 1 Delta).coeff 3 = 252 := by
  ps_coeff [Delta_ps_eq, E4_q_exp, E6_q_exp, sigma_apply]

private lemma Delta4 : (qExpansion 1 Delta).coeff 4 = -1472 := by
ps_coeff [Delta_ps_eq, E4_q_exp, E6_q_exp, sigma_apply]

private lemma Delta5 : (qExpansion 1 Delta).coeff 5 = 4830 := by
  ps_coeff [Delta_ps_eq, E4_q_exp, E6_q_exp, sigma_apply]

private lemma doverq_coeff (n : ℕ) :
    ((qExpansion 1 Deltaoverq).coeff n : ℂ) = (qExpansion 1 Delta).coeff (n + 1) := by
  have h1 : ((qExpansion 1 Deltaoverq).coeff n : ℂ) = (qExpansion 1 Deltaoverq).coeff n := by
    have := congrArg (coeff n) (coeTo_of_toIntegralPowerSeries DeltaoverqIsIntegralPowerSeries)
    simp
  rw [h1, ← InfSumDeltashift_eq_Deltaoverq]
  exact InfSumDeltashift_coeff_eq n

private lemma doq_0 : (qExpansion 1 Deltaoverq).coeff 0 = 1 := by
  simp [doverq_coeff, Delta1]

private lemma doq_1 : (qExpansion 1 Deltaoverq).coeff 1 = -24 := by
  simp [doverq_coeff, Delta2]

private lemma doq_2 : (qExpansion 1 Deltaoverq).coeff 2 = 252 := by
  simp [doverq_coeff, Delta3]

private lemma doq_3 : (qExpansion 1 Deltaoverq).coeff 3 = -1472 := by
  simp [doverq_coeff, Delta4]

private lemma doq_4 : (qExpansion 1 Deltaoverq).coeff 4 = 4830 := by
  simp [doverq_coeff, Delta5]

-- qoverDelta coefficients from inverse relation:
-- integralDeltaoverq * qExpansion 1 qoverDelta = 1
-- Bridge: connects coeToComplexPowerSeries.ringHom form to qExpansion form
private lemma coe_doq (n : ℕ) :
    (coeToComplexPowerSeries.ringHom integralDeltaoverq).coeff n =
    (qExpansion 1 Deltaoverq).coeff n :=
  congrArg (coeff n)
    (coeTo_of_toIntegralPowerSeries DeltaoverqIsIntegralPowerSeries)

private lemma qod_0 : (qExpansion 1 qoverDelta).coeff 0 = 1 := by
  ps_coeff [integralDeltaoverq_mul_qoverDelta_qExpansion,
    coe_doq, doq_0]

private lemma qod_1 : (qExpansion 1 qoverDelta).coeff 1 = 24 := by
  ps_coeff [integralDeltaoverq_mul_qoverDelta_qExpansion,
    coe_doq, doq_0, doq_1, qod_0]

private lemma qod_2 : (qExpansion 1 qoverDelta).coeff 2 = 324 := by
  ps_coeff [integralDeltaoverq_mul_qoverDelta_qExpansion,
    coe_doq, doq_0, doq_1, doq_2, qod_0, qod_1]

private lemma qod_3 : (qExpansion 1 qoverDelta).coeff 3 = 3200 := by
  ps_coeff [integralDeltaoverq_mul_qoverDelta_qExpansion,
    coe_doq, doq_0, doq_1, doq_2, doq_3, qod_0, qod_1, qod_2]

private lemma qod_4 : (qExpansion 1 qoverDelta).coeff 4 = 25650 := by
  ps_coeff [integralDeltaoverq_mul_qoverDelta_qExpansion,
    coe_doq, doq_0, doq_1, doq_2, doq_3, doq_4,
    qod_0, qod_1, qod_2, qod_3]

noncomputable example : (qExpansion 1 qj).coeff 0 = 1 := by
  simp_q_exp [qjIdentity, qoverDelta_AnalyticAt']
  ps_coeff [qod_0, qod_1, qod_2, qod_3, qod_4, E4_q_exp, sigma_apply]
noncomputable example : (qExpansion 1 qj).coeff 1 = 744 := by
  simp_q_exp [qjIdentity, qoverDelta_AnalyticAt']
  ps_coeff [qod_0, qod_1, qod_2, qod_3, qod_4, E4_q_exp, sigma_apply]
noncomputable example : (qExpansion 1 qj).coeff 2 = 196884 := by
  simp_q_exp [qjIdentity, qoverDelta_AnalyticAt']
  ps_coeff [qod_0, qod_1, qod_2, qod_3, qod_4, E4_q_exp, sigma_apply]
noncomputable example : (qExpansion 1 qj).coeff 3 = 21493760 := by
  simp_q_exp [qjIdentity, qoverDelta_AnalyticAt']
  ps_coeff [qod_0, qod_1, qod_2, qod_3, qod_4, E4_q_exp, sigma_apply]
noncomputable example : (qExpansion 1 qj).coeff 4 = 864299970 := by
  simp_q_exp [qjIdentity, qoverDelta_AnalyticAt']
  ps_coeff [qod_0, qod_1, qod_2, qod_3, qod_4, E4_q_exp, sigma_apply]

end ps_coeff_examples
