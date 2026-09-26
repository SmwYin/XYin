# Inventory: XYin/PhD/Tactic2/qexp_simp.lean  (207 lines)

Experimental "q-expansion simplifier": a custom simp set `qexp_simps` (registered in `QExpSimpAttr.lean`) populated with (a) 29 lemmas in namespace `QExpSimp` — thin aliases of mathlib `ModularFormClass`/`CuspFormClass` facts and ring-operation closure lemmas for `Periodic (f ∘ ofComplex) h`, `MDiff f`, `IsBoundedAtImInfty f`, `AnalyticAt ℂ (cuspFunction h f) 0` — plus (b) 20 mathlib lemmas tagged via `attribute [qexp_simps]`, and two `qexp_simp` tactic macros (with/without extra simp args) that try `simp only [qexp_simps]` (discharge depth 20) and then a fixed list of `apply` fallbacks. Imports only mathlib (`QExpansion`, `LevelOne`) and the attribute file. Used ONLY by `QExpSimpConditionTests.lean`; no library file uses the tactic or the attribute (grep-verified).

## Declarations

All 29 lemmas below are in `namespace QExpSimp`, are `@[qexp_simps]`, public, and have implicit context `{h : ℝ} {f g : ℍ → ℂ} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]` (L17–18).

### `lemma QExpSimp.one_mem_strictPeriods_gamma1`
- **Type**: `(1 : ℝ) ∈ (CongruenceSubgroup.Gamma 1).strictPeriods`
- **What**: 1 is a strict period of Γ(1).
- **How**: `simp` (via mathlib `one_mem_strictPeriods_SL`, `Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean:69`).
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: unused in file (member of the simp set)
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 20–22, body 1 line
- **Notes**: Redundant with L159 `attribute [qexp_simps] one_mem_strictPeriods_SL` (same fact for the same group, `Γ(1)` unfolds to SL by simp).

### `lemma QExpSimp.periodic_comp_ofComplex_of_slashInvariantFormClass`
- **Type**: `[SlashInvariantFormClass F Γ k] (f : F) (hΓ : h ∈ Γ.strictPeriods) : Periodic (f ∘ UpperHalfPlane.ofComplex) h`
- **What**: A slash-invariant form is h-periodic for any strict period h.
- **How**: alias of `SlashInvariantFormClass.periodic_comp_ofComplex` (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:120`).
- **Hypotheses**: h a strict period of Γ
- **Uses from project**: []
- **Used by**: macros `qexp_simp` (L169, L191)
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 24–27, body 1 line
- **Notes**: one-line wrapper around a mathlib lemma.

### `lemma QExpSimp.mdiff_of_modularFormClass`
- **Type**: `[ModularFormClass F Γ k] (f : F) : MDiff f`
- **What**: Modular forms are holomorphic.
- **How**: class field `ModularFormClass.holo`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: macros (L171, L193)
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 29–31, body 1 line
- **Notes**: wrapper; `apply ModularFormClass.holo` works directly.

### `lemma QExpSimp.isBoundedAtImInfty_of_modularFormClass`
- **Type**: `[ModularFormClass F Γ k] [Fact (IsCusp OnePoint.infty Γ)] (f : F) : IsBoundedAtImInfty f`
- **What**: Modular forms are bounded at i∞ when ∞ is a cusp.
- **How**: alias of `ModularFormClass.bdd_at_infty` (`Mathlib/NumberTheory/ModularForms/Basic.lean:734`).
- **Hypotheses**: ∞ is a cusp of Γ (as a `Fact`)
- **Uses from project**: []
- **Used by**: macros (L172, L194)
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 33–36, body 1 line
- **Notes**: wrapper.

### `lemma QExpSimp.isZeroAtImInfty_of_cuspFormClass`
- **Type**: `[CuspFormClass F Γ k] [Fact (IsCusp OnePoint.infty Γ)] (f : F) : IsZeroAtImInfty f`
- **What**: Cusp forms vanish at i∞.
- **How**: alias of `CuspFormClass.zero_at_infty` (`Basic.lean:738`).
- **Hypotheses**: ∞ a cusp
- **Uses from project**: []
- **Used by**: macros (L173, L195)
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 38–41, body 1 line
- **Notes**: wrapper.

### `lemma QExpSimp.analyticAt_cuspFunction_of_modularFormClass`
- **Type**: `[ModularFormClass F Γ k] (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) : AnalyticAt ℂ (cuspFunction h f) 0`
- **What**: The cusp function of a modular form is analytic at q = 0.
- **How**: alias of `ModularFormClass.analyticAt_cuspFunction_zero` (`QExpansion.lean:153`).
- **Hypotheses**: 0 < h, h a strict period
- **Uses from project**: []
- **Used by**: unused in file (simp-set member; conditional rewrite discharged via `hh`/`hΓ` in the set)
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 43–47, body 1 line
- **Notes**: wrapper.

### `lemma QExpSimp.cuspFunction_apply_zero_of_cuspFormClass`
- **Type**: `[CuspFormClass F Γ k] (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) : cuspFunction h f 0 = 0`
- **What**: Cusp function of a cusp form vanishes at 0.
- **How**: alias of `CuspFormClass.cuspFunction_apply_zero` (`QExpansion.lean:345`).
- **Hypotheses**: 0 < h, strict period
- **Uses from project**: []
- **Used by**: macros (L174, L196)
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 49–52, body 1 line
- **Notes**: wrapper.

### `lemma QExpSimp.analyticAt_cuspFunction_mul`
- **Type**: `(hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ (cuspFunction h g) 0) : AnalyticAt ℂ (cuspFunction h (f * g)) 0`
- **What**: Analyticity at the cusp is closed under products.
- **How**: mathlib `cuspFunction_mul hf.continuousAt hg.continuousAt` (`QExpansion.lean:440`) rewrites `cuspFunction h (f*g)` to the product, then `AnalyticAt.mul`.
- **Hypotheses**: both cusp functions analytic at 0
- **Uses from project**: []
- **Used by**: unused in file (simp-set member)
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 54–58, body 1 line
- **Notes**: Genuinely new (no mathlib `analyticAt_cuspFunction_mul`; grep of `QExpansion.lean`). Candidate for upstreaming alongside the four below.

### `lemma QExpSimp.analyticAt_cuspFunction_add`
- **Type**: `(hf) (hg) : AnalyticAt ℂ (cuspFunction h (f + g)) 0`
- **What**: closure under addition.
- **How**: `cuspFunction_add` (`QExpansion.lean:456`) + `AnalyticAt.add`.
- **Hypotheses**: as above
- **Uses from project**: []
- **Used by**: unused in file (simp-set member)
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 60–64, body 1 line
- **Notes**: same skeleton ×5 (mul/add/sub/neg/smul).

### `lemma QExpSimp.analyticAt_cuspFunction_sub`
- **Type**: `(hf) (hg) : AnalyticAt ℂ (cuspFunction h (f - g)) 0`
- **What**: closure under subtraction.
- **How**: `cuspFunction_sub` (`QExpansion.lean:461`) + `AnalyticAt.sub`.
- **Hypotheses**: as above
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 66–70, body 1 line
- **Notes**: Dead inside `qexp_simp`: the set also contains `sub_eq_add_neg` (L158), so simp rewrites `f - g` to `f + -g` in subterms first and the `_add`/`_neg` lemmas fire instead.

### `lemma QExpSimp.analyticAt_cuspFunction_neg`
- **Type**: `(hf) : AnalyticAt ℂ (cuspFunction h (-f)) 0`
- **What**: closure under negation.
- **How**: `cuspFunction_neg` (`QExpansion.lean:452`) + `AnalyticAt.neg`.
- **Hypotheses**: as above
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 72–75, body 1 line
- **Notes**: —

### `lemma QExpSimp.analyticAt_cuspFunction_smul`
- **Type**: `(a : ℂ) (hf) : AnalyticAt ℂ (cuspFunction h (a • f)) 0`
- **What**: closure under scalar multiples.
- **How**: `cuspFunction_smul` (`QExpansion.lean:448`) + `AnalyticAt.const_smul`.
- **Hypotheses**: as above
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 77–81, body 1 line
- **Notes**: —

### `lemma QExpSimp.periodic_comp_ofComplex_mul`
- **Type**: `(hf : Periodic (f ∘ ofComplex) h) (hg : Periodic (g ∘ ofComplex) h) : Periodic ((f * g) ∘ ofComplex) h`
- **What**: Periodicity of the ℂ-extension is closed under products.
- **How**: `Function.Periodic.mul` (`Mathlib/Algebra/Ring/Periodic.lean:59`) after unfolding `Pi.mul_apply`/`comp_def`.
- **Hypotheses**: both periodic
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 83–87, body 1 line
- **Notes**: one-line wrapper; the only content is `(f * g) ∘ φ = (f ∘ φ) * (g ∘ φ)` (mathlib `Pi.mul_comp`/`Function.comp_mul`?—not searched; `simpa` handles it).

### `lemma QExpSimp.periodic_comp_ofComplex_add`
- **Type**: analogous for `f + g`
- **What**: closure under addition.
- **How**: `Function.Periodic.add` (to_additive of `Periodic.mul`, `Algebra/Ring/Periodic.lean:58–60`).
- **Hypotheses**: both periodic
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 89–93, body 1 line
- **Notes**: —

### `lemma QExpSimp.periodic_comp_ofComplex_sub`
- **Type**: analogous for `f - g`
- **What**: closure under subtraction.
- **How**: `Function.Periodic.sub` (to_additive of `Periodic.div`, `Algebra/Ring/Periodic.lean:62–64`).
- **Hypotheses**: both periodic
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 95–99, body 1 line
- **Notes**: dead inside `qexp_simp` (see `sub_eq_add_neg` remark).

### `lemma QExpSimp.periodic_comp_ofComplex_neg`
- **Type**: `(hf) : Periodic ((-f) ∘ ofComplex) h`
- **What**: closure under pointwise negation.
- **How**: `hf.comp (fun z : ℂ => -z)` — mathlib `Function.Periodic.comp` (`Algebra/Ring/Periodic.lean:51`) post-composing with negation (NOT `Periodic.neg`, which negates the period).
- **Hypotheses**: periodic
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 101–104, body 1 line
- **Notes**: —

### `lemma QExpSimp.periodic_comp_ofComplex_smul`
- **Type**: `(a : ℂ) (hf) : Periodic ((a • f) ∘ ofComplex) h`
- **What**: closure under scalars.
- **How**: `Function.Periodic.smul` (`Algebra/Ring/Periodic.lean:86`).
- **Hypotheses**: periodic
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 106–110, body 1 line
- **Notes**: —

### `lemma QExpSimp.mdiff_mul`
- **Type**: `(hf : MDiff f) (hg : MDiff g) : MDiff (f * g)`
- **What**: holomorphy closed under products.
- **How**: `MDifferentiable.mul` (`Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:955`).
- **Hypotheses**: both MDiff
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 112–114, body 1 line
- **Notes**: pure alias; `attribute [qexp_simps] MDifferentiable.mul` would do. (`MDiff` is mathlib's scoped elaborator, `Mathlib/Geometry/Manifold/Notation.lean:858`.)

### `lemma QExpSimp.mdiff_add`
- **Type**: `MDiff (f + g)`; **What/How**: alias of `MDifferentiable.add` (`SpecificFunctions.lean:784`). **Hypotheses**: both MDiff. **Uses from project**: []. **Used by**: unused in file. **Visibility**: public, `@[qexp_simps]`. **Lines**: 116–118, body 1 line. **Notes**: alias.

### `lemma QExpSimp.mdiff_sub`
- **Type**: `MDiff (f - g)`; **What/How**: alias of `MDifferentiable.sub` (`SpecificFunctions.lean:910`). **Hypotheses**: both MDiff. **Uses from project**: []. **Used by**: unused in file. **Visibility**: public, `@[qexp_simps]`. **Lines**: 120–122, body 1 line. **Notes**: alias; dead under `sub_eq_add_neg`.

### `lemma QExpSimp.mdiff_neg`
- **Type**: `MDiff (-f)`; **What/How**: alias of `MDifferentiable.neg` (`SpecificFunctions.lean:878`). **Hypotheses**: MDiff f. **Uses from project**: []. **Used by**: unused in file. **Visibility**: public, `@[qexp_simps]`. **Lines**: 124–126, body 1 line. **Notes**: alias.

### `lemma QExpSimp.mdiff_smul`
- **Type**: `(a : ℂ) (hf : MDiff f) : MDiff (a • f)`; **What/How**: alias of `MDifferentiable.const_smul` (`SpecificFunctions.lean:847`). **Hypotheses**: MDiff f. **Uses from project**: []. **Used by**: unused in file. **Visibility**: public, `@[qexp_simps]`. **Lines**: 128–130, body 1 line. **Notes**: alias.

### `lemma QExpSimp.isBoundedAtImInfty_mul`
- **Type**: `(hf : IsBoundedAtImInfty f) (hg : IsBoundedAtImInfty g) : IsBoundedAtImInfty (f * g)`
- **What**: boundedness at i∞ closed under products.
- **How**: `Filter.BoundedAtFilter.mul` (`Mathlib/Order/Filter/ZeroAndBoundedAtFilter.lean:101`) through the def `IsBoundedAtImInfty := BoundedAtFilter atImInfty` (`Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean:46`).
- **Hypotheses**: both bounded
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 132–135, body 1 line
- **Notes**: alias.

### `lemma QExpSimp.isBoundedAtImInfty_add`
- **Type**: `IsBoundedAtImInfty (f + g)`; **What/How**: alias of `BoundedAtFilter.add` (`ZeroAndBoundedAtFilter.lean:88`). **Hypotheses**: both bounded. **Uses from project**: []. **Used by**: unused in file. **Visibility**: public, `@[qexp_simps]`. **Lines**: 137–140, body 1 line. **Notes**: alias.

### `lemma QExpSimp.isBoundedAtImInfty_sub`
- **Type**: `IsBoundedAtImInfty (f - g)`
- **What**: closure under subtraction.
- **How**: `sub_eq_add_neg` then `BoundedAtFilter.add`/`.neg`.
- **Hypotheses**: both bounded
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public, `@[qexp_simps]`
- **Lines**: 142–145, body 1 line
- **Notes**: Mathlib has NO `BoundedAtFilter.sub` (grep `ZeroAndBoundedAtFilter.lean`: only add:88, neg:92, smul:96, mul:101, mul_zeroAtFilter:112) — the one genuinely missing mathlib lemma in this block; upstream as `Filter.BoundedAtFilter.sub`.

### `lemma QExpSimp.isBoundedAtImInfty_neg`
- **Type**: `IsBoundedAtImInfty (-f)`; **What/How**: alias of `BoundedAtFilter.neg` (:92). **Hypotheses**: bounded. **Uses from project**: []. **Used by**: unused in file. **Visibility**: public, `@[qexp_simps]`. **Lines**: 147–149, body 1 line. **Notes**: alias.

### `lemma QExpSimp.isBoundedAtImInfty_smul`
- **Type**: `(a : ℂ) (hf) : IsBoundedAtImInfty (a • f)`; **What/How**: `Filter.BoundedAtFilter.smul a hf` (:96), written out explicitly. **Hypotheses**: bounded. **Uses from project**: []. **Used by**: unused in file. **Visibility**: public, `@[qexp_simps]`. **Lines**: 151–154, body 1 line. **Notes**: alias.

### `attribute [qexp_simps] one_pos pow_zero pow_one pow_succ one_mul mul_one sub_eq_add_neg` — L158
- **Type**: attribute registration (7 mathlib lemmas added to the `qexp_simps` simp set)
- **What**: Adds generic arithmetic normalisation facts (`0 < 1`, `x^0 = 1`, `x^1 = x`, `x^(n+1) = x^n * x`, unit laws, `a - b = a + -b`) so that side goals like `0 < 1` and numeral powers close inside `qexp_simp`.
- **How**: `attribute [qexp_simps] …` on core/mathlib lemmas (`Mathlib/Algebra/Order/…`, `Mathlib/Algebra/Group/Defs.lean`).
- **Hypotheses**: none
- **Uses from project**: [] (attribute `qexp_simps` from `QExpSimpAttr.lean`)
- **Used by**: both `qexp_simp` macros (every `simp only [qexp_simps]` call)
- **Visibility**: public (global attribute instance)
- **Lines**: 158
- **Notes**: `sub_eq_add_neg` as a simp lemma makes every `_sub` closure lemma in the set unreachable; `pow_succ`/`pow_zero`/`pow_one` are unrelated to q-expansions and are a blunt substitute for missing `_pow` closure lemmas.

### `attribute [qexp_simps] one_mem_strictPeriods_SL` — L159
- **Type**: attribute registration (1 mathlib lemma)
- **What**: `(1:ℝ) ∈ strictPeriods` for the level-one group, so `hΓ` side goals for `Γ(1)` close.
- **How**: tags mathlib `one_mem_strictPeriods_SL` (`Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean:69`).
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: both macros (side goals of the `apply … <;> simp only [qexp_simps]` branches, e.g. `QExpSimpConditionTests.lean:40–41, 52–53`)
- **Visibility**: public
- **Lines**: 159
- **Notes**: Duplicates `QExpSimp.one_mem_strictPeriods_gamma1` (L21), which proves the same fact by `simp` from this lemma.

### `attribute [qexp_simps] analyticAt_cuspFunction_zero differentiableAt_cuspFunction differentiableOn_cuspFunction_ball` — L160–161
- **Type**: attribute registration (3 mathlib lemmas)
- **What**: The conditional facts "cusp function analytic at 0 / differentiable at |q| < 1 / differentiable on the unit ball" for any h-periodic, holomorphic, bounded-at-i∞ `f`.
- **How**: tags mathlib `UpperHalfPlane.analyticAt_cuspFunction_zero` (`QExpansion.lean:101`), `differentiableAt_cuspFunction` (:83), `differentiableOn_cuspFunction_ball` (:95); each has 4 hypotheses `hh hfper hfhol hfbdd` that simp must discharge from the set plus user-supplied args, hence `maxDischargeDepth := 20`.
- **Hypotheses**: (of the tagged lemmas) `0 < h`, `Periodic (f ∘ ofComplex) h`, `MDiff f`, `IsBoundedAtImInfty f`
- **Uses from project**: []
- **Used by**: both macros; exercised by `QExpSimpConditionTests.lean:11–25`
- **Visibility**: public
- **Lines**: 160–161
- **Notes**: These are the engine of the tactic — the closure lemmas exist to reduce `f*g+…` goals to instances of these.

### `attribute [qexp_simps] qExpansion_zero qExpansion_one qExpansion_mul qExpansion_add qExpansion_sub qExpansion_neg qExpansion_smul` — L162–163
- **Type**: attribute registration (7 mathlib lemmas)
- **What**: Ring-homomorphism rules for `qExpansion h` (of 0, 1, products, sums, differences, negatives, scalar multiples) so that `qexp_simp` can normalise `qExpansion h (f*g+…)` to a polynomial in `qExpansion h f`, `qExpansion h g`.
- **How**: tags mathlib `UpperHalfPlane.qExpansion_zero` (`QExpansion.lean:500`), `qExpansion_one` (:515), `qExpansion_mul` (:466, hypotheses: both cusp functions analytic at 0), `qExpansion_add` (:487), `qExpansion_sub` (:494), `qExpansion_neg` (:483), `qExpansion_smul` (:477). Because only `UpperHalfPlane` is opened, these are the analytic-hypothesis versions, not the protected `ModularForm.qExpansion_*` (:556–594) ones.
- **Hypotheses**: (of `qExpansion_mul`) `AnalyticAt ℂ (cuspFunction h f) 0`, `AnalyticAt ℂ (cuspFunction h g) 0`, discharged via the `analyticAt_cuspFunction_*` members
- **Uses from project**: []
- **Used by**: both macros; NOT exercised by any test (no `qExpansion_*` rewriting goal in `QExpSimpConditionTests.lean`)
- **Visibility**: public
- **Lines**: 162–163
- **Notes**: `qExpansion_sub` is dead under `sub_eq_add_neg` (L158). `link.lean:398–404` does by hand (`qExpansion_of_pow`, `qExpansion_mul` with explicit analyticity proofs) exactly what this set is meant to automate.

### `macro "qexp_simp" : tactic` — L165–185
- **What**: `first | simp only [qexp_simps] (discharge depth 20) | apply <each of 5 QExpSimp aliases> <;> simp only [qexp_simps] | apply hasSum_qExpansion / hasSum_qExpansion_of_norm_lt / qExpansion_coeff_zero / qExpansion_coeff_eq_circleIntegral / qExpansion_coeff_eq_intervalIntegral <;> simp only [qexp_simps]`.
- **How**: 11-branch `first`; the fallbacks are mathlib `hasSum_qExpansion` (`QExpansion.lean:189`), `hasSum_qExpansion_of_norm_lt` (:179), `qExpansion_coeff_zero` (:173), `qExpansion_coeff_eq_circleIntegral` (:279), `qExpansion_coeff_eq_intervalIntegral` (:294).
- **Uses from project**: `QExpSimp.periodic_comp_ofComplex_of_slashInvariantFormClass`, `mdiff_of_modularFormClass`, `isBoundedAtImInfty_of_modularFormClass`, `isZeroAtImInfty_of_cuspFormClass`, `cuspFunction_apply_zero_of_cuspFormClass`, attribute `qexp_simps`
- **Used by**: `QExpSimpConditionTests.lean` only (5 bare uses L41–53)
- **Visibility**: global tactic syntax
- **Lines**: 165–185 (21 lines)
- **Notes**: `simp (config := { maxDischargeDepth := 20 })` is the deprecated config syntax (`simp +maxDischargeDepth` … not available for that field; the modern form is `simp (maxDischargeDepth := 20)`). Repeated 6× per macro.

### `macro "qexp_simp" "[" args,* "]" : tactic` — L187–207
- **What**: identical to the above with `[$args,*, qexp_simps]` in every `simp only`.
- **Uses from project**: same
- **Used by**: `QExpSimpConditionTests.lean` L17, L25, L34
- **Lines**: 187–207 (21 lines)
- **Notes**: 21-line verbatim duplicate of the first macro; a single `macro "qexp_simp" args:(" [" simpLemma,* "]")? : tactic` (or `syntax … (simpArgs)?`) collapses both.

## File Summary
- Total declarations: 35 (0 defs, 29 lemmas, 0 instances, 6 other: 4 `attribute` registrations + 2 macros)
- Key API (used by 3+ others in the file): none (the 5 `_of_*Class` aliases are each used by both macros; every other lemma is only a simp-set member)
- Unused declarations (not used by anything in this file): the 24 closure/alias lemmas other than the 5 `apply`-targets are referenced only through the attribute; nothing outside `Tactic2/` uses any `QExpSimp.*` name, the attribute, or the macros (grep-verified)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (all ≤ 1 line)

## Observations (evidence for the analysis phases)
### Mathlib API candidates (the full `qexp_simps` membership list, all in THIS file)
- Project-defined members (29, all `XYin/PhD/Tactic2/qexp_simp.lean`): `QExpSimp.one_mem_strictPeriods_gamma1` (L21), `periodic_comp_ofComplex_of_slashInvariantFormClass` (L25), `mdiff_of_modularFormClass` (L30), `isBoundedAtImInfty_of_modularFormClass` (L34), `isZeroAtImInfty_of_cuspFormClass` (L39), `analyticAt_cuspFunction_of_modularFormClass` (L44), `cuspFunction_apply_zero_of_cuspFormClass` (L50), `analyticAt_cuspFunction_{mul,add,sub,neg,smul}` (L55–81), `periodic_comp_ofComplex_{mul,add,sub,neg,smul}` (L84–110), `mdiff_{mul,add,sub,neg,smul}` (L113–130), `isBoundedAtImInfty_{mul,add,sub,neg,smul}` (L133–154).
- Mathlib members tagged by `attribute` (20, L158–163): `one_pos pow_zero pow_one pow_succ one_mul mul_one sub_eq_add_neg`, `one_mem_strictPeriods_SL`, `analyticAt_cuspFunction_zero differentiableAt_cuspFunction differentiableOn_cuspFunction_ball`, `qExpansion_zero qExpansion_one qExpansion_mul qExpansion_add qExpansion_sub qExpansion_neg qExpansion_smul`.
- No other file registers anything with `qexp_simps` (grep over `XYin/`).
- 22 of the 29 project lemmas are one-line aliases of mathlib lemmas (verified paths above: `QExpansion.lean:120/153/345`, `Basic.lean:734/738`, `Algebra/Ring/Periodic.lean:51/59/62/86`, `MFDeriv/SpecificFunctions.lean:784/847/878/910/955`, `ZeroAndBoundedAtFilter.lean:88/92/96/101`) that exist only to carry the attribute; `attribute [qexp_simps] <mathlib name>` (as already done at L158–163) makes them unnecessary. The 7 with real content: `analyticAt_cuspFunction_{mul,add,sub,neg,smul}` (compose `cuspFunction_*` with `AnalyticAt.*`), `isBoundedAtImInfty_sub` (mathlib lacks `BoundedAtFilter.sub`), and `periodic_comp_ofComplex_*` only insofar as they push `∘ ofComplex` through `Pi` ops.

### Missing API / repeated patterns
- Five-fold `{mul,add,sub,neg,smul}` closure blocks ×4 predicates (L54–154): the `_sub` members are dead because `sub_eq_add_neg` is in the set. Either drop `sub_eq_add_neg` or drop the `_sub` lemmas.
- Missing: a `pow` closure (`analyticAt_cuspFunction_pow`, `periodic_comp_ofComplex_pow`, `mdiff_pow`, `isBoundedAtImInfty_pow`) — `pow_succ` is in the set as a workaround, which unrolls `f ^ n` for numerals only.
- Missing: `qexp_simp` does not know the project's `IsIntegralPowerSeries`/`laurentqExpansion` layer; `LaurentQExpSimpTests.lean` (misnamed) does not use the tactic at all.
- The two macros duplicate 21 lines; one macro with optional simp-args suffices.

### Junk candidates
- Whole file is unused by the library (only `QExpSimpConditionTests.lean` calls `qexp_simp`); `XYin.lean:32` imports it into the root, so it is compiled and its global tactic syntax `qexp_simp` and 29 lemmas are visible to every downstream file for no benefit.
- `QExpSimp.one_mem_strictPeriods_gamma1` (L21) duplicates the tagged `one_mem_strictPeriods_SL` (L159).
- Module docstring L5–9 says "sandboxed under `XYin/Tactic2`" but the file is in `XYin/PhD/Tactic2` and imported by the root; no copyright header.
- Deprecated `simp (config := {...})` spelling ×12.

### Moral duplicates within this batch
- `periodic_comp_ofComplex_of_slashInvariantFormClass` (L25) ≡ mathlib `SlashInvariantFormClass.periodic_comp_ofComplex`; `analyticAt_cuspFunction_of_modularFormClass` (L44) ≡ `ModularFormClass.analyticAt_cuspFunction_zero`; `cuspFunction_apply_zero_of_cuspFormClass` (L50) ≡ `CuspFormClass.cuspFunction_apply_zero`; `mdiff_*` ≡ `MDifferentiable.*`; `isBoundedAtImInfty_{mul,add,neg,smul}` ≡ `BoundedAtFilter.*` — see paths above.
- Cross-batch: `link.lean:398–401` proves `qExpansion 1 (E4^3) = (qExpansion 1 E4)^3` by hand from `qExpansion_of_pow`; the `qexp_simps` set (with `pow_succ` + `qExpansion_mul`) is designed for exactly such goals but is not used there.

### Generalization notes
- `mdiff_*`, `isBoundedAtImInfty_*`, `periodic_comp_ofComplex_*` are stated for `ℍ → ℂ` but the underlying mathlib lemmas are generic (`MDifferentiable` over any model, `BoundedAtFilter` over any `SeminormedRing`, `Periodic` over any `[Add α] [Mul β]`); the specialisation is deliberate for the simp set and harmless.
- `analyticAt_cuspFunction_*` are inherently ℂ-specific (`cuspFunction`).
