# XYin/PhD/Tactic2/qexp_simp.lean
Project-internal imports: XYin.PhD.Tactic2.QExpSimpAttr

All lemmas live in namespace `QExpSimp` with shared variables `{h : ℝ} {f g : ℍ → ℂ} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]`. Every lemma carries `@[qexp_simps]` (the attribute registered in `QExpSimpAttr.lean`), so all of them feed the `qexp_simp` tactic's simp set; below, "Used by: qexp_simp macros (via simp set)" records that implicit use, while explicit `apply` uses in the macros are noted separately.

### `lemma QExpSimp.one_mem_strictPeriods_gamma1`
- **Type**: `(1 : ℝ) ∈ (CongruenceSubgroup.Gamma 1).strictPeriods`
- **What**: The real number 1 is a strict period of the full modular group Γ(1), i.e. τ ↦ τ+1 lies in Γ(1) — the basic fact that level-one modular forms are 1-periodic.
- **How**: Discharged by `simp`, which reduces membership in `strictPeriods` of Γ(1) using mathlib's simp lemmas for congruence-subgroup periods (Γ(1) contains the translation matrix T).
- **Hypotheses**: none
- **Uses from project**: [`qexp_simps` attribute (QExpSimpAttr.lean)]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 20–22, 1-line proof
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.periodic_comp_ofComplex_of_slashInvariantFormClass`
- **Type**: `[SlashInvariantFormClass F Γ k] (f : F) (hΓ : h ∈ Γ.strictPeriods) : Periodic (f ∘ UpperHalfPlane.ofComplex) h`
- **What**: A slash-invariant form of weight k for Γ, viewed as a function on ℂ via the section `ofComplex`, is periodic with any strict period h of Γ.
- **How**: Direct application of mathlib's `SlashInvariantFormClass.periodic_comp_ofComplex`: slash-invariance under the translation-by-h matrix (which lies in Γ since h is a strict period) gives f(τ+h) = f(τ).
- **Hypotheses**: F is a slash-invariant-form class for Γ of weight k; h is a strict period of Γ.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (explicit `apply` branch and via simp set)
- **Visibility**: public
- **Lines**: 24–27, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.mdiff_of_modularFormClass`
- **Type**: `[ModularFormClass F Γ k] (f : F) : MDiff f`
- **What**: Any modular form (for arbitrary Γ ≤ GL₂(ℝ), weight k) is holomorphic on ℍ in the manifold-differentiability sense (`MDiff`).
- **How**: Direct application of mathlib's `ModularFormClass.holo`, the holomorphy field of the modular-form class.
- **Hypotheses**: F is a modular-form class for Γ of weight k.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (explicit `apply` branch and via simp set)
- **Visibility**: public
- **Lines**: 29–31, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.isBoundedAtImInfty_of_modularFormClass`
- **Type**: `[ModularFormClass F Γ k] [Fact (IsCusp OnePoint.infty Γ)] (f : F) : IsBoundedAtImInfty f`
- **What**: A modular form for a group Γ having ∞ as a cusp is bounded as Im τ → ∞.
- **How**: Direct application of mathlib's `ModularFormClass.bdd_at_infty`, the boundedness-at-cusps field of the class, specialized to the cusp ∞.
- **Hypotheses**: F is a modular-form class; ∞ is a cusp of Γ (as a `Fact` instance).
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (explicit `apply` branch and via simp set)
- **Visibility**: public
- **Lines**: 33–36, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.isZeroAtImInfty_of_cuspFormClass`
- **Type**: `[CuspFormClass F Γ k] [Fact (IsCusp OnePoint.infty Γ)] (f : F) : IsZeroAtImInfty f`
- **What**: A cusp form for a group Γ having ∞ as a cusp tends to 0 as Im τ → ∞.
- **How**: Direct application of mathlib's `CuspFormClass.zero_at_infty`, the vanishing-at-cusps field of the cusp-form class.
- **Hypotheses**: F is a cusp-form class; ∞ is a cusp of Γ.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (explicit `apply` branch and via simp set)
- **Visibility**: public
- **Lines**: 38–41, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.analyticAt_cuspFunction_of_modularFormClass`
- **Type**: `[ModularFormClass F Γ k] (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) : AnalyticAt ℂ (cuspFunction h f) 0`
- **What**: The cusp function (q-disc transform) of a modular form is analytic at q = 0; this is the analytic content of the existence of a holomorphic q-expansion.
- **How**: Direct application of mathlib's `ModularFormClass.analyticAt_cuspFunction_zero`: holomorphy plus boundedness at ∞ gives a removable singularity at q = 0 by Riemann's removable-singularity theorem (packaged in mathlib).
- **Hypotheses**: F is a modular-form class; h > 0 is a strict period of Γ.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 43–47, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.cuspFunction_apply_zero_of_cuspFormClass`
- **Type**: `[CuspFormClass F Γ k] (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) : cuspFunction h f 0 = 0`
- **What**: The cusp function of a cusp form vanishes at q = 0, i.e. cusp forms have zero constant term in their q-expansion.
- **How**: Direct application of mathlib's `CuspFormClass.cuspFunction_apply_zero`: the value at q = 0 is the limit of f as Im τ → ∞, which is 0 by the cusp-form vanishing condition.
- **Hypotheses**: F is a cusp-form class; h > 0 is a strict period of Γ.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (explicit `apply` branch and via simp set)
- **Visibility**: public
- **Lines**: 49–52, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.analyticAt_cuspFunction_mul`
- **Type**: `(hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ (cuspFunction h g) 0) : AnalyticAt ℂ (cuspFunction h (f * g)) 0`
- **What**: Analyticity at q = 0 of cusp functions is closed under pointwise multiplication of the underlying functions on ℍ.
- **How**: Mathlib's `cuspFunction_mul` (valid where both cusp functions are continuous, in particular at 0 by `AnalyticAt.continuousAt`) rewrites cuspFunction h (f·g) to the product of cusp functions, and `AnalyticAt.mul` closes the goal.
- **Hypotheses**: cuspFunction h f and cuspFunction h g are analytic at 0.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 54–58, 1-line proof
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.analyticAt_cuspFunction_add`
- **Type**: `(hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ (cuspFunction h g) 0) : AnalyticAt ℂ (cuspFunction h (f + g)) 0`
- **What**: Analyticity at q = 0 of cusp functions is closed under pointwise addition.
- **How**: Mathlib's `cuspFunction_add` (with continuity at 0 from analyticity) identifies cuspFunction h (f+g) with the sum of cusp functions; `AnalyticAt.add` finishes.
- **Hypotheses**: both cusp functions analytic at 0.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 60–64, 1-line proof
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.analyticAt_cuspFunction_sub`
- **Type**: `(hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ (cuspFunction h g) 0) : AnalyticAt ℂ (cuspFunction h (f - g)) 0`
- **What**: Analyticity at q = 0 of cusp functions is closed under pointwise subtraction.
- **How**: Mathlib's `cuspFunction_sub` plus `AnalyticAt.sub`, with continuity at 0 supplied by `AnalyticAt.continuousAt`.
- **Hypotheses**: both cusp functions analytic at 0.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 66–70, 1-line proof
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.analyticAt_cuspFunction_neg`
- **Type**: `(hf : AnalyticAt ℂ (cuspFunction h f) 0) : AnalyticAt ℂ (cuspFunction h (-f)) 0`
- **What**: Analyticity at q = 0 of the cusp function is preserved under pointwise negation.
- **How**: Mathlib's `cuspFunction_neg` rewrites cuspFunction h (−f) as −(cuspFunction h f); `AnalyticAt.neg` finishes.
- **Hypotheses**: cuspFunction h f analytic at 0.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 72–75, 1-line proof
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.analyticAt_cuspFunction_smul`
- **Type**: `(a : ℂ) (hf : AnalyticAt ℂ (cuspFunction h f) 0) : AnalyticAt ℂ (cuspFunction h (a • f)) 0`
- **What**: Analyticity at q = 0 of the cusp function is preserved under scalar multiplication by a complex constant.
- **How**: Mathlib's `cuspFunction_smul` rewrites cuspFunction h (a•f) as a • cuspFunction h f; `AnalyticAt.const_smul` finishes.
- **Hypotheses**: cuspFunction h f analytic at 0.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 77–81, 1-line proof
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.periodic_comp_ofComplex_mul`
- **Type**: `(hf : Periodic (f ∘ ofComplex) h) (hg : Periodic (g ∘ ofComplex) h) : Periodic ((f * g) ∘ ofComplex) h`
- **What**: h-periodicity (as functions on ℂ via `ofComplex`) is closed under pointwise product.
- **How**: `Function.Periodic.mul` gives periodicity of the pointwise product; `Pi.mul_apply` and `Function.comp_def` reconcile `(f*g) ∘ ofComplex` with the product of composites.
- **Hypotheses**: f∘ofComplex and g∘ofComplex are h-periodic.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 83–87, 1-line proof
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.periodic_comp_ofComplex_add`
- **Type**: `(hf : Periodic (f ∘ ofComplex) h) (hg : Periodic (g ∘ ofComplex) h) : Periodic ((f + g) ∘ ofComplex) h`
- **What**: h-periodicity via `ofComplex` is closed under pointwise sum.
- **How**: `Function.Periodic.add` plus the `Pi.add_apply`/`Function.comp_def` unfolding.
- **Hypotheses**: both composites h-periodic.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 89–93, 1-line proof
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.periodic_comp_ofComplex_sub`
- **Type**: `(hf : Periodic (f ∘ ofComplex) h) (hg : Periodic (g ∘ ofComplex) h) : Periodic ((f - g) ∘ ofComplex) h`
- **What**: h-periodicity via `ofComplex` is closed under pointwise difference.
- **How**: `Function.Periodic.sub` plus `Pi.sub_apply`/`Function.comp_def` unfolding.
- **Hypotheses**: both composites h-periodic.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 95–99, 1-line proof
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.periodic_comp_ofComplex_neg`
- **Type**: `(hf : Periodic (f ∘ ofComplex) h) : Periodic ((-f) ∘ ofComplex) h`
- **What**: h-periodicity via `ofComplex` is preserved under pointwise negation.
- **How**: Post-composition of the periodic function with the negation map z ↦ −z on the codomain (`Function.Periodic.comp`) — negating values does not affect periodicity; `Pi.neg_apply` reconciles the statements.
- **Hypotheses**: f∘ofComplex is h-periodic.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 101–104, 1-line proof
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.periodic_comp_ofComplex_smul`
- **Type**: `(a : ℂ) (hf : Periodic (f ∘ ofComplex) h) : Periodic ((a • f) ∘ ofComplex) h`
- **What**: h-periodicity via `ofComplex` is preserved under scalar multiplication by a complex constant.
- **How**: `Function.Periodic.smul` on the composite, with `Pi.smul_apply`/`Function.comp_def` unfolding.
- **Hypotheses**: f∘ofComplex is h-periodic.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 106–110, 1-line proof
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.mdiff_mul`
- **Type**: `(hf : MDiff f) (hg : MDiff g) : MDiff (f * g)`
- **What**: Holomorphy on ℍ (manifold-differentiability into ℂ) is closed under pointwise product.
- **How**: Mathlib's `MDiff.mul` (product rule for manifold-differentiable ℂ-valued maps).
- **Hypotheses**: f, g holomorphic on ℍ.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 112–114, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.mdiff_add`
- **Type**: `(hf : MDiff f) (hg : MDiff g) : MDiff (f + g)`
- **What**: Holomorphy on ℍ is closed under pointwise sum.
- **How**: Mathlib's `MDiff.add`.
- **Hypotheses**: f, g holomorphic on ℍ.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 116–118, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.mdiff_sub`
- **Type**: `(hf : MDiff f) (hg : MDiff g) : MDiff (f - g)`
- **What**: Holomorphy on ℍ is closed under pointwise difference.
- **How**: Mathlib's `MDiff.sub`.
- **Hypotheses**: f, g holomorphic on ℍ.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 120–122, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.mdiff_neg`
- **Type**: `(hf : MDiff f) : MDiff (-f)`
- **What**: Holomorphy on ℍ is preserved under pointwise negation.
- **How**: Mathlib's `MDiff.neg`.
- **Hypotheses**: f holomorphic on ℍ.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 124–126, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.mdiff_smul`
- **Type**: `(a : ℂ) (hf : MDiff f) : MDiff (a • f)`
- **What**: Holomorphy on ℍ is preserved under scalar multiplication by a complex constant.
- **How**: Mathlib's `MDiff.const_smul`.
- **Hypotheses**: f holomorphic on ℍ.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 128–130, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.isBoundedAtImInfty_mul`
- **Type**: `(hf : IsBoundedAtImInfty f) (hg : IsBoundedAtImInfty g) : IsBoundedAtImInfty (f * g)`
- **What**: Boundedness at the cusp i∞ is closed under pointwise product.
- **How**: Mathlib's `BoundedAtFilter.mul` (`hf.mul hg`): a product of eventually-bounded functions is eventually bounded.
- **Hypotheses**: f, g bounded at i∞.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 132–135, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.isBoundedAtImInfty_add`
- **Type**: `(hf : IsBoundedAtImInfty f) (hg : IsBoundedAtImInfty g) : IsBoundedAtImInfty (f + g)`
- **What**: Boundedness at i∞ is closed under pointwise sum.
- **How**: Mathlib's `BoundedAtFilter.add`.
- **Hypotheses**: f, g bounded at i∞.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 137–140, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.isBoundedAtImInfty_sub`
- **Type**: `(hf : IsBoundedAtImInfty f) (hg : IsBoundedAtImInfty g) : IsBoundedAtImInfty (f - g)`
- **What**: Boundedness at i∞ is closed under pointwise difference.
- **How**: Rewrites f − g as f + (−g) via `sub_eq_add_neg` and applies `BoundedAtFilter.add` with `BoundedAtFilter.neg` (`hf.add hg.neg`).
- **Hypotheses**: f, g bounded at i∞.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 142–145, 1-line proof
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.isBoundedAtImInfty_neg`
- **Type**: `(hf : IsBoundedAtImInfty f) : IsBoundedAtImInfty (-f)`
- **What**: Boundedness at i∞ is preserved under pointwise negation.
- **How**: Mathlib's `BoundedAtFilter.neg`.
- **Hypotheses**: f bounded at i∞.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 147–149, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `lemma QExpSimp.isBoundedAtImInfty_smul`
- **Type**: `(a : ℂ) (hf : IsBoundedAtImInfty f) : IsBoundedAtImInfty (a • f)`
- **What**: Boundedness at i∞ is preserved under scalar multiplication by a complex constant.
- **How**: Direct application of mathlib's `Filter.BoundedAtFilter.smul a hf`.
- **Hypotheses**: f bounded at i∞.
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 151–154, term-mode 1 line
- **Notes**: `@[qexp_simps]`

### `attribute [qexp_simps] (4 attribute commands, lines 158–163)`
- **Type**: n/a (attribute assignment commands)
- **What**: Enrolls a batch of mathlib lemmas into the `qexp_simps` simp set: (i) arithmetic normalizers `one_pos`, `pow_zero`, `pow_one`, `pow_succ`, `one_mul`, `mul_one`, `sub_eq_add_neg`; (ii) `one_mem_strictPeriods_SL` (1 is a strict period of SL₂(ℤ)-type groups); (iii) the analytic facts `analyticAt_cuspFunction_zero`, `differentiableAt_cuspFunction`, `differentiableOn_cuspFunction_ball`; (iv) the q-expansion ring homomorphism lemmas `qExpansion_zero/one/mul/add/sub/neg/smul` (the q-expansion of a sum/product/scalar multiple is the sum/product/scalar multiple of q-expansions).
- **How**: Pure `attribute` commands; the mathematics lives in the tagged mathlib lemmas, notably that `qExpansion h` behaves ring-homomorphically on functions whose cusp functions are analytic at 0.
- **Hypotheses**: none (side conditions of the tagged lemmas are discharged at simp time by the rest of the set, using `maxDischargeDepth := 20` in the macros)
- **Uses from project**: [`qexp_simps` attribute]
- **Used by**: qexp_simp macros (via simp set)
- **Visibility**: public
- **Lines**: 158–163, no proof
- **Notes**: none

### `macro qexp_simp (bare form)`
- **Type**: `macro "qexp_simp" : tactic`
- **What**: The main experimental tactic for q-expansion goals: closes goals about periodicity, holomorphy, boundedness/vanishing at i∞, analyticity of cusp functions, constant terms of cusp forms, convergence of q-expansions (`HasSum`), and integral formulas for q-expansion coefficients.
- **How**: A `first`-alternation: try `simp only [qexp_simps]` with `maxDischargeDepth := 20` (so conditional rewrites like `qExpansion_mul` can recursively discharge analyticity/periodicity side conditions); failing that, `apply` one of the class-based lemmas (`periodic_comp_ofComplex_of_slashInvariantFormClass`, `mdiff_of_modularFormClass`, `isBoundedAtImInfty_of_modularFormClass`, `isZeroAtImInfty_of_cuspFormClass`, `cuspFunction_apply_zero_of_cuspFormClass`) or a mathlib q-expansion theorem (`hasSum_qExpansion`, `hasSum_qExpansion_of_norm_lt`, `qExpansion_coeff_zero`, `qExpansion_coeff_eq_circleIntegral`, `qExpansion_coeff_eq_intervalIntegral`), then clean up remaining side goals with the same simp call.
- **Hypotheses**: n/a (tactic; needed facts must be in context or derivable from the simp set / instances)
- **Uses from project**: [`qexp_simps` simp set, `QExpSimp.periodic_comp_ofComplex_of_slashInvariantFormClass`, `QExpSimp.mdiff_of_modularFormClass`, `QExpSimp.isBoundedAtImInfty_of_modularFormClass`, `QExpSimp.isZeroAtImInfty_of_cuspFormClass`, `QExpSimp.cuspFunction_apply_zero_of_cuspFormClass`]
- **Used by**: unused in file (exercised by `QExpSimpConditionTests.lean`)
- **Visibility**: public
- **Lines**: 165–185, 21-line macro body
- **Notes**: sets `maxDischargeDepth := 20` in each simp call (config option, not `set_option`); 11-branch `first` alternation duplicated with the bracketed form below

### `macro qexp_simp [args] (simp-argument form)`
- **Type**: `macro "qexp_simp" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic`
- **What**: Variant of `qexp_simp` accepting user-supplied extra simp lemmas/hypotheses (e.g. local periodicity or holomorphy hypotheses), merged into every simp call of the alternation.
- **How**: Identical 11-branch `first`-alternation as the bare form, with `$args,*` prepended to `qexp_simps` in each `simp only` call; the extra hypotheses let the discharger close side conditions that are goal-local rather than instance-derived.
- **Hypotheses**: n/a (tactic)
- **Uses from project**: [`qexp_simps` simp set, `QExpSimp.periodic_comp_ofComplex_of_slashInvariantFormClass`, `QExpSimp.mdiff_of_modularFormClass`, `QExpSimp.isBoundedAtImInfty_of_modularFormClass`, `QExpSimp.isZeroAtImInfty_of_cuspFormClass`, `QExpSimp.cuspFunction_apply_zero_of_cuspFormClass`]
- **Used by**: unused in file (exercised by `QExpSimpConditionTests.lean`)
- **Visibility**: public
- **Lines**: 187–207, 21-line macro body
- **Notes**: near-verbatim duplicate of the bare macro (only the simp-argument splice differs) — a candidate for factoring through a single implementation

### File Summary
- Total declarations: 30 (0 defs, 27 lemmas/theorems, 0 instances, 3 tactic/meta decls: 2 macros + 1 batch of attribute commands)
- Key API (used by 3+ others): [`qexp_simps` simp set (all 27 lemmas + the attribute batch feed it; both macros consume it)]
- Unused declarations (not used by anything in this file): [both `qexp_simp` macros — used only in test file `QExpSimpConditionTests.lean`; all 27 lemmas are used only implicitly via the simp set]
- Declarations with sorry: []
- Declarations with set_option: [] (both macros use per-call `simp (config := { maxDischargeDepth := 20 })`, not `set_option`)
- Proofs >30 lines: []
