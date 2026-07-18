# XYin/PhD/Tactic2/QExpSimpConditionTests.lean
Project-internal imports: XYin.PhD.Tactic2.qexp_simp, XYin.PhD.jFunction.Deltaqexpansions

Pure test file: 8 anonymous `example`s exercising the `qexp_simp` tactic, no named declarations.

### `example (test 1, general product-minus analyticity)`
- **Type**: `(hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (hgper : Periodic (g ∘ ofComplex) h) (hfhol : MDiff f) (hghol : MDiff g) (hfbdd : IsBoundedAtImInfty f) (hgbdd : IsBoundedAtImInfty g) : AnalyticAt ℂ (cuspFunction h (f*g - f)) 0`
- **What**: Tests that `qexp_simp` proves analyticity at q = 0 of the cusp function of the compound expression f·g − f, given periodicity, holomorphy, and boundedness of f and g individually.
- **How**: Single call `qexp_simp [hh, hfper, hgper, hfhol, hghol, hfbdd, hgbdd]`; internally the simp set decomposes f·g − f via `analyticAt_cuspFunction_sub`/`analyticAt_cuspFunction_mul` and discharges each leaf from mathlib's `analyticAt_cuspFunction_zero` with the supplied hypotheses (conditional-rewrite discharge depth 20).
- **Hypotheses**: h > 0; f, g are h-periodic through `ofComplex`, holomorphic on ℍ, and bounded at i∞.
- **Uses from project**: [`qexp_simp` macro (bracketed form), `qexp_simps` simp set (transitively `QExpSimp.analyticAt_cuspFunction_sub`, `QExpSimp.analyticAt_cuspFunction_mul`)]
- **Used by**: unused in file
- **Visibility**: public (anonymous example)
- **Lines**: 11–17, 1-line proof
- **Notes**: none

### `example (test 2, differentiability on unit ball)`
- **Type**: same 7 hypotheses as test 1; conclusion `DifferentiableOn ℂ (cuspFunction h (f * g)) (Metric.ball 0 1)`
- **What**: Tests that `qexp_simp` proves the cusp function of a product is complex-differentiable on the open unit q-disc.
- **How**: `qexp_simp` with all hypotheses; the tagged mathlib lemma `differentiableOn_cuspFunction_ball` fires, with its periodicity/holomorphy/boundedness side conditions closed by the closure lemmas (`QExpSimp.periodic_comp_ofComplex_mul`, `QExpSimp.mdiff_mul`, `QExpSimp.isBoundedAtImInfty_mul`) applied to the hypotheses.
- **Hypotheses**: as test 1.
- **Uses from project**: [`qexp_simp` macro (bracketed form), `qexp_simps` simp set]
- **Used by**: unused in file
- **Visibility**: public (anonymous example)
- **Lines**: 19–25, 1-line proof
- **Notes**: none

### `example (test 3, HasSum of q-expansion)`
- **Type**: `(hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (τ : ℍ) : HasSum (fun m ↦ (qExpansion h f).coeff m • Periodic.qParam h τ ^ m) (f τ)`
- **What**: Tests that `qexp_simp` proves convergence of the q-expansion: the series Σ aₘ qᵐ (with q = e^{2πiτ/h}) sums to f(τ).
- **How**: The macro's `apply hasSum_qExpansion` branch fires (mathlib's convergence theorem for q-expansions of bounded periodic holomorphic functions), and the trailing `simp only [qexp_simps]` with the supplied hypotheses closes the three side conditions.
- **Hypotheses**: h > 0; f h-periodic through `ofComplex`, holomorphic, bounded at i∞.
- **Uses from project**: [`qexp_simp` macro (bracketed form), `qexp_simps` simp set]
- **Used by**: unused in file
- **Visibility**: public (anonymous example)
- **Lines**: 27–34, 1-line proof
- **Notes**: none

### `example (test 4, E4 periodicity)`
- **Type**: `Function.Periodic (E4 ∘ UpperHalfPlane.ofComplex) 1`
- **What**: Tests the instance-driven branch: the Eisenstein series E₄ (a level-one modular form) is 1-periodic as a function on ℂ.
- **How**: The macro's `apply QExpSimp.periodic_comp_ofComplex_of_slashInvariantFormClass` branch fires using the `SlashInvariantFormClass` instance for `ModularForm`, with the strict-period side goal `1 ∈ Γ(1).strictPeriods` closed by the simp set (`QExpSimp.one_mem_strictPeriods_gamma1` / `one_mem_strictPeriods_SL`).
- **Hypotheses**: none (instance-derived from E4 : ModularForm Γ(1) 4)
- **Uses from project**: [`qexp_simp` macro (bare form), `E4` (abbrev for `E₄`, XYin.PhD.jFunction.Deltaqexpansions), `qexp_simps` simp set]
- **Used by**: unused in file
- **Visibility**: public (anonymous example, `noncomputable`)
- **Lines**: 40–41, 1-line proof
- **Notes**: none

### `example (test 5, E4 holomorphy)`
- **Type**: `MDiff E4`
- **What**: Tests that `qexp_simp` proves holomorphy of E₄ from its `ModularFormClass` instance.
- **How**: The macro's `apply QExpSimp.mdiff_of_modularFormClass` branch fires (wrapping mathlib's `ModularFormClass.holo`).
- **Hypotheses**: none (instance-derived)
- **Uses from project**: [`qexp_simp` macro (bare form), `E4`]
- **Used by**: unused in file
- **Visibility**: public (anonymous example, `noncomputable`)
- **Lines**: 43–44, 1-line proof
- **Notes**: none

### `example (test 6, E4 boundedness at i∞)`
- **Type**: `IsBoundedAtImInfty E4`
- **What**: Tests that `qexp_simp` proves E₄ is bounded at the cusp i∞.
- **How**: The `apply QExpSimp.isBoundedAtImInfty_of_modularFormClass` branch fires (wrapping `ModularFormClass.bdd_at_infty`), the `Fact (IsCusp ∞ Γ(1))` instance being found by instance search.
- **Hypotheses**: none (instance-derived)
- **Uses from project**: [`qexp_simp` macro (bare form), `E4`]
- **Used by**: unused in file
- **Visibility**: public (anonymous example, `noncomputable`)
- **Lines**: 46–47, 1-line proof
- **Notes**: none

### `example (test 7, Delta vanishing at i∞)`
- **Type**: `IsZeroAtImInfty Delta`
- **What**: Tests that `qexp_simp` proves the discriminant cusp form Δ tends to 0 at i∞.
- **How**: The `apply QExpSimp.isZeroAtImInfty_of_cuspFormClass` branch fires (wrapping `CuspFormClass.zero_at_infty`) using the `CuspFormClass` instance of `Delta : CuspForm Γ(1) 12`.
- **Hypotheses**: none (instance-derived)
- **Uses from project**: [`qexp_simp` macro (bare form), `Delta` (XYin.PhD.Modularforms.Delta, via Deltaqexpansions import)]
- **Used by**: unused in file
- **Visibility**: public (anonymous example, `noncomputable`)
- **Lines**: 49–50, 1-line proof
- **Notes**: none

### `example (test 8, Delta constant term zero)`
- **Type**: `cuspFunction 1 Delta 0 = 0`
- **What**: Tests that `qexp_simp` proves the cusp function of Δ vanishes at q = 0, i.e. Δ has zero constant term.
- **How**: The `apply QExpSimp.cuspFunction_apply_zero_of_cuspFormClass` branch fires (wrapping `CuspFormClass.cuspFunction_apply_zero`), with side goals `0 < 1` and `1 ∈ Γ(1).strictPeriods` closed by the simp set (`one_pos`, `QExpSimp.one_mem_strictPeriods_gamma1`).
- **Hypotheses**: none (instance-derived)
- **Uses from project**: [`qexp_simp` macro (bare form), `Delta`, `qexp_simps` simp set]
- **Used by**: unused in file
- **Visibility**: public (anonymous example, `noncomputable`)
- **Lines**: 52–53, 1-line proof
- **Notes**: none

### File Summary
- Total declarations: 8 (0 defs, 0 lemmas/theorems, 0 instances, 0 tactic/meta decls; 8 anonymous examples)
- Key API (used by 3+ others): [] (test file; every example independently exercises `qexp_simp` from XYin.PhD.Tactic2.qexp_simp)
- Unused declarations (not used by anything in this file): [all 8 examples — anonymous tests by design]
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: []
