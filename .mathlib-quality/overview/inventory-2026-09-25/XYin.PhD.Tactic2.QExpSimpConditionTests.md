# Inventory: XYin/PhD/Tactic2/QExpSimpConditionTests.lean  (55 lines)

Eight anonymous `example`s that are the only uses of the `qexp_simp` tactic in the project: three "general function" goals (analyticity of `cuspFunction h (f*g - f)` at 0, `DifferentiableOn` on the unit ball, `HasSum` of the q-expansion) closed by `qexp_simp [hyps]`, and five goals about the concrete forms `E4` and `Delta` (periodicity, `MDiff`, boundedness, vanishing at i∞, `cuspFunction 1 Delta 0 = 0`) closed by bare `qexp_simp` through the `apply`-fallback branches. Imports `XYin.PhD.Tactic2.qexp_simp` and `XYin.PhD.jFunction.Deltaqexpansions` (for `E4`, `Delta`). Contains NO declarations. Imported by the library root `XYin.lean:31`.

## Declarations

(none — only `open`, `variable`, `section` and `example`s; no copyright header, no module docstring)

### `example` — L11–17
- **Type**: `(hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (hgper : …) (hfhol : MDiff f) (hghol : MDiff g) (hfbdd : IsBoundedAtImInfty f) (hgbdd : IsBoundedAtImInfty g) : AnalyticAt ℂ (cuspFunction h (f * g - f)) 0`
- **What**: Analyticity of the cusp function of `f·g − f` from analyticity data of f, g.
- **How**: `qexp_simp [hh, …]`: `simp only` rewrites `f*g - f` to `f*g + -f` (`sub_eq_add_neg`), then `QExpSimp.analyticAt_cuspFunction_add/_neg/_mul` reduce to `AnalyticAt ℂ (cuspFunction h f) 0` etc., discharged by `analyticAt_cuspFunction_zero hh hfper hfhol hfbdd` (mathlib `QExpansion.lean:101`) with the hypotheses supplied as simp args.
- **Hypotheses**: h > 0; f, g h-periodic, holomorphic, bounded at i∞
- **Uses from project**: `qexp_simp` macro (with args), simp-set members `QExpSimp.analyticAt_cuspFunction_{add,neg,mul}`, tagged `analyticAt_cuspFunction_zero`, `sub_eq_add_neg`
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 11–17
- **Notes**: This is the one test that exercises the closure lemmas; it confirms the `_sub` lemmas are bypassed via `sub_eq_add_neg`.

### `example` — L19–25
- **Type**: same hypotheses : `DifferentiableOn ℂ (cuspFunction h (f * g)) (Metric.ball 0 1)`
- **What**: Differentiability of the cusp function of a product on the unit disc.
- **How**: tagged mathlib `differentiableOn_cuspFunction_ball` (`QExpansion.lean:95`) whose 4 hypotheses for `f*g` are discharged by `QExpSimp.periodic_comp_ofComplex_mul`, `mdiff_mul`, `isBoundedAtImInfty_mul` + the supplied args.
- **Hypotheses**: as above
- **Uses from project**: `qexp_simp`, `QExpSimp.periodic_comp_ofComplex_mul`, `QExpSimp.mdiff_mul`, `QExpSimp.isBoundedAtImInfty_mul`
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 19–25
- **Notes**: —

### `example` — L27–34
- **Type**: `(hh) (hfper) (hfhol) (hfbdd) (τ : ℍ) : HasSum (fun m ↦ (qExpansion h f).coeff m • Function.Periodic.qParam h τ ^ m) (f τ)`
- **What**: The q-expansion of f sums to f(τ).
- **How**: `apply hasSum_qExpansion <;> simp only [args, qexp_simps]` branch (mathlib `QExpansion.lean:189`).
- **Hypotheses**: h > 0; f periodic, holomorphic, bounded
- **Uses from project**: `qexp_simp`
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 27–34
- **Notes**: Uses mathlib's `𝕢` notation spelled out as `Function.Periodic.qParam`.

### `noncomputable example` — L40–41
- **Type**: `Function.Periodic (E4 ∘ UpperHalfPlane.ofComplex) 1`
- **What**: E₄ is 1-periodic.
- **How**: branch `apply QExpSimp.periodic_comp_ofComplex_of_slashInvariantFormClass <;> simp only [qexp_simps]` — side goal `1 ∈ Γ(1).strictPeriods` closed by `one_mem_strictPeriods_gamma1`/`one_mem_strictPeriods_SL`.
- **Hypotheses**: none
- **Uses from project**: `qexp_simp`, `E4` (Deltaqexpansions.lean:36, abbrev of mathlib `E₄`), `QExpSimp.periodic_comp_ofComplex_of_slashInvariantFormClass`, `QExpSimp.one_mem_strictPeriods_gamma1`
- **Used by**: n/a
- **Visibility**: n/a
- **Lines**: 40–41
- **Notes**: `noncomputable` on an `example` is meaningless (examples are never compiled); harmless.

### `noncomputable example` — L43–44
- **Type**: `MDiff E4`
- **What/How**: `apply QExpSimp.mdiff_of_modularFormClass` branch (= `ModularFormClass.holo`).
- **Hypotheses**: none
- **Uses from project**: `qexp_simp`, `E4`, `QExpSimp.mdiff_of_modularFormClass`
- **Used by**: n/a; **Visibility**: n/a; **Lines**: 43–44
- **Notes**: —

### `noncomputable example` — L46–47
- **Type**: `IsBoundedAtImInfty E4`
- **What/How**: `apply QExpSimp.isBoundedAtImInfty_of_modularFormClass` (= `ModularFormClass.bdd_at_infty`; needs the mathlib `Fact (IsCusp ∞ Γ(1))` instance).
- **Hypotheses**: none
- **Uses from project**: `qexp_simp`, `E4`, `QExpSimp.isBoundedAtImInfty_of_modularFormClass`
- **Used by**: n/a; **Visibility**: n/a; **Lines**: 46–47
- **Notes**: —

### `noncomputable example` — L49–50
- **Type**: `IsZeroAtImInfty Delta`
- **What/How**: `apply QExpSimp.isZeroAtImInfty_of_cuspFormClass` (= `CuspFormClass.zero_at_infty`).
- **Hypotheses**: none
- **Uses from project**: `qexp_simp`, `Delta` (Modularforms/Delta.lean:170), `QExpSimp.isZeroAtImInfty_of_cuspFormClass`
- **Used by**: n/a; **Visibility**: n/a; **Lines**: 49–50
- **Notes**: —

### `noncomputable example` — L52–53
- **Type**: `cuspFunction 1 Delta 0 = 0`
- **What/How**: `apply QExpSimp.cuspFunction_apply_zero_of_cuspFormClass <;> simp only [qexp_simps]` — side goals `0 < 1` (`one_pos`) and `1 ∈ strictPeriods` (`one_mem_strictPeriods_*`).
- **Hypotheses**: none
- **Uses from project**: `qexp_simp`, `Delta`, `QExpSimp.cuspFunction_apply_zero_of_cuspFormClass`, `QExpSimp.one_mem_strictPeriods_gamma1`
- **Used by**: n/a; **Visibility**: n/a; **Lines**: 52–53
- **Notes**: —

## File Summary
- Total declarations: 0 (0 defs, 0 lemmas/theorems, 0 instances, 0 other); 8 `example`s (3 with simp args, 5 bare; 5 marked `noncomputable`)
- Key API (used by 3+ others in the file): none
- Unused declarations: none
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations (evidence for the analysis phases)
### Mathlib API candidates
- Every one of the 8 goals is a direct mathlib lemma application: L11–17 ← `analyticAt_cuspFunction_zero` + `AnalyticAt.{mul,sub}` + `cuspFunction_{mul,sub}`; L19–25 ← `differentiableOn_cuspFunction_ball`; L27–34 ← `hasSum_qExpansion`; L40 ← `SlashInvariantFormClass.periodic_comp_ofComplex`; L43 ← `ModularFormClass.holo`; L46 ← `ModularFormClass.bdd_at_infty`; L49 ← `CuspFormClass.zero_at_infty`; L52 ← `CuspFormClass.cuspFunction_apply_zero` (all paths in the qexp_simp inventory). The tactic saves at most one `exact` per goal.

### Missing API / repeated patterns
- The 7-hypothesis context (L11–15 = L19–23) is repeated verbatim; a `variable` block or a bundled "f has a q-expansion" structure would remove it — but that is a design question for the tactic, not the tests.
- No test covers `qExpansion_coeff_zero`, `qExpansion_coeff_eq_circleIntegral`, `qExpansion_coeff_eq_intervalIntegral`, `hasSum_qExpansion_of_norm_lt` branches, nor `smul`/`neg`/`sub`-only goals, nor any `qExpansion_*` rewriting — so 4 of the 11 macro branches and the `qExpansion_*` part of the simp set are untested.

### Junk candidates
- Whole file: test-only, no declarations, imported by the library root (`XYin.lean:31`) — should live under a `test/` target outside the `XYin` lib; as it stands every library build re-runs these tactic calls.
- `noncomputable` on 5 `example`s (L40–52) is a no-op.
- No copyright header / module docstring.

### Moral duplicates within this batch
- L11–17 and L19–25 share the entire hypothesis list and differ only in the goal.
- Cross-batch: `link.lean:398–404` (`qj_qexpansion_link`) discharges `AnalyticAt` side conditions for `qExpansion_mul` by hand with `E4_pow_three_cuspFunction_analyticAt`/`qOverDelta_cuspFunction_analyticAt` — the kind of goal L11–17 shows `qexp_simp` can close, yet the tactic is not used there.

### Generalization notes
- None.
