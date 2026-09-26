# Inventory: XYin/PhD/Cox/ModularFunction/CuspData.lean  (154 lines)

Defines the raw analytic predicate `CuspData N f` (meromorphy on ℍ, weight-0 `Γ₀(N)`-invariance, meromorphic width-`N` cusp expansions after every `SL₂(ℤ)` transform) that Cox's pole-clearing and interpolation proofs manipulate pointwise, derives it from the bundled `ModularFunction (Gamma0 N)`, and proves closure under pointwise product and polynomial evaluation. Also defines the pointwise rationality predicates `RationalIn` and `RationalInTwo` used to state Theorem 11.9.

## Declarations

### `def Cox.CuspData`
- **Type**: `(N : ℕ+) (f : ℍ → ℂ) : Prop` := `(∀ z : ℂ, 0 < z.im → MeromorphicAt (f ∘ ofComplex) z) ∧ (∀ γ : Gamma0 N, f ∣[(0:ℤ)] (γ : SL(2,ℤ)) = f) ∧ (∀ γ : SL(2,ℤ), MeromorphicAt (cuspFunction (N:ℝ) (fun τ ↦ f (γ • τ))) 0)`
- **What**: Raw "modular function of level `N`" data without normal-form normalization: meromorphic on ℍ, weight-zero invariant under `Γ₀(N)`, and with meromorphic period-`N` q-expansion at every cusp.
- **How**: A conjunction of three `Prop`s; components are accessed by `.1`, `.2.1`, `.2.2` throughout the Cox files.
- **Hypotheses**: none (definition).
- **Uses from project**: `UpperHalfPlane.cuspFunction` (mathlib)
- **Used by**: `LevelOneCuspData`, `periodic_comp_sl2`, `CuspData.of_modularFunction`, `j_cuspData`, `CuspData.mul`, `CuspData.polynomialIn`
- **Visibility**: public
- **Lines**: 30–34
- **Notes**: Anonymous-conjunction design: no projections `CuspData.meromorphicAt`, `.slash_invariant`, `.cuspFunction_meromorphicAt` exist, so every consumer writes `hf.1 z hz`, `hf.2.1 γ`, `hf.2.2 γ` (ModularFunction.lean:49, 82, 90, 209, 249, 274, 324; CuspData.lean:69, 103, 106, 111; CoxMatrices/Basic.lean:621; DiagonalLaurent.lean:30, 161, 179; IntegralDescent.lean:33, 47; AnalyticSupport.lean:30; Interpolation.lean many). A `structure` with named fields would be the mathlib-style form. External definers/consumers: `CoxMatrices/Basic.lean:616` (`rightCosetTranslate` takes `hf : CuspData m f` and uses only `hf.2.1`), Interpolation.lean (`interpolationAt`, `interpolation_coeff_cuspData`, `theorem_11_9_ii_pointwise`).

### `abbrev Cox.LevelOneCuspData`
- **Type**: `(f : ℍ → ℂ) : Prop := CuspData (1 : ℕ+) f`
- **What**: Level-one specialization: `SL₂(ℤ)`-invariant with meromorphic width-1 cusp expansion.
- **How**: abbreviation.
- **Hypotheses**: none.
- **Uses from project**: `CuspData`
- **Used by**: `CuspData.of_levelOneModularFunction`, `j_levelOneCuspData`
- **Visibility**: public
- **Lines**: 37–38
- **Notes**: External: ModularFunction.lean (12 uses), Interpolation.lean:276 (`interpolation_coeff_cuspData`).

### `def Cox.polynomialIn`
- **Type**: `(P : Polynomial ℂ) (g : ℍ → ℂ) : ℍ → ℂ := fun τ ↦ P.eval (g τ)`
- **What**: Pointwise evaluation of a complex polynomial at a function, i.e. `P(g)`.
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: `CuspData.polynomialIn`
- **Visibility**: public
- **Lines**: 41–42
- **Notes**: No companion simp lemmas (`polynomialIn_C`, `_X`, `_add`, `_mul`, `_apply`, `_monomial`); consumers unfold it by `simp only [polynomialIn]`/`change` (ModularFunction.lean:217, 237, 389, 422, 428; DiagonalLaurent.lean:163–184; IntegralDescent.lean:35–50; Construction.lean:298). It is `Polynomial.aeval g P` in the Pi-algebra `ℍ → ℂ` (mathlib `Polynomial.aeval_fn_apply`, see Observations). External uses: DiagonalLaurent.lean:160–182, Construction.lean:285, 298, IntegralDescent.lean:32–49, 108–147, 266, 272.

### `def Cox.RationalIn`
- **Type**: `(f g : ℍ → ℂ) : Prop := ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ τ, Q.eval (g τ) ≠ 0 → f τ = P.eval (g τ) / Q.eval (g τ)`
- **What**: `f` is a rational function of `g`, pointwise, off the zero set of a chosen nonzero denominator.
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 48–50
- **Notes**: Conclusion form of `theorem_11_9_i` (ModularFunction.lean:431) and `CuspData.rationalInJ`; consumed by Interpolation.lean:354 (`exists_commonDenominator_polynomialEval_of_natDegree_lt`) and :468. `Q ≠ 0` as a polynomial is the right condition only because `j` is surjective (`j_surjective`, LatticeJ.lean:626) — otherwise `Q(g)` could vanish identically. Contrast `RationalInTwo`, where the denominator must be nonzero as a function.

### `def Cox.RationalInTwo`
- **Type**: `(f g h : ℍ → ℂ) : Prop := ∃ P Q : ℂ[X][Y], (fun τ ↦ Q.evalEval (g τ) (h τ)) ≠ 0 ∧ ∀ τ, Q.evalEval (g τ) (h τ) ≠ 0 → f τ = P.evalEval (g τ) (h τ) / Q.evalEval (g τ) (h τ)`
- **What**: `f` is a rational function of the pair `(g, h)`, with denominator nonzero as a function on the parametrized curve `τ ↦ (g τ, h τ)`.
- **How**: definition; the docstring explains why "`Q ≠ 0` as a bivariate polynomial" would be vacuous (the modular equation `Φ_N(g,h) = 0` is a nonzero `Q` vanishing identically).
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 56–59
- **Notes**: Conclusion form of `theorem_11_9_ii_pointwise` (Interpolation.lean:488–490); unfolded by `obtain ⟨P, Q, hQ, hPQ⟩` at ModularFunctionField.lean:155 and Interpolation.lean:469. Denominator condition is exactly `evalJLevel N Q ≠ 0` in the language of ModularFunctionField.lean (cf. `toMeromorphicField_eq_evalJLevel_div_of`, lines 96–100 there).

### `theorem Cox.periodic_comp_sl2`
- **Type**: `(N : ℕ+) {f : ℍ → ℂ} (hf : CuspData N f) (γ : SL(2, ℤ)) : Periodic (fun z : ℂ ↦ f (γ • ofComplex z)) (N : ℂ)`
- **What**: Every `SL₂(ℤ)`-transform of a `Γ₀(N)`-invariant function has period `N` (as a function of `z ∈ ℂ` through `ofComplex`).
- **How**: Direct application of `ModularFunction.periodic_comp_sl2_of_gamma0_invariant N hf.2.1 γ`.
- **Hypotheses**: cusp data (only the invariance component is used).
- **Uses from project**: `CuspData`, `ModularFunction.periodic_comp_sl2_of_gamma0_invariant`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 62–64, proof body ≈ 1 line
- **Notes**: One-line wrapper; external uses only ModularFunction.lean:35, 247. Hypothesis could be weakened to the invariance component alone (which is what the wrapped lemma takes).

### `theorem Cox.CuspData.of_modularFunction`
- **Type**: `(N : ℕ+) (f : ModularFunction (Gamma0 N)) : CuspData N f`
- **What**: The bridge from the bundled definition to raw data: a bundled `Γ₀(N)` modular function has cusp data.
- **How**: `⟨f.meromorphicOn, fun γ ↦ f.slash_action_eq' _ ⟨γ, γ.property, rfl⟩, ModularFunction.cuspFunction_gamma0 N f⟩`.
- **Hypotheses**: `f` bundled level-`N` modular function.
- **Uses from project**: `CuspData`, `ModularFunction`, `ModularFunction.meromorphicOn`, `ModularFunction.cuspFunction_gamma0`
- **Used by**: `CuspData.of_levelOneModularFunction`, `j_cuspData`
- **Visibility**: public
- **Lines**: 67–70, proof body ≈ 2 lines
- **Notes**: Load-bearing: external uses Interpolation.lean:491 (`theorem_11_9_ii_pointwise`), LevelJ.lean:327. The invariance component is exactly `SlashInvariantFormClass.slash_action_eq` specialized to `Gamma0 N ≤ 𝒮ℒ` via `⟨γ, γ.property, rfl⟩` (the `Subgroup.map` membership witness) — a standalone `ModularFunction.slash_gamma0` lemma is missing (the same witness is written at Congruence.lean:92).

### `theorem Cox.CuspData.of_levelOneModularFunction`
- **Type**: `(f : ModularFunction 𝒮ℒ) : LevelOneCuspData f`
- **What**: A bundled level-one modular function has level-one cusp data.
- **How**: `CuspData.of_modularFunction 1 (f.restrict (Subgroup.map_le_range ..))`.
- **Hypotheses**: bundled `SL₂(ℤ)` modular function.
- **Uses from project**: `LevelOneCuspData`, `ModularFunction`, `ModularFunction.restrict`, `CuspData.of_modularFunction`
- **Used by**: `j_levelOneCuspData`
- **Visibility**: public
- **Lines**: 73–75, proof body ≈ 1 line
- **Notes**: External uses ModularFunction.lean:432, 437 (`theorem_11_9_i`, `levelOne_polynomialInJ_of_holomorphic`).

### `theorem Cox.j_cuspData`
- **Type**: `(N : ℕ+) : CuspData N j`
- **What**: `j` has level-`N` cusp data for every `N` (restriction of the level-one bundle).
- **How**: `CuspData.of_modularFunction N (jModularFunction.restrict (Subgroup.map_le_range ..))`.
- **Hypotheses**: none.
- **Uses from project**: `CuspData`, `j`, `CuspData.of_modularFunction`, `jModularFunction`, `ModularFunction.restrict`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 78–79, proof body ≈ 1 line
- **Notes**: External: DiagonalLaurent.lean:30, 161, 179 (width-`m` expansions of `j`).

### `theorem Cox.j_levelOneCuspData`
- **Type**: `LevelOneCuspData j`
- **What**: `j` has level-one cusp data.
- **How**: `CuspData.of_levelOneModularFunction jModularFunction`.
- **Hypotheses**: none.
- **Uses from project**: `LevelOneCuspData`, `j`, `CuspData.of_levelOneModularFunction`, `jModularFunction`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 82–83, proof body ≈ 1 line
- **Notes**: Propositionally identical to `j_cuspData 1` (`LevelOneCuspData j` is by `abbrev` `CuspData 1 j`) — moral duplicate. External: IntegralDescent.lean:33, 47; ModularFunction.lean:226, 423.

### `private lemma Cox.cuspFunction_mul_eventuallyEq`
- **Type**: `(h : ℝ) (f g : ℍ → ℂ) : cuspFunction h (fun τ ↦ f τ * g τ) =ᶠ[nhdsWithin 0 {0}ᶜ] fun q ↦ cuspFunction h f q * cuspFunction h g q`
- **What**: Off `q = 0`, the cusp function of a product is the product of cusp functions.
- **How**: `filter_upwards [self_mem_nhdsWithin]`, `Periodic.cuspFunction_eq_of_nonzero` ×3, `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: `CuspData.mul`
- **Visibility**: private
- **Lines**: 86–95, proof body ≈ 7 lines
- **Notes**: Verbatim duplicate (same name, statement, proof) of the private `cuspFunction_mul_eventuallyEq` at LaurentQExpansion.lean:79, which is already in the import closure (Congruence → JInvariant → jfunction → LaurentQExpansion).

### `theorem Cox.CuspData.mul`
- **Type**: `{N : ℕ+} {f g : ℍ → ℂ} (hf : CuspData N f) (hg : CuspData N g) : CuspData N (fun τ ↦ f τ * g τ)`
- **What**: Raw cusp data is closed under pointwise multiplication.
- **How**: `MeromorphicAt.mul` on ℍ; invariance by `congrArg₂ (·*·)` on slash identities after `SL_slash_apply`; cusp component via `(hf.2.2 γ).mul (hg.2.2 γ)` and `MeromorphicAt.congr` with `cuspFunction_mul_eventuallyEq`.
- **Hypotheses**: both have level-`N` cusp data.
- **Uses from project**: `CuspData`, `cuspFunction_mul_eventuallyEq`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 98–113, proof body ≈ 13 lines
- **Notes**: Only consumer anywhere is ModularFunction.lean:423 (`CuspData.rationalInJ`). Docstring says "Raw analytic cusp data is preserved by pointwise multiplication". Companion closure lemmas `CuspData.add`, `.sub`, `.neg`, `.const_mul`, `.pow`, `.const` are missing (ModularFunction.lean:75 hand-rolls `sub_const_mul_pow`).

### `private lemma Cox.meromorphicAt_polynomial_eval`
- **Type**: `{g : ℂ → ℂ} {z : ℂ} (hg : MeromorphicAt g z) (P : Polynomial ℂ) : MeromorphicAt (fun w ↦ P.eval (g w)) z`
- **What**: A polynomial in a meromorphic function is meromorphic.
- **How**: `Polynomial.induction_on'` with `MeromorphicAt.add`, `MeromorphicAt.const.mul (hg.pow n)`.
- **Hypotheses**: `g` meromorphic at `z`.
- **Uses from project**: `[]`
- **Used by**: `CuspData.polynomialIn` (twice)
- **Visibility**: private
- **Lines**: 115–123, proof body ≈ 7 lines
- **Notes**: Generic; no mathlib analogue found (searched `MeromorphicAt.*[Pp]olynomial`, `meromorphicAt_eval`, `MeromorphicOn.eval` over `Mathlib/Analysis/Meromorphic/`). Candidate mathlib addition `MeromorphicAt.polynomial_eval`.

### `private lemma Cox.cuspFunction_polynomial_eval_eventuallyEq`
- **Type**: `(h : ℝ) (g : ℍ → ℂ) (P : Polynomial ℂ) : cuspFunction h (fun τ ↦ P.eval (g τ)) =ᶠ[nhdsWithin 0 {0}ᶜ] fun q ↦ P.eval (cuspFunction h g q)`
- **What**: Off `q = 0`, the cusp function of `P(g)` is `P` of the cusp function of `g`.
- **How**: same skeleton as `cuspFunction_mul_eventuallyEq` with two rewrites.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: `CuspData.polynomialIn`
- **Visibility**: private
- **Lines**: 125–134, proof body ≈ 7 lines
- **Notes**: Third instance of the `cuspFunction … =ᶠ[𝓝[≠] 0]` skeleton (see ModularFunction.lean inventory).

### `theorem Cox.CuspData.polynomialIn`
- **Type**: `{N : ℕ+} {f : ℍ → ℂ} (hf : CuspData N f) (P : Polynomial ℂ) : CuspData N (Cox.polynomialIn P f)`
- **What**: Raw cusp data is closed under polynomial evaluation.
- **How**: `meromorphicAt_polynomial_eval` for both meromorphy components, `congrArg P.eval` for invariance, `MeromorphicAt.congr` with `cuspFunction_polynomial_eval_eventuallyEq`.
- **Hypotheses**: `f` has level-`N` cusp data.
- **Uses from project**: `CuspData`, `Cox.polynomialIn`, `meromorphicAt_polynomial_eval`, `cuspFunction_polynomial_eval_eventuallyEq`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 137–152, proof body ≈ 13 lines
- **Notes**: External: DiagonalLaurent.lean:161, 179; IntegralDescent.lean:33, 47 (all use only the `.2.2 1` cusp component); ModularFunction.lean:423.

## File Summary
- Total declarations: 15 (5 defs/abbrevs, 10 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `CuspData` (6)
- Unused declarations (not used by anything in this file): `RationalIn`, `RationalInTwo`, `periodic_comp_sl2`, `j_cuspData`, `j_levelOneCuspData`, `CuspData.mul`, `CuspData.polynomialIn` (all used externally — see Notes)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations

### Mathlib API candidates
- `CuspData` vs bundled `ModularFunction (Gamma0 N)` (Basic.lean:31): the bundle has `SlashInvariantForm` data (mathlib `Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean`), `meromorphic'` (normal-form representative) and exponential cusp growth; `CuspData` = `MeromorphicOn` + invariance + `cuspFunction_gamma0`, i.e. the bundle minus normal form. After the 2026-09-21 migration the only raw-to-bundle direction is `ModularFunction.ofGamma0CuspData` (Congruence.lean:115), which requires `MeromorphicNFOn`; there is deliberately no `CuspData → ModularFunction` map. The invariance component `∀ γ : Gamma0 N, f ∣[0] γ = f` is redundant with `SlashInvariantFormClass` (`Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean`) once bundled; `of_modularFunction` (67–70) is where that redundancy is discharged.
- `polynomialIn P g` is `(Polynomial.aeval g P : ℍ → ℂ)` under `Pi.algebra`; mathlib `Polynomial.aeval_fn_apply` (`Mathlib/Algebra/Polynomial/AlgebraMap.lean`, grep-verified) gives `aeval g P τ = aeval (g τ) P = P.eval (g τ)`. Adopting `aeval` would provide `map_add/map_mul/aeval_C/aeval_X` for free and eliminate the manual `Polynomial.induction_on'` in DiagonalLaurent.lean:163–184 and IntegralDescent.lean:35–50.
- `RationalIn`/`RationalInTwo`: no mathlib analogue (searched `RationalIn`, `rational in`, `IsRationalFunction`). Their field-theoretic upgrades already exist in ModularFunctionField.lean (`toMeromorphicField_eq_ratFunc` = `f ∈ (algebraMap (RatFunc ℂ) FunctionField).range`; `toMeromorphicField_mem_jLevelFunctionField` = `f ∈ IntermediateField.adjoin (RatFunc ℂ) {j_N}`), which are the mathlib-native forms (`RatFunc`, `IntermediateField.adjoin`, `Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean`).
- `meromorphicAt_polynomial_eval` (115–123): no mathlib analogue (see Notes); candidate contribution alongside `MeromorphicAt.pow`/`MeromorphicAt.mul` in `Mathlib/Analysis/Meromorphic/Basic.lean`.
- The analytic counterpart *does* exist: `AnalyticAt.aeval_polynomial` (`.lake/packages/mathlib/Mathlib/Analysis/Analytic/Polynomial.lean:38`, `AnalyticAt 𝕜 f z → AnalyticAt 𝕜 (fun x ↦ aeval (f x) p) z`); `mdifferentiable_polynomialIn_j` (ModularFunction.lean:338) and the `MDiff`-closure of `polynomialIn` could ride on it via `mdifferentiable_iff`/`DifferentiableOn.analyticAt`, and the meromorphic version is the natural `MeromorphicAt.aeval_polynomial` to contribute next to it.
- `cuspFunction_mul_eventuallyEq` / `cuspFunction_polynomial_eval_eventuallyEq`: mathlib has only `UpperHalfPlane.cuspFunction_mul` (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:440`) which is pointwise at 0 under `ContinuousAt` hypotheses; the `=ᶠ[𝓝[≠] 0]` form is a project-wide gap (see below).

### Missing API / repeated patterns
- `CuspData` has no field projections or `structure` form; `.1/.2.1/.2.2` access appears at ≥ 20 sites across Cox (listed under `CuspData` Notes). Suggest `structure CuspData` with fields `meromorphicAt`, `slash_eq`, `cuspFunction_meromorphicAt`, plus `CuspData.apply_smul (γ : Gamma0 N) : f (γ • τ) = f τ` (idiom at 104–109, 144–148, ModularFunction.lean:46–49, 344–350, Interpolation.lean:283–287).
- Missing closure lemmas for `CuspData`: `add`, `sub`, `neg`, `const`, `const_mul`, `pow` (ModularFunction.lean:75–94 builds `sub_const_mul_pow` by hand from the same 3-bullet template as `mul` (98–113) and `polynomialIn` (137–152)).
- Missing simp lemmas for `polynomialIn`: `_apply`, `_C`, `_X`, `_add`, `_mul`, `_monomial`, `polynomialIn_j_mdifferentiable` (private at ModularFunction.lean:338).
- Missing `MeromorphicAt.polynomial_eval` public (private at 115).
- Missing `UpperHalfPlane.cuspFunction_comp₂_eventuallyEq` — the `=ᶠ[𝓝[≠] 0]` template is duplicated at 86–95, 125–134, ModularFunction.lean:63–73, LaurentQExpansion.lean:68/79/90, Algebra.lean:55.

### Junk candidates
- `cuspFunction_mul_eventuallyEq` (86–95): exact duplicate of `LaurentQExpansion.lean:79` (private there too); make the latter public and delete this one.
- `j_levelOneCuspData` (82–83): definitionally `j_cuspData 1`; keep one (or make the other an `abbrev`/`alias`).
- `periodic_comp_sl2` (62–64): one-line wrapper around `ModularFunction.periodic_comp_sl2_of_gamma0_invariant`, used only twice (ModularFunction.lean:35, 247); callers could use the wrapped lemma with `hf.2.1` directly.
- Blank double line at 84–85 (style).

### Moral duplicates within this batch
- `CuspData.mul` (98) / `CuspData.polynomialIn` (137) / ModularFunction.lean:75 `cuspData_sub_const_mul_pow`: same 3-bullet template.
- `cuspFunction_mul_eventuallyEq` (86) / `cuspFunction_polynomial_eval_eventuallyEq` (125) / ModularFunction.lean:63 / LaurentQExpansion.lean:68, 79, 90.
- `j_levelOneCuspData` (82) / `j_cuspData 1` (78).
- `CuspData.of_levelOneModularFunction` (73) is `CuspData.of_modularFunction 1 ∘ restrict` — thin, acceptable.

### Generalization notes
- `periodic_comp_sl2` needs only `hf.2.1` (invariance), not meromorphy — the wrapped `periodic_comp_sl2_of_gamma0_invariant` (Congruence.lean:69) already has the weaker hypothesis. Same for `rightCosetTranslate` (CoxMatrices/Basic.lean:616), which takes full `CuspData m f` but uses only `hf.2.1`.
- `RationalIn`/`RationalInTwo` are stated for `ℍ → ℂ` but nothing uses ℍ or ℂ: they make sense for `X → K` with `K` any field (`eval`, `evalEval`, `/`).
- `meromorphicAt_polynomial_eval` holds for `g : 𝕜 → 𝕜` over any `𝕜` `[NontriviallyNormedField 𝕜]` with `P : 𝕜[X]` (only `MeromorphicAt.add/mul/pow/const` used).
