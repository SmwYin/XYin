# Inventory: XYin/PhD/Modularforms/eta.lean  (81 lines)

Proves the Dedekind eta transformation law `η(−1/z) = (√i)⁻¹ · √z · η(z)` on the upper half-plane by the logarithmic-derivative method: `logDeriv (η ∘ (−1/·)) = logDeriv (csqrt · η)` (via mathlib's `logDeriv_eta_eq_E2` and the project's `E₂_S_transform`), hence the two functions agree up to a constant, which is pinned down at `z = i`. The whole file is now superseded verbatim by mathlib's `Mathlib/NumberTheory/ModularForms/Discriminant.lean:66–143` and nothing in the project uses any of its four lemmas.

## Declarations

### `lemma eta_logDeriv_eql`
- **Type**: `(z : ℍ) : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z = (logDeriv ((csqrt) * η)) z`
- **What**: The logarithmic derivatives of `z ↦ η(−1/z)` and `z ↦ √z·η(z)` agree on ℍ.
- **How**: Chain rule `logDeriv_comp` with `hasDerivAt_inv` for `−1/z`; `logDeriv_mul` splits `csqrt * η`; `logDeriv csqrt z = 1/(2z)` is computed from `Complex.hasDerivAt_log`; both `logDeriv η` terms are rewritten with mathlib `ModularForm.logDeriv_eta_eq_E2`, and the resulting identity is exactly `E₂_S_transform` after `field_simp; ring`.
- **Hypotheses**: `z` in the upper half-plane (so `−1/z ∈ ℍ` via `pnat_div_upper 1 z`, `z ∈ slitPlane`, `η z ≠ 0`).
- **Uses from project**: `csqrt` (csqrt.lean:22), `csqrt_differentiableAt` (csqrt.lean:46), `pnat_div_upper` (upperhalfplane.lean:13), `E₂_S_transform` (E2.lean:87), `E₂` (E2.lean:21)
- **Used by**: `eta_logderivs`
- **Visibility**: public
- **Lines**: 23–50, proof body ≈ 27 lines
- **Notes**: mathlib `ModularForm.logDeriv_eta_comp_eq_logDeriv_csqrt_eta (z : ℍ) : logDeriv (η ∘ (-1 / ·)) z = logDeriv (sqrt * η) z` (`Discriminant.lean:75`) is the same statement with `Complex.sqrt` in place of `csqrt`; mathlib's proof uses `deriv_sqrt` (`Analysis/Complex/SqrtDeriv.lean:54`) and inlines the `E2_slash_action S` computation. `change` at line 46 is needed because `E₂` is a `def` alias of `E2`. The `logDeriv_comp`/`logDeriv_mul` API is `Mathlib/Analysis/Calculus/LogDeriv.lean:111,54`; `Complex.logDeriv_exp` is `Trigonometric/Deriv.lean:746`.

### `lemma eta_logderivs`
- **Type**: `{z : ℂ | 0 < z.im}.EqOn (logDeriv (η ∘ (fun z : ℂ => -1/z))) (logDeriv ((csqrt) * η))`
- **What**: `Set.EqOn` packaging of `eta_logDeriv_eql` over `upperHalfPlaneSet`.
- **How**: `fun z hz ↦ eta_logDeriv_eql ⟨z, hz⟩`.
- **Hypotheses**: none
- **Uses from project**: `eta_logDeriv_eql`, `csqrt`
- **Used by**: `eta_logderivs_const`
- **Visibility**: public
- **Lines**: 52–54, proof body ≈ 1 line
- **Notes**: mathlib inlines this as `fun z hz ↦ logDeriv_eta_comp_eq_logDeriv_csqrt_eta ⟨z, hz⟩` (`Discriminant.lean:97`). The set is written `{z : ℂ | 0 < z.im}` rather than `upperHalfPlaneSet`.

### `lemma eta_logderivs_const`
- **Type**: `∃ z : ℂ, z ≠ 0 ∧ {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z))) (z • ((csqrt) * η))`
- **What**: Two nowhere-vanishing holomorphic functions on the connected open set ℍ with equal logarithmic derivatives differ by a nonzero constant.
- **How**: mathlib `logDeriv_eqOn_iff` (needs `DifferentiableOn` of both sides, `IsOpen`, `IsPreconnected` via `convex_halfSpace_im_gt`, and non-vanishing from `ModularForm.eta_ne_zero`/`Complex.exp_ne_zero`), applied to `eta_logderivs`.
- **Hypotheses**: none
- **Uses from project**: `eta_logderivs`, `csqrt`, `csqrt_differentiableAt`, `pnat_div_upper`
- **Used by**: `eta_equality`
- **Visibility**: public
- **Lines**: 56–70, proof body ≈ 13 lines
- **Notes**: mathlib `ModularForm.eta_comp_eqOn_const_mul_csqrt_eta : ∃ c : ℂ, c ≠ 0 ∧ upperHalfPlaneSet.EqOn (η ∘ (fun z ↦ -1 / z)) (c • (sqrt * η))` (`Discriminant.lean:94`), same proof via `logDeriv_eqOn_iff` (`Analysis/Calculus/LogDeriv.lean:116`).

### `lemma eta_equality`
- **Type**: `{z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z))) ((csqrt (Complex.I))⁻¹ • ((csqrt) * η))`
- **What**: The eta transformation law `η(−1/z) = (√i)⁻¹ √z η(z)`.
- **How**: Evaluate `eta_logderivs_const` at `z = i` (a fixed point of `S`), cancel `η(i) ≠ 0` with `mul_right_cancel₀`, and solve `c · csqrt i = 1` by `mul_eq_one_iff_eq_inv₀`.
- **Hypotheses**: none
- **Uses from project**: `eta_logderivs_const`, `csqrt`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 72–81, proof body ≈ 8 lines
- **Notes**: mathlib `ModularForm.eta_comp_eq_csqrt_I_inv : upperHalfPlaneSet.EqOn (η ∘ (-1 / ·)) ((sqrt I)⁻¹ • (sqrt * η))` (`Discriminant.lean:135`). Unused anywhere in the project (`Delta.lean` gets `Δ ∣[12] S = Δ` from mathlib's `discriminant_S_invariant` instead).

## File Summary
- Total declarations: 4 (0 defs, 4 lemmas, 0 instances, 0 other)
- Key API (used by 3+ others in the file): none
- Unused declarations (not used by anything in this file): `eta_equality` — and none of the four lemmas is used anywhere else in the project (verified with `grep -rnw` over `XYin`).
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: `eta_logDeriv_eql`, 27 lines)

## Observations (evidence for the analysis phases)
### Mathlib API candidates
- The entire file is a 1:1 image of mathlib's `Discriminant.lean` auxiliary section: `eta_logDeriv_eql` = `ModularForm.logDeriv_eta_comp_eq_logDeriv_csqrt_eta` (`.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Discriminant.lean:75`); `eta_logderivs_const` = `eta_comp_eqOn_const_mul_csqrt_eta` (line 94); `eta_equality` = `eta_comp_eq_csqrt_I_inv` (line 135). The only difference is `csqrt z := cexp ((1/2) * log z)` (project `csqrt.lean:22`) vs mathlib `Complex.sqrt z := z ^ (2⁻¹ : ℂ)` (`Mathlib/Analysis/RCLike/Sqrt.lean:26`), which agree for `z ≠ 0` by `sqrt_eq_exp : sqrt z = exp (log z / 2)` (`RCLike/Sqrt.lean:40`); they differ only at `0` (`csqrt 0 = 1`, `sqrt 0 = 0`), irrelevant on ℍ. Deleting this file (and `csqrt.lean`) in favour of mathlib unlocks `differentiableAt_sqrt`, `deriv_sqrt` (`Analysis/Complex/SqrtDeriv.lean:42,54`) and `csqrt_pow_24_eq`/`csqrt_I_pow_24` (`Discriminant.lean:58,63`).
- mathlib's `eta_ne_zero`, `differentiableAt_eta_of_mem_upperHalfPlaneSet`, `logDeriv_eta_eq_E2` (`DedekindEta.lean:117,151,169`) are already used here; the notation `η` is mathlib's `scoped[ModularForm] notation "η" => eta` (`DedekindEta.lean:63`).
- `pnat_div_upper 1 z` (project) is mathlib's `UpperHalfPlane.im_pnat_div_pos` (`Analysis/Complex/UpperHalfPlane/Basic.lean:180`), which mathlib uses at `Discriminant.lean:71`.
### Missing API / repeated patterns
- `{z : ℂ | 0 < z.im}` is spelled out 5× (lines 52, 56, 58, 60, 63, 72) instead of `upperHalfPlaneSet` (mathlib's name, with `isOpen_upperHalfPlaneSet` available); `isOpen_lt continuous_const Complex.continuous_im` (line 66) re-proves openness.
- `DifferentiableOn ℂ η {z | 0 < z.im}` (58–59) and `DifferentiableOn ℂ csqrt …` (63–64) are re-derived pointwise; a `DifferentiableOn`-level lemma for `η` (`ModularForm.differentiableOn_eta`?) does not exist in mathlib either (mathlib re-derives it at `Discriminant.lean:99`).
### Junk candidates
- The whole file (4 declarations, 81 lines): unused anywhere and duplicated by mathlib. Its only downstream role was to feed `Delta.lean`'s `S`-invariance, which now comes from `ModularForm.discriminant_S_invariant`.
- Stale comment lines 19–21 ("Lean 4.29+ no longer allows η as an identifier…").
- `open MeasureTheory intervalIntegral Metric …` (11–12) unused; `open scoped ArithmeticFunction.sigma` (16) unused.
- Imports `XYin.PhD.Modularforms.upperhalfplane` only for `pnat_div_upper` (= mathlib `im_pnat_div_pos`).
### Moral duplicates within this batch
- `eta_logderivs` vs `eta_logDeriv_eql` (pointwise vs `EqOn` form of the same fact).
- `Delta.lean:36–41` (`Delta_eq_eta_pow`, `delta_eq_discriminant`) reduces `Δ` to `η^24`, at which point every lemma here is subsumed by `discriminant_S_invariant`.
### Generalization notes
- None; the argument is specific to `η` on ℍ. (The connectedness/log-derivative principle itself is already general in mathlib's `logDeriv_eqOn_iff`.)
