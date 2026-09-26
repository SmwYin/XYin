# Inventory: XYin/PhD/Modularforms/E2.lean  (109 lines)

Compatibility shim over mathlib's weight-2 quasi-modular Eisenstein series: defines `G₂ := EisensteinSeries.G2`, `E₂ := EisensteinSeries.E2`, `D₂ := EisensteinSeries.D2` and re-exports mathlib's `D2_*`, `G2_*`, `E2_slash_action` lemmas under project names, then derives the pointwise forms `E₂(z+1) = E₂(z)`, `E₂(−1/z) = z²(E₂(z) + 6/(πiz))` and the Lambert-series form `E₂ = 1 − 24 Σ n qⁿ/(1−qⁿ)`. Only `E₂`, `E₂_S_transform` and `E₂_eq` are used elsewhere (by `eta.lean` and `Eisenstein.lean`).

## Declarations

### `def G₂`
- **Type**: `ℍ → ℂ`
- **What**: The unnormalised weight-2 Eisenstein series `G₂(z) = Σ_m Σ_n (mz+n)^{−2}` (Eisenstein summation).
- **How**: Alias `EisensteinSeries.G2`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `G2_q_exp`, `G2_periodic`, `G₂_transform`
- **Visibility**: public
- **Lines**: 18, proof body ≈ 0 lines
- **Notes**: Docstring says "Compatibility alias". mathlib: `EisensteinSeries.G2` (`Mathlib/NumberTheory/ModularForms/EisensteinSeries/E2/Defs.lean:56`). Unused outside this file.

### `def E₂`
- **Type**: `ℍ → ℂ`
- **What**: The normalised quasi-modular `E₂ = G₂ / (2ζ(2))`.
- **How**: Alias `EisensteinSeries.E2`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `E₂_periodic`, `E₂_transform`, `E₂_slash_transform`, `E₂_S_transform`, `E₂_eq`
- **Visibility**: public
- **Lines**: 21, proof body ≈ 0 lines
- **Notes**: mathlib: `EisensteinSeries.E2` (`E2/Defs.lean:60`). Externally used by `eta.lean` (via `E₂_S_transform`) and `Eisenstein.lean` (`φ₀`, `φ₂'`, `E₂_imag_axis_real`, `E₂_isBoundedAtImInfty`, `E₂_mul_E₄_isBoundedAtImInfty`). Since it is a `def` (not `abbrev`), mathlib's `logDeriv_eta_eq_E2` (stated with `E2`) needs a `change` to match (`eta.lean:46`).

### `def D₂`
- **Type**: `SL(2, ℤ) → ℍ → ℂ`
- **What**: The weight-2 cocycle defect `D₂(γ)(z) = 2πi c / (cz+d)` appearing in the E₂ transformation law.
- **How**: Alias `EisensteinSeries.D2 γ`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `D₂_apply`, `D2_one`, `D2_mul`, `D2_inv`, `D2_T`, `D2_S`, `G₂_transform`, `E₂_slash_transform`
- **Visibility**: public
- **Lines**: 24, proof body ≈ 0 lines
- **Notes**: mathlib: `EisensteinSeries.D2` (`E2/Defs.lean:63`). Unused outside this file.

### `lemma D₂_apply`
- **Type**: `(γ : SL(2, ℤ)) (z : ℍ) : D₂ γ z = (2 * π * I * γ 1 0) / (γ 1 0 * z + γ 1 1)`
- **What**: Unfolds `D₂` to the explicit formula.
- **How**: `rfl` (mathlib's `D2` is `2πi c / denom γ z` and `denom` unfolds definitionally).
- **Hypotheses**: none
- **Uses from project**: `D₂`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 26–28, proof body ≈ 1 line
- **Notes**: Unused anywhere.

### `lemma D2_one`
- **Type**: `D₂ 1 = 0`
- **What**: The defect of the identity is zero.
- **How**: `ext; simp [D₂]` (mathlib `EisensteinSeries.D2_one`).
- **Hypotheses**: none
- **Uses from project**: `D₂`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 30–32, proof body ≈ 2 lines
- **Notes**: Wrapper of `EisensteinSeries.D2_one` (`E2/Defs.lean:66`). Unused anywhere.

### `lemma D2_mul`
- **Type**: `(A B : SL(2, ℤ)) : D₂ (A * B) = ((D₂ A) ∣[(2 : ℤ)] B) + (D₂ B)`
- **What**: `D₂` is a weight-2 cocycle.
- **How**: `simpa [D₂] using EisensteinSeries.D2_mul A B`.
- **Hypotheses**: none
- **Uses from project**: `D₂`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 34–35, proof body ≈ 1 line
- **Notes**: Wrapper of `EisensteinSeries.D2_mul` (`E2/Defs.lean:78`). Unused anywhere.

### `lemma D2_inv`
- **Type**: `(A : SL(2, ℤ)) : (D₂ A) ∣[(2 : ℤ)] A⁻¹ = -D₂ (A⁻¹)`
- **What**: Cocycle identity for inverses.
- **How**: Wrapper of `EisensteinSeries.D2_inv`.
- **Hypotheses**: none
- **Uses from project**: `D₂`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 37–38, proof body ≈ 1 line
- **Notes**: mathlib `E2/Defs.lean:94`. Unused anywhere.

### `lemma D2_T`
- **Type**: `D₂ ModularGroup.T = 0`
- **What**: No defect for translation.
- **How**: Wrapper of `EisensteinSeries.D2_T`.
- **Hypotheses**: none
- **Uses from project**: `D₂`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 40–41, proof body ≈ 1 line
- **Notes**: mathlib `E2/Defs.lean:97`. Unused anywhere (note `E₂_periodic` uses mathlib's `EisensteinSeries.D2_T` directly, not this).

### `lemma D2_S`
- **Type**: `(z : ℍ) : D₂ ModularGroup.S z = 2 * π * I / z`
- **What**: The defect for `S` is `2πi/z`.
- **How**: Term-mode `EisensteinSeries.D2_S z`.
- **Hypotheses**: none
- **Uses from project**: `D₂`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 43–44, proof body ≈ 1 line
- **Notes**: mathlib `E2/Defs.lean:101`. Unused anywhere (`E₂_transform` uses mathlib's directly).

### `lemma G2_q_exp`
- **Type**: `(z : ℍ) : G₂ z = 2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : ℕ+, sigma 1 n * cexp (2 * π * I * n * z)`
- **What**: q-expansion of `G₂`.
- **How**: `simpa [G₂, ← Complex.exp_nat_mul, mul_assoc, …] using EisensteinSeries.G2_eq_tsum_cexp z` (converting `q^n` to `exp(2πi n z)`).
- **Hypotheses**: none
- **Uses from project**: `G₂`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 46–49, proof body ≈ 2 lines
- **Notes**: mathlib `G2_eq_tsum_cexp` (`E2/Summable.lean:97`). Unused anywhere.

### `lemma G2_periodic`
- **Type**: `(G₂ ∣[(2 : ℤ)] ModularGroup.T) = G₂`
- **What**: `G₂` is `T`-invariant.
- **How**: Wrapper of `EisensteinSeries.G2_T_transform`.
- **Hypotheses**: none
- **Uses from project**: `G₂`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 51–52, proof body ≈ 1 line
- **Notes**: mathlib `E2/Transform.lean:192`. Unused anywhere.

### `lemma G₂_transform`
- **Type**: `(γ : SL(2, ℤ)) : (G₂ ∣[(2 : ℤ)] γ) = G₂ - (D₂ γ)`
- **What**: Full transformation law of `G₂`.
- **How**: Wrapper of `EisensteinSeries.G2_slash_action`.
- **Hypotheses**: none
- **Uses from project**: `G₂`, `D₂`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 54–55, proof body ≈ 1 line
- **Notes**: mathlib `E2/Transform.lean:198`. Unused anywhere.

### `lemma E₂_periodic`
- **Type**: `(z : ℍ) : E₂ ((1 : ℝ) +ᵥ z) = E₂ z`
- **What**: `E₂` is 1-periodic.
- **How**: Evaluate `EisensteinSeries.E2_slash_action ModularGroup.T` at `z`, rewrite with project `modular_slash_T_apply`, and kill `D2_T`.
- **Hypotheses**: none
- **Uses from project**: `E₂`, `modular_slash_T_apply` (SlashActionAuxil.lean:58)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 58–61, proof body ≈ 3 lines
- **Notes**: Unused anywhere. Same skeleton as `E₄_periodic`/`E₆_periodic`/`Δ_periodic` in the batch (those use `SlashInvariantForm.vAdd_width_periodic`, `Identities.lean:37`).

### `lemma E₂_transform`
- **Type**: `(z : ℍ) : (E₂ ∣[(2 : ℤ)] ModularGroup.S) z = E₂ z + 6 / (π * I * z)`
- **What**: Pointwise `S`-slash transformation of `E₂` with `1/(2ζ(2))·2πi/z` evaluated to `6/(πiz)`.
- **How**: `E2_slash_action S` + `D2_S` + `riemannZeta_two` (`π²/6`), then `field_simp`/`ring_nf`/`I_sq`.
- **Hypotheses**: none
- **Uses from project**: `E₂`
- **Used by**: `E₂_S_transform`
- **Visibility**: public
- **Lines**: 63–79, proof body ≈ 16 lines
- **Notes**: `riemannZeta_two` is `Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean:214`. mathlib performs the identical inline computation in `logDeriv_eta_comp_eq_logDeriv_csqrt_eta` (`Discriminant.lean:81–86`) but has no standalone lemma.

### `lemma E₂_slash_transform`
- **Type**: `(γ : SL(2, ℤ)) : (E₂ ∣[(2 : ℤ)] γ) = E₂ - (1 / (2 * riemannZeta 2)) • D₂ γ`
- **What**: Full `SL(2,ℤ)` transformation law of `E₂`.
- **How**: Wrapper of `EisensteinSeries.E2_slash_action`.
- **Hypotheses**: none
- **Uses from project**: `E₂`, `D₂`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 82–84, proof body ≈ 1 line
- **Notes**: mathlib `E2/Transform.lean:224`. Unused anywhere.

### `lemma E₂_S_transform`
- **Type**: `(z : ℍ) : E₂ (ModularGroup.S • z) = z ^ 2 * (E₂ z + 6 / (π * I * z))`
- **What**: The classical `E₂(−1/z) = z² E₂(z) + 6z/(πi)`.
- **How**: From `E₂_transform` via `SL_slash_apply`, `ModularGroup.denom_S`, `zpow_neg`, and `mul_inv_eq_iff_eq_mul₀`.
- **Hypotheses**: none
- **Uses from project**: `E₂`, `E₂_transform`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 87–91, proof body ≈ 3 lines
- **Notes**: Externally used by `eta.lean:35`. Same skeleton as `E₄_S_transform`, `E₆_S_transform` (`Eisenstein.lean:79–100`) and `Δ_S_transform` (`Delta.lean:69–73`).

### `lemma tsum_eq_tsum_sigma`
- **Type**: `(z : ℍ) : ∑' n : ℕ, (n + 1) * cexp (2πi (n+1) z) / (1 - cexp (2πi (n+1) z)) = ∑' n : ℕ, sigma 1 (n + 1) * cexp (2πi (n+1) z)`
- **What**: Lambert-series identity `Σ n qⁿ/(1−qⁿ) = Σ σ₁(n) qⁿ`, indexed by `ℕ` with shift.
- **How**: mathlib `tsum_pow_div_one_sub_eq_tsum_sigma` with `k = 1` and `‖q‖ < 1` from `norm_exp_two_pi_I_lt_one`, re-indexed by `tsum_pnat_eq_tsum_succ` twice.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 93–102, proof body ≈ 8 lines
- **Notes**: Unused anywhere. mathlib `tsum_pow_div_one_sub_eq_tsum_sigma` (`Mathlib/NumberTheory/TsumDivisorsAntidiagonal.lean:119`) already gives the `ℕ+`-indexed form; the shift to `ℕ` is `tsum_pnat_eq_tsum_succ` (`InfiniteSum/NatInt.lean:545`, to_additive).

### `lemma E₂_eq`
- **Type**: `(z : ℍ) : E₂ z = 1 - 24 * ∑' n : ℕ+, n * cexp (2πi n z) / (1 - cexp (2πi n z))`
- **What**: Lambert-series form of `E₂`.
- **How**: `E2_eq_tsum_cexp` (σ-form) rewritten backwards with `tsum_pow_div_one_sub_eq_tsum_sigma`, then `exp_nat_mul` normalisation.
- **Hypotheses**: none
- **Uses from project**: `E₂`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 104–109, proof body ≈ 4 lines
- **Notes**: Externally used by `Eisenstein.lean` (`E₂_imag_axis_real:545`, `E₂_isBoundedAtImInfty:665`). mathlib `E2_eq_tsum_cexp` (`E2/Summable.lean:102`) is the σ-form; no Lambert-form lemma in mathlib (searched `E2_eq`, `E2.*one_sub` in `EisensteinSeries/E2/`).

## File Summary
- Total declarations: 18 (3 defs, 15 lemmas, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `E₂` (5), `D₂` (8), `G₂` (3)
- Unused declarations (not used by anything in this file): `D₂_apply`, `D2_one`, `D2_mul`, `D2_inv`, `D2_T`, `D2_S`, `G2_q_exp`, `G2_periodic`, `G₂_transform`, `E₂_periodic`, `E₂_slash_transform`, `E₂_S_transform` (used externally by `eta.lean`), `tsum_eq_tsum_sigma`, `E₂_eq` (used externally by `Eisenstein.lean`). All except `E₂`, `E₂_S_transform`, `E₂_eq` are unused anywhere in the project.
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: `E₂_transform`, 16 lines)

## Observations (evidence for the analysis phases)
### Mathlib API candidates
- Everything in lines 17–55 and 82–84 is a rename of mathlib: `G₂`/`E₂`/`D₂` = `EisensteinSeries.G2/E2/D2` (`Mathlib/NumberTheory/ModularForms/EisensteinSeries/E2/Defs.lean:56,60,63`); `D2_one/mul/inv/T/S` = `EisensteinSeries.D2_one/D2_mul/D2_inv/D2_T/D2_S` (`Defs.lean:66,78,94,97,101`); `G2_q_exp` = `G2_eq_tsum_cexp` (`E2/Summable.lean:97`); `G2_periodic` = `G2_T_transform` (`E2/Transform.lean:192`); `G₂_transform` = `G2_slash_action` (198); `E₂_slash_transform` = `E2_slash_action` (224). Replacing `def E₂ := EisensteinSeries.E2` by `abbrev` (or `open EisensteinSeries` + notation) would let mathlib's `logDeriv_eta_eq_E2` (`DedekindEta.lean:169`), `E2_mdifferentiable` (`E2/MDifferentiable.lean:27`) apply without `change` (cf. `eta.lean:46`).
- `E₂_eq` uses `E2_eq_tsum_cexp` (`E2/Summable.lean:102`) + `tsum_pow_div_one_sub_eq_tsum_sigma` (`TsumDivisorsAntidiagonal.lean:119`); no mathlib Lambert form of `E2` exists, so `E₂_eq` is a legitimate small addition.
- `E₂_S_transform`/`E₂_transform`: no standalone mathlib lemma; mathlib inlines the same `riemannZeta_two`/`field_simp` computation at `Discriminant.lean:81–86`. Candidate upstream lemma `EisensteinSeries.E2_S_smul (z) : E2 (S • z) = z^2 * (E2 z + 6/(π I z))`.
### Missing API / repeated patterns
- The "evaluate slash action at `S` and clear `denom_S`" fragment (`rw [SL_slash_apply, ModularGroup.denom_S, zpow_neg…] at h; … mul_inv_eq_iff_eq_mul₀`) appears at `E2.lean:90–91`, `Eisenstein.lean:85–88, 97–100`, `Delta.lean:71–73`. A lemma `SlashInvariantForm.S_smul_apply (f : SlashInvariantForm ↑Γ(1) k) (z) : f (S • z) = z ^ k * f z` (or a `ℍ → ℂ` version with hypothesis `f ∣[k] S = f`) would collapse all four.
- Per the `open Complex` at line 9 and `open ArithmeticFunction` at line 10, `sigma 1 n` and `σ 1 n` are both used (line 47 vs `Eisenstein.lean`); pick one.
### Junk candidates
- Dead wrappers (unused anywhere): `D₂_apply`, `D2_one`, `D2_mul`, `D2_inv`, `D2_T`, `D2_S`, `G2_q_exp`, `G2_periodic`, `G₂_transform`, `E₂_periodic`, `E₂_slash_transform`, `tsum_eq_tsum_sigma` (12 of 18 declarations, lines 26–55, 58–61, 82–84, 93–102).
- Mixed naming: `D2_one` vs `D₂_apply`, `G2_q_exp` vs `G₂_transform`.
- `open MeasureTheory intervalIntegral Metric …` (line 8–9) — none used.
### Moral duplicates within this batch
- `E₂_transform` (63–79) and `E₂_S_transform` (87–91) are two forms of the same fact; only the second is used.
- `tsum_eq_tsum_sigma` (93–102) and the inner rewrite of `E₂_eq` (107–109) both apply `tsum_pow_div_one_sub_eq_tsum_sigma … 1`.
### Generalization notes
- None applicable: everything is specific to `ℍ → ℂ` and `SL(2,ℤ)`.
