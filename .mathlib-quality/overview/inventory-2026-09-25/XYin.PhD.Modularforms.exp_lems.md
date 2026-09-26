# Inventory: XYin/PhD/Modularforms/exp_lems.lean  (29 lines)

Three small facts about `exp(2πi·z)` on ℍ: `‖q‖ < 1`, `‖q^{n+1}‖ < 1`, and 1-periodicity of `exp(2πi n z)`. Imported by `tsumderivWithin.lean` and `Summability/Basic.lean`; `exp_upperHalfPlane_lt_one` is used in 4 files (Eisenstein, tsumderivWithin, Summability/Basic ×4, multipliable_lems via `_nat`), `exp_periodo` nowhere.

## Declarations

### `theorem exp_upperHalfPlane_lt_one`
- **Type**: `(z : ℍ) : ‖(Complex.exp (2 * ↑π * Complex.I * z))‖ < 1`
- **What**: The nome `q = e^{2πiz}` has modulus `< 1` for `z ∈ ℍ`.
- **How**: `UpperHalfPlane.norm_exp_two_pi_I_lt_one z`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file; externally Eisenstein.lean:567, tsumderivWithin.lean:113, Summability/Basic.lean:142/155/160/182
- **Visibility**: public
- **Lines**: 14–16, body 1 line
- **Notes**: **pure alias** of mathlib `UpperHalfPlane.norm_exp_two_pi_I_lt_one` (`Mathlib/Analysis/Complex/UpperHalfPlane/Exp.lean:43`) — identical statement; the 6 call sites can use the mathlib name directly.

### `theorem exp_upperHalfPlane_lt_one_nat`
- **Type**: `(z : ℍ) (n : ℕ) : ‖(Complex.exp (2 * ↑π * Complex.I * (n+1) * z))‖ < 1`
- **What**: `‖q^{n+1}‖ < 1`, i.e. `‖exp(2πi(n+1)z)‖ < 1`.
- **How**: `Complex.norm_exp`, compute the real part of `2πi(n+1)z` as `−2π(n+1)·Im z` with the `re`/`im` simp set, `Real.exp_lt_one_iff`, `positivity`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file; externally multipliable_lems.lean:22, Summability/Basic.lean:110/188
- **Visibility**: public
- **Lines**: 18–23, body ≈ 4 lines
- **Notes**: long explicit simp list (L20–22) is what `simp [Complex.norm_exp]` + `positivity` would do. No exact mathlib analogue (searched `norm_exp_two_pi_I_nat`, `exp_two_pi_I_nat_lt_one`, `Exp.lean`); composable as `norm_exp_two_pi_I_lt_one ((⟨n+1, _⟩ : {x : ℝ // 0 < x}) • z)` using `UpperHalfPlane.posRealAction`/`coe_pos_real_smul` (`UpperHalfPlane/Basic.lean:197/205`), or from `norm_pow` + `pow_lt_one₀` applied to the previous lemma after rewriting `exp(2πi(n+1)z) = exp(2πiz)^(n+1)` (`Complex.exp_nat_mul`; mathlib `eta_q_eq_pow`, `DedekindEta.lean:50`, is exactly this rewrite).

### `lemma exp_periodo`
- **Type**: `(z : ℍ) (n : ℕ) : cexp (2 * ↑π * Complex.I * ↑↑n * (1 + ↑z)) = cexp (2 * ↑π * Complex.I * ↑↑n * ↑z)`
- **What**: `exp(2πi n z)` is invariant under `z ↦ z + 1`.
- **How**: `Complex.exp_periodic.nat_mul n` (`Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean:1201`) + `ring` for the exponent.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 25–29, body 3 lines
- **Notes**: unused anywhere; `z : ℍ` is irrelevant (holds for all `z : ℂ`); double coercion `↑↑n`; misspelt name (`periodo`).

## File Summary
- Total declarations: 3 (0 defs; 3 lemmas; 0 instances; 0 other)
- Key API (used by 3+ others in the file): none
- Unused declarations (not used by anything in this file): all three (in-file); project-wide `exp_periodo` is unused
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations

### Mathlib API candidates
- `exp_upperHalfPlane_lt_one` (L14) = `UpperHalfPlane.norm_exp_two_pi_I_lt_one` (`Mathlib/Analysis/Complex/UpperHalfPlane/Exp.lean:43`), verbatim alias; replace at the 6 call sites and delete.
- `exp_upperHalfPlane_lt_one_nat` (L18): derive from the above via `UpperHalfPlane.posRealAction` (`Basic.lean:197`) or `Complex.exp_nat_mul` + `pow_lt_one₀`; mathlib's `UpperHalfPlane.norm_qParam_lt_one` (`Exp.lean:38`) is the `q^{1/n}` direction, not this one.
- `exp_periodo` (L25) = `Complex.exp_periodic.nat_mul n _` up to `ring` (`Trigonometric/Basic.lean:1201`); also `Function.Periodic.qParam`-style lemmas in `Mathlib/Analysis/Complex/Periodic.lean`.

### Missing API / repeated patterns
- The two callers `Summability/Basic.lean:110/188` and `multipliable_lems.lean:22` want `‖q^(n+1)‖ < 1` in the form `‖cexp(2πi z)‖^(n+1) < 1`; a lemma stated as `‖cexp (2πi z) ^ (n+1)‖ < 1` (or simply `pow_lt_one₀` on the base) would match them without the `simpa` reshaping.

### Junk candidates
- `exp_upperHalfPlane_lt_one` (L14): alias — delete after renaming call sites.
- `exp_periodo` (L25): unused anywhere.
- `open scoped … NNReal ENNReal BigOperators Nat` (L12) and `open … Metric Filter Function` (L9–10): nothing from these is used.

### Moral duplicates within this batch
- `exp_upperHalfPlane_lt_one_nat` is `exp_upperHalfPlane_lt_one` at the scaled point `(n+1)·z`.

### Generalization notes
- `exp_periodo` holds for all `z : ℂ` and all `n : ℤ` (`Complex.exp_periodic.int_mul`); restricting to `z : ℍ`, `n : ℕ` is gratuitous.
- `exp_upperHalfPlane_lt_one_nat` holds for any real `c > 0` in place of `n+1` (`exp(2πi c z)`), the proof only uses `0 < (n+1) · Im z`.
