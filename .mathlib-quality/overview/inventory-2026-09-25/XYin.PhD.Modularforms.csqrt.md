# Inventory: XYin/PhD/Modularforms/csqrt.lean  (57 lines)

A principal complex square root `csqrt z := exp (½ · log z)`, its derivative on ℍ, complex differentiability on ℍ, and `csqrt z ^ 24 = z ^ 12` (used for the Dedekind-eta transformation `η(−1/z) = √(−iz)·η(z)` in eta.lean, the only importer, which uses `csqrt` and `csqrt_differentiableAt`).

## Declarations

### `noncomputable def csqrt`
- **Type**: `ℂ → ℂ`
- **What**: `z ↦ exp (½ · log z)`, the principal square root (with `csqrt 0 = exp 0 = 1`, since `Complex.log 0 = 0`).
- **How**: `fun a => cexp ((1 / (2 : ℂ)) * log a)`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: csqrt_differentiableAt, csqrt_pow_24, csqrt_I; externally eta.lean:24–63
- **Visibility**: public
- **Lines**: 22
- **Notes**: **Mathlib**: `z ^ (1/2 : ℂ)` via `Complex.cpow` with `cpow_def_of_ne_zero : x ≠ 0 → x ^ y = exp (log x * y)` (`Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean:38`) agrees for `z ≠ 0` (up to `mul_comm`) but differs at `0` (`0 ^ (1/2) = 0`, `csqrt 0 = 1`). No `Complex.sqrt` def in mathlib (searched `def sqrt` in `SpecialFunctions/Complex/`, `Data/Complex/`). Defined with a redundant `(fun a : ℂ => …)` around the body.

### `lemma csqrt_deriv`
- **Type**: `(z : ℍ) : deriv (fun a : ℂ => cexp ((1 / (2 : ℂ))* (log a))) z = (2 : ℂ)⁻¹ • (fun a : ℂ => cexp (-(1 / (2 : ℂ)) * (log a))) z`
- **What**: `csqrt' (z) = ½ · exp(−½ log z) = ½ / csqrt z` on ℍ.
- **How**: Writes the function as `cexp ∘ (½·log)`, `deriv_comp` with `Complex.hasDerivAt_log` (`z ∈ slitPlane` since `Im z > 0`), `Complex.exp_neg`, `field_simp`, and the identity `exp(log z / 2)^2 = exp (log z)` via `Complex.exp_nat_mul` + `grind`, closing with `Complex.exp_log` and `mul_inv_cancel`.
- **Hypotheses**: `z ∈ ℍ` (coerced).
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 24–44, body ≈ 20 lines
- **Notes**: unused anywhere (eta.lean:30 recomputes `logDeriv csqrt z = (2:ℂ)⁻¹ * z⁻¹` itself). Statement does not mention `csqrt` (spelled out as the lambda) and the RHS is an odd `(2:ℂ)⁻¹ • (fun …) z`. Non-terminal `simp` at L35; `grind` at L39. Mathlib: `deriv_cpow_const` (`Pow/Deriv.lean:318`: `deriv (fun x => f x ^ c) x = c * f x ^ (c - 1) * deriv f x` for `f x ∈ slitPlane`) gives `deriv (· ^ (1/2)) z = ½ · z^(−½)` directly.

### `lemma csqrt_differentiableAt`
- **Type**: `(z : ℍ) : DifferentiableAt ℂ csqrt z`
- **What**: `csqrt` is complex-differentiable at every point of ℍ.
- **How**: `(Complex.differentiableAt_log (Or.inr z.im_pos.ne')).const_mul _ |>.cexp`.
- **Hypotheses**: `z ∈ ℍ`.
- **Uses from project**: csqrt
- **Used by**: unused in file; externally eta.lean:40
- **Visibility**: public
- **Lines**: 46–47, body 1 line
- **Notes**: mathlib: `DifferentiableAt.cpow_const` (`Pow/Deriv.lean:116`) / `differentiableAt_id.cpow_const` for the `cpow` spelling.

### `lemma csqrt_pow_24`
- **Type**: `(z : ℂ) (hz : z ≠ 0) : (csqrt z) ^ 24 = z ^ 12`
- **What**: The 24th power of the square root is the 12th power.
- **How**: `← Complex.exp_nat_mul`, `24 · (½ log z) = 12 · log z` by `norm_num; ring`, `Complex.exp_nat_mul`, `Complex.exp_log hz`.
- **Hypotheses**: `z ≠ 0`.
- **Uses from project**: csqrt
- **Used by**: csqrt_I
- **Visibility**: public
- **Lines**: 49–52, body 3 lines
- **Notes**: unused outside file. Mathlib: `Complex.cpow_nat_inv_pow : (x ^ (n⁻¹ : ℂ)) ^ n = x` (`Pow/Complex.lean:137`) / `cpow_ofNat_inv_pow` (:142, `@[simp]`) plus `pow_mul` give `(z^(1/2))^24 = ((z^(1/2))^2)^12 = z^12` with no nonvanishing hypothesis.

### `lemma csqrt_I`
- **Type**: `(csqrt (Complex.I)) ^ 24 = 1`
- **What**: `√i` is a 24th root of unity.
- **How**: `csqrt_pow_24` with `Complex.I_ne_zero`, `Complex.I_pow_eq_pow_mod`, `norm_num`.
- **Hypotheses**: none.
- **Uses from project**: csqrt, csqrt_pow_24
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 54–57, body 3 lines
- **Notes**: unused anywhere.

## File Summary
- Total declarations: 5 (1 def; 4 lemmas; 0 instances; 0 other)
- Key API (used by 3+ others in the file): csqrt (3)
- Unused declarations (not used by anything in this file): csqrt_deriv, csqrt_differentiableAt (ext. eta.lean), csqrt_I
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: csqrt_deriv, 20 lines)

## Observations

### Mathlib API candidates
- `csqrt` (L22) ≈ `fun z => z ^ (1/2 : ℂ)` (`Complex.cpow`, `Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean`, `cpow_def_of_ne_zero` :38) — equal on `ℂ \ {0}` (which is all that eta.lean uses, since it works on ℍ). Switching unlocks: `csqrt_differentiableAt` → `DifferentiableAt.cpow_const` (`Pow/Deriv.lean:116`); `csqrt_deriv` → `deriv_cpow_const` (`Pow/Deriv.lean:318`) / `HasDerivAt.cpow_const` (:218); `csqrt_pow_24` → `cpow_ofNat_inv_pow` (:142, simp) + `pow_mul`; `csqrt_I` → `Complex.I_pow_eq_pow_mod`. Mathlib's own `DedekindEta.lean` has no square root yet (its `η` results stop at `logDeriv_eta_eq_E2`, :169), so the project's eta S-transformation is not upstream — but its square root should still be `cpow`.
- Hand-rolled pattern: `csqrt_deriv` computes the chain rule manually (`deriv_comp`, `field_simp`, `grind`) where `HasDerivAt.cpow_const`/`deriv_cpow_const` is a one-liner.

### Missing API / repeated patterns
- `csqrt_deriv` is stated for the lambda, not for `csqrt`; the useful form (`HasDerivAt csqrt (½ / csqrt z) z`, or `logDeriv csqrt z = ½ · z⁻¹` as eta.lean:30 needs) is missing, so eta.lean re-derives it.
- No `csqrt_sq : z ≠ 0 → csqrt z ^ 2 = z`, `csqrt_ne_zero`, `csqrt_mul`… companions; `csqrt_pow_24` is the only algebraic lemma and it is specialised to 24/12 (eta's exponent).

### Junk candidates
- `csqrt_deriv` (L24): unused anywhere, duplicated by eta.lean:30's inline computation.
- `csqrt_I` (L54): unused anywhere.
- Stray imports L3–4, L7–10 (`NatPowAssoc`, `CStarAlgebra.Classes`, `ArithmeticFunction.Defs/Moebius`, `ModularForms.Basic`, `EisensteinSeries.Defs`) and `open ArithmeticFunction` (L19): nothing arithmetic-function-related is used.

### Moral duplicates within this batch
- `csqrt_deriv` (L24) vs eta.lean:30 `hlog : logDeriv csqrt z = (2 : ℂ)⁻¹ * (z : ℂ)⁻¹` (same derivative computed twice, different spellings).
- `csqrt_differentiableAt` (L46) is the `DifferentiableAt` shadow of what `csqrt_deriv` proves via `deriv_comp` (L42–44 re-prove the same differentiability inline).

### Generalization notes
- `csqrt_pow_24` holds for `n·½ = m` in general: `(csqrt z)^(2m) = z^m` for `z ≠ 0`; 24/12 is an eta-specific instance.
- `csqrt_deriv`/`csqrt_differentiableAt` hold on the whole slit plane `Complex.slitPlane`, not just ℍ (the proofs only use `z ∈ slitPlane` via `Or.inr z.im_pos.ne'`).
