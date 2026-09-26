# Inventory: XYin/PhD/Modularforms/clog_arg_lems.lean  (94 lines)

Lemmas about `Complex.arg` and `Complex.log` of powers `(1 + f x)^n` when `f → 0`: `arg (x^n) = n·arg x` under a smallness hypothesis on `arg x`, its eventual version along any filter, specialisations to `atTop` on ℕ and `atImInfty` on ℍ, the corresponding `log ((1+f)^n) = n·log (1+f)` eventually, and summability of `log ((1+f n)^m)` for summable `f`. **Entirely dead code**: imported only by Delta.lean (and `XYin.lean`), which references none of these names.

## Declarations

### `lemma arg_pow_aux`
- **Type**: `(n : ℕ) (x : ℂ) (hx : x ≠ 0) (hna : |arg x| < π / n) : Complex.arg (x ^ n) = n * Complex.arg x`
- **What**: If `|arg x| < π/n` then the argument of `x^n` is exactly `n·arg x` (no wrap-around).
- **How**: Induction on `n`; the step uses mathlib `Complex.arg_mul` (needs `arg x + arg (x^n) ∈ Ioc (-π) π`, `Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean`), the inductive formula `arg (x^n) = n·arg x`, and the bound `|arg x| < π/(n+1) < π/n` unpacked with `abs_lt`, `div_lt_iff₀'`, `lt_div_iff₀'`.
- **Hypotheses**: `x ≠ 0`, `|arg x| < π/n` (for `n = 0` the RHS is `π/0 = 0`, so the hypothesis is `|arg x| < 0`, vacuous — the base case is fine).
- **Uses from project**: []
- **Used by**: eventually_arg_pow
- **Visibility**: public
- **Lines**: 18–51, body ≈ 33 lines
- **Notes**: **proof > 30 lines**; goal order after `rw [pow_succ, arg_mul, hn2, Nat.cast_add]` is handled positionally (L26–51) and the side goals are discharged in a confusing order; `norm_cast; omega` twice. Mathlib has the `Real.Angle`-valued `Complex.arg_pow_coe_angle` (`Arg.lean:502`) with no side condition, and `Complex.cpow_nat_mul'` (`Pow/Complex.lean:159`) whose hypotheses `-π < n * x.arg ∧ n * x.arg ≤ π` are exactly the form needed here; no mathlib lemma states `arg (x^n) = n * arg x` under `|arg x| < π/n` (searched `arg_pow`, `arg_nat_pow`, `arg_natCast_mul`, `natCast_mul_arg` in `Arg.lean`, `Pow/Complex.lean`, `Log.lean`).

### `lemma one_add_abs_half_ne_zero`
- **Type**: `{x : ℂ} (hb : ‖x‖ < 1 / 2) : 1 + x ≠ 0`
- **What**: `1 + x ≠ 0` when `‖x‖ < 1/2`.
- **How**: If `1 + x = 0` then `x = -1` (`add_eq_zero_iff_eq_neg`), contradicting `‖-1‖ = 1 < 1/2` by `norm_num`.
- **Hypotheses**: `‖x‖ < 1/2`.
- **Uses from project**: []
- **Used by**: eventually_arg_pow
- **Visibility**: public
- **Lines**: 53–56, body 3 lines
- **Notes**: the natural hypothesis is `‖x‖ < 1`; `1/2` is an artefact of the caller. No direct mathlib lemma (searched `one_add_ne_zero`, `isUnit_one_add`, `ne_zero_of_norm_lt`; mathlib has `Complex.one_add_coe_ne_zero` only for the unit disc `𝔻`, `Mathlib/Analysis/Complex/UnitDisc/Basic.lean:86`).

### `private lemma eventually_arg_pow`
- **Type**: `{α : Type*} {l : Filter α} (n : ℕ) (f : α → ℂ) (hf : Tendsto f l (𝓝 0)) : ∀ᶠ x in l, arg ((1 + f x) ^ n) = n * arg (1 + f x)`
- **What**: Along any filter where `f → 0`, eventually `arg ((1+f)^n) = n·arg (1+f)`.
- **How**: `arg (1 + f x) → 0` by continuity of `arg` at `1` (`Complex.continuousAt_arg Complex.one_mem_slitPlane`, `Arg.lean:579`); eventually `|arg (1+f x)| < π/n` and `‖f x‖ < 1/2` (`tendsto_order`), then `arg_pow_aux` with `one_add_abs_half_ne_zero`.
- **Hypotheses**: `f → 0` along `l`.
- **Uses from project**: arg_pow_aux, one_add_abs_half_ne_zero
- **Used by**: arg_pow, arg_pow2
- **Visibility**: private
- **Lines**: 58–69, body ≈ 10 lines
- **Notes**: the genuinely general statement — it should be the public one; the two public specialisations below are its instances.

### `lemma arg_pow`
- **Type**: `(n : ℕ) (f : ℕ → ℂ) (hf : Tendsto f atTop (𝓝 0)) : ∀ᶠ m : ℕ in atTop, Complex.arg ((1 + f m) ^ n) = n * Complex.arg (1 + f m)`
- **What**: `eventually_arg_pow` for sequences.
- **How**: `exact eventually_arg_pow n f hf`.
- **Hypotheses**: `f → 0`.
- **Uses from project**: eventually_arg_pow
- **Used by**: clog_pow
- **Visibility**: public
- **Lines**: 71–73, body 1 line
- **Notes**: pure specialisation.

### `lemma arg_pow2`
- **Type**: `(n : ℕ) (f : ℍ → ℂ) (hf : Tendsto f atImInfty (𝓝 0)) : ∀ᶠ m : ℍ in atImInfty, Complex.arg ((1 + f m) ^ n) = n * Complex.arg (1 + f m)`
- **What**: `eventually_arg_pow` at `i∞`.
- **How**: `exact eventually_arg_pow n f hf`.
- **Hypotheses**: `f → 0` at `i∞`.
- **Uses from project**: eventually_arg_pow
- **Used by**: clog_pow2
- **Visibility**: public
- **Lines**: 75–77, body 1 line
- **Notes**: pure specialisation; name suffix `2` is uninformative.

### `lemma clog_pow`
- **Type**: `(n : ℕ) (f : ℕ → ℂ) (hf : Tendsto f atTop (𝓝 0)) : ∀ᶠ m : ℕ in atTop, Complex.log ((1 + f m) ^ n) = n * Complex.log (1 + f m)`
- **What**: Eventually `log ((1+f m)^n) = n·log (1+f m)`.
- **How**: Unfold `Complex.log = ↑(Real.log ‖·‖) + arg·I`; `norm_pow`, `Real.log_pow`, and `arg_pow` for the argument; `ring`.
- **Hypotheses**: `f → 0`.
- **Uses from project**: arg_pow
- **Used by**: log_summable_pow
- **Visibility**: public
- **Lines**: 79–83, body 3 lines
- **Notes**: no mathlib `Complex.log_pow` under an `arg` side condition (searched `log_pow`, `log_nat_mul`, `natCast_mul_log` in `Log.lean`, `Pow/Complex.lean`); the closest is `Complex.cpow_nat_mul'` (`Pow/Complex.lean:159`).

### `lemma clog_pow2`
- **Type**: `(n : ℕ) (f : ℍ → ℂ) (hf : Tendsto f atImInfty (𝓝 0)) : ∀ᶠ m : ℍ in atImInfty, Complex.log ((1 + f m) ^ n) = n * Complex.log (1 + f m)`
- **What**: Same at `i∞`.
- **How**: verbatim copy of `clog_pow`'s 3-line proof with `arg_pow2`.
- **Hypotheses**: `f → 0` at `i∞`.
- **Uses from project**: arg_pow2
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 85–89, body 3 lines
- **Notes**: unused anywhere; duplicate proof body (L82–83 = L88–89).

### `lemma log_summable_pow`
- **Type**: `(f : ℕ → ℂ) (hf : Summable f) (m : ℕ) : Summable (fun n => Complex.log ((1 + f n)^m))`
- **What**: If `∑ f n` converges absolutely then `∑ log ((1 + f n)^m)` converges.
- **How**: mathlib `Complex.summable_log_one_add_of_summable` (`Mathlib/Analysis/SpecialFunctions/Log/Summable.lean:43`) scaled by `m` (`Summable.mul_left`), then `Summable.congr_cofinite` using `clog_pow` (converted from `atTop` to `cofinite` via `Nat.cofinite_eq_atTop`).
- **Hypotheses**: `f` summable.
- **Uses from project**: clog_pow
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 91–94, body 2 lines
- **Notes**: unused anywhere.

## File Summary
- Total declarations: 8 (0 defs; 8 lemmas; 0 instances; 0 other)
- Key API (used by 3+ others in the file): none (eventually_arg_pow 2)
- Unused declarations (not used by anything in this file): clog_pow2, log_summable_pow — and project-wide NONE of the 8 declarations is referenced outside this file (Delta.lean imports the module but never uses `arg_pow*`, `clog_pow*`, `log_summable_pow`, `one_add_abs_half_ne_zero`).
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: arg_pow_aux (33 lines, L18–51)

## Observations

### Mathlib API candidates
- `arg_pow_aux` (L18): mathlib has `Complex.arg_pow_coe_angle : (arg (x ^ n) : Real.Angle) = n • (arg x : Real.Angle)` (`Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean:502`) and `Complex.arg_mul`/`arg_mul_eq_add_arg_iff` (`Arg.lean:529`); the real-valued statement under `|arg x| < π/n` has no mathlib name — it is a legitimate (small) ForMathlib lemma, provable from `arg_pow_coe_angle` + `Real.Angle.toReal` injectivity on `(-π, π]` in a few lines instead of 33. Note `Complex.cpow_nat_mul'` (`Pow/Complex.lean:159`) already uses the hypothesis shape `-π < n * x.arg ∧ n * x.arg ≤ π`.
- `clog_pow`/`clog_pow2` (L79/L85): no `Complex.log_pow` with side condition in mathlib (searched `Log.lean`, `Pow/Complex.lean`); `Complex.log` unfolding + `Real.log_pow` is the right proof; a single lemma `Complex.log_pow_of_abs_arg_lt (hx : x ≠ 0) (h : |arg x| < π / n) : log (x ^ n) = n * log x` would subsume both and `arg_pow_aux`.
- `log_summable_pow` (L91): rides on `Complex.summable_log_one_add_of_summable` (`Log/Summable.lean:43`) — the only substantive ingredient.
- `one_add_abs_half_ne_zero` (L53): no mathlib analogue with a norm hypothesis (searched `one_add_ne_zero`, `isUnit_one_add`, `Units.oneSub`, `Complex.one_add_coe_ne_zero`); mathlib's `NormedRing.inverse_one_sub`/`Units.oneSub` machinery (`Mathlib/Analysis/Normed/Ring/Units.lean`) gives `IsUnit (1 - t)` for `‖t‖ < 1`, which yields this with `t = -x`.
- `eventually_arg_pow` (L58) uses `Complex.continuousAt_arg Complex.one_mem_slitPlane` (`Arg.lean:579`) — fine.

### Missing API / repeated patterns
- `clog_pow` and `clog_pow2` (L81–83, L87–89) are the same 3 lines; `arg_pow`/`arg_pow2` (L71–77) are the same 1 line. Make `eventually_arg_pow` public and add one filter-generic `eventually_clog_pow`; delete the four specialisations.
- The hypothesis `‖x‖ < 1/2` in `one_add_abs_half_ne_zero` should be `‖x‖ < 1`.

### Junk candidates
- The whole file: no consumer anywhere (Delta.lean:8 imports it — likely a leftover from an earlier proof of Δ's product expansion; the import can be removed after a rebuild check).
- `clog_pow2` (L85), `log_summable_pow` (L91): unused even in-file.
- Stray imports L3–4, L7–8 (`Algebra.Order.Ring.Star`, `CStarAlgebra.Classes`, `LinearAlgebra.Complex.FiniteDimensional`, `Tactic.Cases`) unrelated to the content.

### Moral duplicates within this batch
- `arg_pow` ≡ `arg_pow2` ≡ `eventually_arg_pow` (specialisations); `clog_pow` ≡ `clog_pow2`.
- Against mathlib: `arg_pow_aux` vs `arg_pow_coe_angle`.

### Generalization notes
- `arg_pow`, `arg_pow2`, `clog_pow`, `clog_pow2`: the private `eventually_arg_pow` is already generic in `{α} {l : Filter α}`; the public API should be too.
- `log_summable_pow`: holds for `f : ι → ℂ` over any index type with `cofinite` in place of `atTop` (mathlib's `summable_log_one_add_of_summable` is stated for arbitrary `ι`); only the `Nat.cofinite_eq_atTop` conversion pins it to ℕ.
- `one_add_abs_half_ne_zero`: holds in any normed ring with `‖1‖ = 1` (`NormOneClass`), with hypothesis `‖x‖ < 1`.
