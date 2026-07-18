# Source: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/IntegralPowerSeries/HasIntegralQExpansion.lean
Project-internal imports (XYin): [XYin.PhD.IntegralPowerSeries.IntegralPowerSeries]

### `def HasIntegralQExpansion`
- **Type**: `(h : ℝ) (f : ℍ → ℂ) : Prop`
- **What**: A function `f : ℍ → ℂ` "has an integral q-expansion (up to a pole at infinity)" if for some `n : ℕ` the product `q^n · f` — where `q(z) = e^{2πiz}` so `q^n` kills a pole of order ≤ n at the cusp — has a `q`-expansion (period `h`) with integer coefficients. This is integrality for functions meromorphic at infinity, e.g. the `j`-invariant.
- **How**: Existential over `n` of `IsIntegralPowerSeries (qExpansion h ((fun z ↦ cexp (2πi·z))^n * f))`, using mathlib's `UpperHalfPlane.qExpansion` and the project predicate `IsIntegralPowerSeries`.
- **Hypotheses**: none beyond the data `h`, `f` (no holomorphy or periodicity is imposed by the definition itself).
- **Uses from project**: [`IntegralPowerSeries.IsIntegralPowerSeries`]
- **Used by**: `HasIntegralQExpansion_ofPowerSeries`, `HasIntegralQExpansion.sum`
- **Visibility**: public
- **Lines**: 6–7, 2-line definition
- **Notes**: the multiplier is written with the fixed period `2π` in `cexp (2 * π * Complex.I * z)` while the q-expansion uses general period `h` — the two only match when `h = 1`; potential design mismatch worth flagging

### `lemma HasIntegralQExpansion_ofPowerSeries`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} (hf : IsIntegralPowerSeries (qExpansion h f)) : HasIntegralQExpansion h f`
- **What**: A function whose q-expansion is itself an integral power series (no pole) has an integral q-expansion in the extended sense.
- **How**: Takes `n = 0` in the existential; `pow_zero` and a `funext` computation identify `(fun _ ↦ 1) * f` with `f`, so the hypothesis applies verbatim.
- **Hypotheses**: `qExpansion h f` has integer coefficients.
- **Uses from project**: [`HasIntegralQExpansion`, `IntegralPowerSeries.IsIntegralPowerSeries`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 9–13, 4-line proof
- **Notes**: none

### `lemma IsIntegralPowerSeries_X_pow`
- **Type**: `(n : ℕ) : IsIntegralPowerSeries ((PowerSeries.X : PowerSeries ℂ) ^ n)`
- **What**: The monomial `X^n` in `ℂ⟦X⟧` has integer coefficients (its coefficients are 1 at degree n and 0 elsewhere).
- **How**: Via the coefficientwise criterion `IntegralPowerSeries.int_iff`, splitting on `m = n` and using mathlib's `PowerSeries.coeff_X_pow` (coefficient of `X^n` is the Kronecker delta), with witnesses `1` and `0`.
- **Hypotheses**: none.
- **Uses from project**: [`IntegralPowerSeries.IsIntegralPowerSeries`, `IntegralPowerSeries.int_iff`]
- **Used by**: `IsIntegralPowerSeries.shift`
- **Visibility**: public
- **Lines**: 15–23, 8-line proof
- **Notes**: none

### `lemma IsIntegralPowerSeries.shift`
- **Type**: `{f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f) (n : ℕ) : IsIntegralPowerSeries ((PowerSeries.X : PowerSeries ℂ) ^ n * f)`
- **What**: Multiplying an integral power series by `X^n` (shifting coefficients up by n) preserves integrality.
- **How**: Closure of the subring `IntegralPowerSeriesSubring` under multiplication (`Subring.mul_mem`) applied to `IsIntegralPowerSeries_X_pow n` and `hf`.
- **Hypotheses**: `f` has integer coefficients.
- **Uses from project**: [`IntegralPowerSeries.IntegralPowerSeriesSubring`, `IsIntegralPowerSeries_X_pow`, `IntegralPowerSeries.IsIntegralPowerSeries`]
- **Used by**: unused in file (intended for the sorried `HasIntegralQExpansion.sum`, where the two poles orders must be equalised by shifting)
- **Visibility**: public
- **Lines**: 25–27, 2-line proof
- **Notes**: none

### `lemma HasIntegralQExpansion.sum`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} {g : ℍ → ℂ} (hf : HasIntegralQExpansion h f) (hg : HasIntegralQExpansion h g) : HasIntegralQExpansion h (f + g)`
- **What**: Intended closure of `HasIntegralQExpansion` under addition: if `q^{n₁}f` and `q^{n₂}g` have integral expansions then so does `q^{max(n₁,n₂)}(f+g)`.
- **How**: Not proved — the body is `sorry`. The mathematical route would take `n = max n₁ n₂`, write `q^n(f+g) = q^{n-n₁}(q^{n₁}f) + q^{n-n₂}(q^{n₂}g)`, and combine `IsIntegralPowerSeries.shift` with additivity of `qExpansion` and the subring's `add_mem`; the missing ingredient is a `qExpansion`-of-product/shift identity relating `qExpansion h (q^k · F)` to `X^k * qExpansion h F`.
- **Hypotheses**: both `f` and `g` have integral q-expansions with the same period `h`.
- **Uses from project**: [`HasIntegralQExpansion`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 29–32, proof is a single `sorry`
- **Notes**: sorry present

### File Summary
- Total declarations: 5 (1 def, 4 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): [] (largest fan-in: `HasIntegralQExpansion` used by 2)
- Unused declarations (not used by anything in this file): `HasIntegralQExpansion_ofPowerSeries`, `IsIntegralPowerSeries.shift`, `HasIntegralQExpansion.sum`
- Declarations with sorry: [`HasIntegralQExpansion.sum`]
- Declarations with set_option: []
- Proofs >30 lines: []
