# XYin/PhD/Cox/KroneckerFrobenius.lean
Source: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/KroneckerFrobenius.lean
Project-internal imports: [`XYin.PhD.Cox.Kronecker`] (plus `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Algebra.CharP.Algebra`)

File purpose: the Frobenius calculation completing Kronecker's congruence (Cox Theorem 11.18(v)): `Φ_p(X, Y) ≡ (X^p − Y)(X − Y^p) mod p`. Works with the formal Cox product over `LaurentSeries (ZMod p)` at cyclotomic phase `ζ = 1`: the `p` lower roots coincide with the unit-step `j`-series, the distinguished root is their `p²`-th power, and `sub_pow_char` in characteristic `p` collapses the product to the Kronecker shape. All declarations are in namespace `Cox`.

### `theorem transformedJSeries_one_primeLower_eq_jUnit`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (i : Fin (p : ℕ)) : transformedJSeries (1 : ZMod (p : ℕ)) (primeLowerCoxMatrix p i) = jUnitLaurentSeriesMod p`
- **What**: At phase `ζ = 1`, the Laurent expansion of `j` transformed by any lower prime-level Cox matrix `(1, i; 0, p)`-type representative equals the unit-step reduction of the `j`-series mod `p` — all `p` lower roots coincide.
- **How**: Coefficientwise (`ext k`): `transformedJSeries_coeff` and `jUnitLaurentSeriesMod_coeff` reduce both sides to guarded `jIntCoeff` expressions; at phase 1 the cyclotomic factor is `1^… = 1`, and the divisibility guard `1 ∣ k` is trivial; coefficients below `-1` vanish by `jIntCoeff_eq_zero_of_lt`.
- **Hypotheses**: `p` prime (as `Fact`).
- **Uses from project**: [`transformedJSeries`, `primeLowerCoxMatrix`, `jUnitLaurentSeriesMod`, `transformedJSeries_coeff`, `jUnitLaurentSeriesMod_coeff`, `jIntCoeff_eq_zero_of_lt`]
- **Used by**: `formalCoxPolynomial_prime_one_factorization`, `transformedJSeries_one_sigmaZero_eq_primeLower_pow`
- **Visibility**: public
- **Lines**: 27–37 (proof 9 lines)
- **Notes**: none

### `theorem formalCoxPolynomial_prime_one_factorization`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : formalCoxPolynomial p (1 : ZMod (p : ℕ)) = (X - C (jUnitLaurentSeriesMod p)) ^ (p : ℕ) * (X - C (transformedJSeries (1 : ZMod (p : ℕ)) (sigmaZero p)))`
- **What**: At prime level and phase 1, the formal Cox product `∏_σ (X − j∘σ)` over the `p + 1` Cox matrices splits as one lower factor repeated `p` times, times one distinguished factor for `σ₀ = (p, 0; 0, 1)`.
- **How**: Reindexes the product over `CoxMatrix p` along the equivalence `primeCoxMatrixEquiv p` with `Fin (p+1)` (using `Equiv.prod_comp`), splits off the last index with `Fin.prod_univ_castSucc`, identifies each `castSucc` index with a `primeLowerCoxMatrix` via `primeCoxMatrixEquiv_symm_apply_of_lt`, and rewrites all lower factors equal via `transformedJSeries_one_primeLower_eq_jUnit`; `Fin.prod_const` collapses the constant product to a `p`-th power.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`formalCoxPolynomial`, `jUnitLaurentSeriesMod`, `transformedJSeries`, `sigmaZero`, `CoxMatrix`, `primeCoxMatrixEquiv`, `primeLowerCoxMatrix`, `primeCoxMatrixEquiv_symm_apply_of_lt`, `primeCoxMatrixEquiv_symm_apply_last`, `transformedJSeries_one_primeLower_eq_jUnit`]
- **Used by**: `formalCoxPolynomial_prime_one_frobenius`
- **Visibility**: public
- **Lines**: 41–64 (proof 22 lines)
- **Notes**: proof >10 lines; key lemmas `Fin.prod_univ_castSucc`, `Equiv.prod_comp`, `Fin.prod_const`

### `def unitJPowerSeries` (private)
- **Type**: `(K : Type*) [Ring K] : PowerSeries K`
- **What**: The power series `∑_{n≥0} c(n−1) q^n` whose coefficients are the integer `j`-expansion coefficients shifted by one — i.e. `q · j(q)` written as a genuine power series (the "unit part" of the `j`-Laurent series).
- **How**: `PowerSeries.mk` with coefficient function `n ↦ (jIntCoeff (n − 1) : K)`.
- **Hypotheses**: `K` any ring.
- **Uses from project**: [`jIntCoeff`]
- **Used by**: `unitJPowerSeries_coeff`, `jUnitLaurentSeriesMod_eq_unitJPowerSeries`, `transformedJSeries_one_sigmaZero_eq_expand`, `unitJPowerSeries_pow_prime_sq_eq_expand`
- **Visibility**: private
- **Lines**: 66–68
- **Notes**: `noncomputable`

### `theorem unitJPowerSeries_coeff` (private)
- **Type**: `{K : Type*} [Ring K] (n : ℕ) : PowerSeries.coeff n (unitJPowerSeries K) = (jIntCoeff ((n : ℤ) - 1) : K)`
- **What**: The defining coefficient formula of `unitJPowerSeries` in simp-normal form.
- **How**: Unfolds `unitJPowerSeries` and `PowerSeries.mk` by `simp`.
- **Hypotheses**: `K` any ring.
- **Uses from project**: [`unitJPowerSeries`, `jIntCoeff`]
- **Used by**: `jUnitLaurentSeriesMod_eq_unitJPowerSeries`, `transformedJSeries_one_sigmaZero_eq_expand`
- **Visibility**: private
- **Lines**: 70–75 (proof 1 line)
- **Notes**: `@[simp]` (private simp lemma)

### `theorem jUnitLaurentSeriesMod_eq_unitJPowerSeries` (private)
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : jUnitLaurentSeriesMod p = HahnSeries.single (-1 : ℤ) 1 * (unitJPowerSeries (ZMod (p : ℕ)) : LaurentSeries (ZMod (p : ℕ)))`
- **What**: Normal form for the unit-step `j`-series mod `p`: it is `q^{-1}` times the coerced power series `unitJPowerSeries` — separating the pole from the regular part.
- **How**: Coefficientwise: `HahnSeries.coeff_single_mul` shifts the index by `−1`, `PowerSeries.coeff_coe` handles the coercion's support guard, `Int.natAbs_of_nonneg` matches the shifted natural index, and coefficients below the pole vanish by `jIntCoeff_eq_zero_of_lt`; the integer bookkeeping is discharged by `lia`.
- **Hypotheses**: `p` prime (only used for the `ZMod p` coefficient ring).
- **Uses from project**: [`jUnitLaurentSeriesMod`, `jUnitLaurentSeriesMod_coeff`, `unitJPowerSeries`, `unitJPowerSeries_coeff`, `jIntCoeff_eq_zero_of_lt`, `jIntCoeff`]
- **Used by**: `transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq`
- **Visibility**: private
- **Lines**: 77–96 (proof 18 lines)
- **Notes**: proof >10 lines; key lemmas `HahnSeries.coeff_single_mul`, `PowerSeries.coeff_coe`

### `theorem prime_sq_dvd_iff_dvd_shift_natAbs` (private)
- **Type**: `(p : ℕ+) (k : ℤ) : ((p : ℤ) ^ 2 ∣ k) ↔ (p : ℕ) ^ 2 ∣ (k - -((p : ℤ) ^ 2)).natAbs`
- **What**: Pure integer arithmetic: `p² ∣ k` iff `p² ∣ |k + p²|` (as naturals) — the divisibility guard transforms correctly under the index shift by the pole order `p²`.
- **How**: Transfers to `ℤ` via `Int.natCast_dvd`, then both directions follow from closure of divisibility under adding/subtracting `p²` (`Dvd.dvd.add` / `Dvd.dvd.sub` with `dvd_refl`).
- **Hypotheses**: none (works for any `p : ℕ+`, `k : ℤ`).
- **Uses from project**: []
- **Used by**: `transformedJSeries_one_sigmaZero_eq_expand`
- **Visibility**: private
- **Lines**: 98–110 (proof 11 lines)
- **Notes**: proof >10 lines; key lemma `Int.natCast_dvd`

### `theorem transformedJSeries_one_sigmaZero_eq_expand` (private)
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : transformedJSeries (1 : ZMod (p : ℕ)) (sigmaZero p) = HahnSeries.single (-((p : ℤ) ^ 2)) 1 * ((unitJPowerSeries (ZMod (p : ℕ))).expand ((p : ℕ) ^ 2) (pow_ne_zero 2 (PNat.ne_zero p)) : LaurentSeries (ZMod (p : ℕ)))`
- **What**: The distinguished root `j∘σ₀` (with `σ₀ = diag(p, 1)` acting as `τ ↦ p²τ` in the series variable) equals `q^{-p²}` times the `p²`-fold expansion (substitution `q ↦ q^{p²}`) of the unit power series — its q-expansion is the original with all exponents multiplied by `p²`.
- **How**: Coefficientwise: `transformedJSeries_coeff` gives the guarded formula with divisibility guard `p² ∣ k`; `HahnSeries.coeff_single_mul` shifts by `−p²` and `PowerSeries.coeff_expand` produces the matching guard on the power-series side, aligned via `prime_sq_dvd_iff_dvd_shift_natAbs`; on the divisible branch the exponent identity `(p²t + p²)/p² = t + 1` is computed with `Int.mul_ediv_cancel_left`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`transformedJSeries`, `sigmaZero`, `transformedJSeries_coeff`, `unitJPowerSeries`, `unitJPowerSeries_coeff`, `prime_sq_dvd_iff_dvd_shift_natAbs`]
- **Used by**: `transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq`
- **Visibility**: private
- **Lines**: 112–147 (proof 30 lines)
- **Notes**: proof at 30 lines (the longest in the file); key lemmas `PowerSeries.coeff_expand`, `HahnSeries.coeff_single_mul`, `Int.mul_ediv_cancel_left`

### `theorem unitJPowerSeries_pow_prime_sq_eq_expand` (private)
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : unitJPowerSeries (ZMod (p : ℕ)) ^ ((p : ℕ) ^ 2) = (unitJPowerSeries (ZMod (p : ℕ))).expand ((p : ℕ) ^ 2) (pow_ne_zero 2 (PNat.ne_zero p))`
- **What**: The Frobenius step: over `ZMod p`, raising the power series to the `p²`-th power equals substituting `q ↦ q^{p²}` — because the coefficient Frobenius `x ↦ x^{p²}` is the identity on `ZMod p`.
- **How**: Instantiates mathlib's `MvPowerSeries.map_iterateFrobenius_expand` at exponent 2, and kills the coefficient map by showing `iterateFrobenius (ZMod p) p 2 = id` via `ZMod.pow_card_pow` (Fermat).
- **Hypotheses**: `p` prime.
- **Uses from project**: [`unitJPowerSeries`]
- **Used by**: `transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq`
- **Visibility**: private
- **Lines**: 149–163 (proof 13 lines)
- **Notes**: proof >10 lines; key lemmas `MvPowerSeries.map_iterateFrobenius_expand`, `ZMod.pow_card_pow`

### `theorem transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq` (private)
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : transformedJSeries (1 : ZMod (p : ℕ)) (sigmaZero p) = jUnitLaurentSeriesMod p ^ ((p : ℕ) ^ 2)`
- **What**: The distinguished root is exactly the `p²`-th power of the (common) lower root: `j(q^{p²}) = j(q)^{p²}` in characteristic `p`.
- **How**: Chains the three private normal forms: rewrite the left side by `transformedJSeries_one_sigmaZero_eq_expand`, the right side by `jUnitLaurentSeriesMod_eq_unitJPowerSeries` and `unitJPowerSeries_pow_prime_sq_eq_expand`; the single-term factor is handled by `HahnSeries.single_pow` and `PowerSeries.coe_pow`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`transformedJSeries`, `sigmaZero`, `jUnitLaurentSeriesMod`, `transformedJSeries_one_sigmaZero_eq_expand`, `jUnitLaurentSeriesMod_eq_unitJPowerSeries`, `unitJPowerSeries_pow_prime_sq_eq_expand`]
- **Used by**: `transformedJSeries_one_sigmaZero_eq_primeLower_pow`, `transformedJSeries_one_sigmaZero_eq_jLaurent_pow`
- **Visibility**: private
- **Lines**: 165–173 (proof 6 lines)
- **Notes**: key lemmas `HahnSeries.single_pow`, `PowerSeries.coe_pow`

### `theorem transformedJSeries_one_sigmaZero_eq_primeLower_pow`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (i : Fin (p : ℕ)) : transformedJSeries (1 : ZMod (p : ℕ)) (sigmaZero p) = transformedJSeries (1 : ZMod (p : ℕ)) (primeLowerCoxMatrix p i) ^ ((p : ℕ) ^ 2)`
- **What**: Public restatement: the distinguished root is the `p²`-th power of each of the `p` equal lower roots.
- **How**: Rewrites the lower root to `jUnitLaurentSeriesMod p` via `transformedJSeries_one_primeLower_eq_jUnit`, then applies `transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`transformedJSeries`, `sigmaZero`, `primeLowerCoxMatrix`, `transformedJSeries_one_primeLower_eq_jUnit`, `transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq`]
- **Used by**: unused in file (exported API)
- **Visibility**: public
- **Lines**: 176–182 (proof 2 lines)
- **Notes**: none

### `theorem transformedJSeries_one_sigmaZero_eq_jLaurent_pow`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : transformedJSeries (1 : ZMod (p : ℕ)) (sigmaZero p) = jLaurentSeriesMod p ^ (p : ℕ)`
- **What**: Equivalent form: the distinguished root is the `p`-th power of the width-`p` `j`-series (the series in `q^{1/p}` reduced mod `p`), since `(j_unit)^{p²} = ((j_unit)^p)^p` and `(j_unit)^p = j_width-p` by Frobenius.
- **How**: From `transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq`, a `calc` step splits `p² = p·p` (`pow_mul`, `pow_two`) and rewrites the inner `p`-th power via the imported `jUnitLaurentSeriesMod_pow_prime`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`transformedJSeries`, `sigmaZero`, `jLaurentSeriesMod`, `jUnitLaurentSeriesMod`, `transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq`, `jUnitLaurentSeriesMod_pow_prime`]
- **Used by**: `formalCoxPolynomial_prime_one_frobenius`
- **Visibility**: public
- **Lines**: 185–195 (proof 8 lines)
- **Notes**: none

### `theorem formalCoxPolynomial_prime_one_frobenius`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : formalCoxPolynomial p (1 : ZMod (p : ℕ)) = (X ^ (p : ℕ) - C (jLaurentSeriesMod p)) * (X - C (jLaurentSeriesMod p ^ (p : ℕ)))`
- **What**: The formal Cox product at prime level and phase 1 in Kronecker form: `(X − j_w)^p (X − j_w^p)` becomes `(X^p − j_w)(X − j_w^p)` where `j_w = jLaurentSeriesMod p` — the algebraic heart of Kronecker's congruence.
- **How**: Installs `CharP (LaurentSeries (ZMod p)) p` via `charP_of_injective_ringHom` along the injective constant map `HahnSeries.C` (`HahnSeries.C_injective`); then from `formalCoxPolynomial_prime_one_factorization` and `transformedJSeries_one_sigmaZero_eq_jLaurent_pow`, the freshman's dream `sub_pow_char` turns `(X − C j_unit)^p` into `X^p − C (j_unit^p)`, and `jUnitLaurentSeriesMod_pow_prime` identifies `j_unit^p = j_w`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`formalCoxPolynomial`, `jLaurentSeriesMod`, `formalCoxPolynomial_prime_one_factorization`, `transformedJSeries_one_sigmaZero_eq_jLaurent_pow`, `jUnitLaurentSeriesMod_pow_prime`]
- **Used by**: `kronecker_after_specializeJ`
- **Visibility**: public
- **Lines**: 198–208 (proof 8 lines)
- **Notes**: key lemmas `sub_pow_char`, `charP_of_injective_ringHom`, `HahnSeries.C_injective`; uses `letI` for the local `CharP` instance

### `theorem kronecker_after_specializeJ`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : specializeJMod p (BivariatePolynomial.map (Int.castRingHom (ZMod (p : ℕ))) (modularPolynomial p)) = specializeJMod p ((varX : BivariatePolynomial (ZMod p)) ^ p - varY) * specializeJMod p (varX - (varY : BivariatePolynomial (ZMod p)) ^ p)` (abbreviated)
- **What**: After specializing the `Y`-variable at the width-`p` `j`-series mod `p`, the reduced modular polynomial `Φ_p mod p` equals the image of `(X^p − Y)(X − Y^p)` — Kronecker's congruence holds after the injective specialization.
- **How**: The imported bridge `specializeJMod_modularPolynomial_eq_formal` identifies the specialized `Φ_p mod p` with the formal Cox product at phase 1, which `formalCoxPolynomial_prime_one_frobenius` puts in Kronecker form; `simp` matches the specialized images of `varX`, `varY`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`specializeJMod`, `BivariatePolynomial.map`, `modularPolynomial`, `BivariatePolynomial.varX`, `BivariatePolynomial.varY`, `specializeJMod_modularPolynomial_eq_formal`, `formalCoxPolynomial_prime_one_frobenius`]
- **Used by**: `theorem_11_18_v`
- **Visibility**: public
- **Lines**: 212–226 (proof 3 lines)
- **Notes**: none

### `theorem theorem_11_18_v`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : BivariatePolynomial.map (Int.castRingHom (ZMod (p : ℕ))) (modularPolynomial p) = ((varX : BivariatePolynomial (ZMod p)) ^ p - varY) * (varX - (varY : BivariatePolynomial (ZMod p)) ^ p)` (abbreviated)
- **What**: Cox Theorem 11.18(v), Kronecker's congruence: the modular polynomial reduced mod `p` factors as `Φ_p(X, Y) ≡ (X^p − Y)(X − Y^p) (mod p)`, as an identity of bivariate polynomials over `ZMod p`.
- **How**: Both sides are bivariate polynomials with the same image under the injective ring hom `specializeJMod p` (injectivity from the imported `specializeJMod_injective`, which rests on the transcendence of the `j`-series); the images agree by `kronecker_after_specializeJ` and multiplicativity (`map_mul`).
- **Hypotheses**: `p` prime.
- **Uses from project**: [`BivariatePolynomial.map`, `modularPolynomial`, `BivariatePolynomial.varX`, `BivariatePolynomial.varY`, `specializeJMod_injective`, `kronecker_after_specializeJ`]
- **Used by**: unused in file (terminal result)
- **Visibility**: public
- **Lines**: 229–239 (proof 2 lines)
- **Notes**: none

### File Summary
- Total declarations: 13 (1 def, 12 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): `unitJPowerSeries` (private, used by 4)
- Unused declarations (not used by anything in this file): `transformedJSeries_one_sigmaZero_eq_primeLower_pow` (exported API), `theorem_11_18_v` (terminal result)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [] (longest: `transformedJSeries_one_sigmaZero_eq_expand` at 30 lines)
