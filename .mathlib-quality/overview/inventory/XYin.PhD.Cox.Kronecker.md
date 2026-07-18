# Inventory: XYin/PhD/Cox/Kronecker.lean

**Source**: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/Kronecker.lean
**Project-internal imports**: `XYin.PhD.Cox.DiagonalLaurent`, `XYin.PhD.Cox.LaurentPolynomialEvaluation`

All declarations live in `namespace Cox` inside a `noncomputable section`. The file develops the cyclotomic-descent and integral Laurent-series infrastructure for Kronecker's congruence `Φ_p(X,Y) ≡ (X^p − Y)(X − Y^p) mod p` (Cox Thm 11.18(v)); the Frobenius factorization itself lives in `KroneckerFrobenius.lean`.

---

### `def primeLowerCoxMatrix`
- **Type**: `(p : ℕ+) → (i : Fin (p : ℕ)) → CoxMatrix p`
- **What**: The prime-level Cox representative matrix `(1, i; 0, p)`, i.e. the upper-triangular matrix with `a = 1`, `b = i`, `d = p`, for each `0 ≤ i < p`.
- **How**: Direct structure construction; the determinant condition is `1 * p = p` (`Nat.one_mul`), primitivity of `(1, i, p)` is discharged by `simp` since `gcd` with 1 is 1.
- **Hypotheses**: `p` a positive natural (primality not needed for the definition), `i < p` from the `Fin` type.
- **Uses from project**: [`CoxMatrix`]
- **Used by**: `primeFinToCoxMatrix`, `primeFinToCoxMatrix_castSucc`, `primeFinToCoxMatrix_surjective`, `primeFinToCoxMatrix_injective`, `primeFinEquivCoxMatrix_apply_of_lt`, `primeCoxMatrixEquiv_symm_apply_of_lt`
- **Visibility**: public
- **Lines**: 31–39, definition (9 lines)
- **Notes**: none

### `def primeFinToCoxMatrix`
- **Type**: `(p : ℕ+) → Fin ((p : ℕ) + 1) → CoxMatrix p`
- **What**: Enumerates the `p + 1` prime-level Cox representatives: index `i < p` maps to `(1,i;0,p)` and the last index maps to `σ₀ = (p,0;0,1)`.
- **How**: Case split on the `Fin (p+1)` index via `Fin.lastCases`, sending the last case to `sigmaZero p` and the cast-successor cases to `primeLowerCoxMatrix p`.
- **Hypotheses**: none beyond `p : ℕ+`.
- **Uses from project**: [`CoxMatrix`, `sigmaZero`, `primeLowerCoxMatrix`]
- **Used by**: `primeFinToCoxMatrix_castSucc`, `primeFinToCoxMatrix_last`, `primeFinToCoxMatrix_surjective`, `primeFinToCoxMatrix_injective`, `primeFinEquivCoxMatrix`, `primeFinEquivCoxMatrix_apply_of_lt`, `primeFinEquivCoxMatrix_apply_last`
- **Visibility**: private
- **Lines**: 41–42, definition (2 lines)
- **Notes**: none

### `theorem primeFinToCoxMatrix_castSucc`
- **Type**: `(p : ℕ+) (i : Fin (p : ℕ)) : primeFinToCoxMatrix p i.castSucc = primeLowerCoxMatrix p i`
- **What**: Computation rule: the enumeration evaluated at a non-last index `i.castSucc` yields the lower-triangular representative `(1,i;0,p)`.
- **How**: Unfolds `primeFinToCoxMatrix` and applies the `Fin.lastCases_castSucc` reduction via `simp`.
- **Hypotheses**: none.
- **Uses from project**: [`primeFinToCoxMatrix`, `primeLowerCoxMatrix`]
- **Used by**: `primeFinToCoxMatrix_surjective`, `primeFinToCoxMatrix_injective`, `primeFinEquivCoxMatrix_apply_of_lt`
- **Visibility**: private
- **Lines**: 44–47, proof 1 line
- **Notes**: `@[simp]`

### `theorem primeFinToCoxMatrix_last`
- **Type**: `(p : ℕ+) : primeFinToCoxMatrix p (Fin.last (p : ℕ)) = sigmaZero p`
- **What**: Computation rule: the enumeration at the last index yields `σ₀ = (p,0;0,1)`.
- **How**: Unfolds `primeFinToCoxMatrix` and applies the `Fin.lastCases_last` reduction via `simp`.
- **Hypotheses**: none.
- **Uses from project**: [`primeFinToCoxMatrix`, `sigmaZero`]
- **Used by**: `primeFinToCoxMatrix_surjective`, `primeFinToCoxMatrix_injective`, `primeFinEquivCoxMatrix_apply_last`
- **Visibility**: private
- **Lines**: 49–52, proof 1 line
- **Notes**: `@[simp]`

### `theorem primeFinToCoxMatrix_surjective`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : Function.Surjective (primeFinToCoxMatrix p)`
- **What**: Every Cox matrix of prime level `p` is one of the `p + 1` enumerated representatives — the classification of degree-`p` upper-triangular primitive matrices at a prime.
- **How**: Since `a ∣ p` (from `a·d = p`) and `p` is prime, `Nat.Prime.eq_one_or_self_of_dvd` gives `a = 1` (then `d = p`, hit by a `castSucc` index with `b = i`) or `a = p` (then `d = 1`, `b < d = 1` forces `b = 0`, giving `σ₀`); equality of Cox matrices is checked componentwise via `CoxMatrix.toFin_injective`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`primeFinToCoxMatrix`, `primeFinToCoxMatrix_castSucc`, `primeFinToCoxMatrix_last`, `CoxMatrix.toFin_injective`, `CoxMatrix.toFin`, `primeLowerCoxMatrix`, `sigmaZero`]
- **Used by**: `primeFinEquivCoxMatrix`
- **Visibility**: private
- **Lines**: 54–79, proof 24 lines
- **Notes**: none

### `theorem primeFinToCoxMatrix_injective`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : Function.Injective (primeFinToCoxMatrix p)`
- **What**: The `p + 1` enumerated prime-level representatives are pairwise distinct.
- **How**: Case split both indices via `Fin.eq_castSucc_or_eq_last`; two lower matrices agreeing forces equal `b`-entries (hence equal indices), while a lower matrix cannot equal `σ₀` because their `a`-entries are `1` and `p` and `p ≠ 1` by `Nat.Prime.ne_one`.
- **Hypotheses**: `p` prime (only to rule out `p = 1`).
- **Uses from project**: [`primeFinToCoxMatrix`, `primeFinToCoxMatrix_castSucc`, `primeFinToCoxMatrix_last`, `primeLowerCoxMatrix`, `sigmaZero`, `CoxMatrix`]
- **Used by**: `primeFinEquivCoxMatrix`
- **Visibility**: private
- **Lines**: 81–103, proof 20 lines
- **Notes**: none

### `def primeFinEquivCoxMatrix`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : Fin ((p : ℕ) + 1) ≃ CoxMatrix p`
- **What**: The bijection between `Fin (p+1)` and the prime-level Cox matrices — in particular there are exactly `p + 1` of them.
- **How**: `Equiv.ofBijective` applied to `primeFinToCoxMatrix` with the injectivity and surjectivity lemmas above.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`primeFinToCoxMatrix`, `primeFinToCoxMatrix_injective`, `primeFinToCoxMatrix_surjective`, `CoxMatrix`]
- **Used by**: `primeFinEquivCoxMatrix_apply_of_lt`, `primeFinEquivCoxMatrix_apply_last`, `primeCoxMatrixEquiv`
- **Visibility**: private
- **Lines**: 105–109, definition (5 lines)
- **Notes**: noncomputable

### `theorem primeFinEquivCoxMatrix_apply_of_lt`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (i : Fin ((p : ℕ) + 1)) (hi : (i : ℕ) < (p : ℕ)) : primeFinEquivCoxMatrix p i = primeLowerCoxMatrix p ⟨i, hi⟩`
- **What**: The equivalence at any index `i < p` gives the lower-triangular representative `(1,i;0,p)`.
- **How**: Identifies `i` with `⟨i,hi⟩.castSucc` (a `Fin.ext` on values) and reduces by `primeFinToCoxMatrix_castSucc`.
- **Hypotheses**: `p` prime; `i < p` as naturals.
- **Uses from project**: [`primeFinEquivCoxMatrix`, `primeLowerCoxMatrix`, `primeFinToCoxMatrix`, `primeFinToCoxMatrix_castSucc`]
- **Used by**: `primeCoxMatrixEquiv_symm_apply_of_lt`
- **Visibility**: private
- **Lines**: 111–119, proof 4 lines
- **Notes**: `@[simp]`

### `theorem primeFinEquivCoxMatrix_apply_last`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : primeFinEquivCoxMatrix p (Fin.last (p : ℕ)) = sigmaZero p`
- **What**: The equivalence at the last index gives `σ₀ = (p,0;0,1)`.
- **How**: `Equiv.ofBijective` applies its underlying function definitionally (`change`), then `primeFinToCoxMatrix_last`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`primeFinEquivCoxMatrix`, `sigmaZero`, `primeFinToCoxMatrix`, `primeFinToCoxMatrix_last`]
- **Used by**: `primeCoxMatrixEquiv_symm_apply_last`
- **Visibility**: private
- **Lines**: 121–126, proof 2 lines
- **Notes**: `@[simp]`

### `def primeCoxMatrixEquiv`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : CoxMatrix p ≃ Fin ((p : ℕ) + 1)`
- **What**: The public-facing enumeration of prime-level Cox representatives: the set of Cox matrices of level a prime `p` is in bijection with `Fin (p+1)` (the `p` matrices `(1,i;0,p)` plus `(p,0;0,1)`).
- **How**: The inverse (`.symm`) of the private `primeFinEquivCoxMatrix`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`primeFinEquivCoxMatrix`, `CoxMatrix`]
- **Used by**: `primeCoxMatrixEquiv_symm_apply_of_lt`, `primeCoxMatrixEquiv_symm_apply_last`
- **Visibility**: public
- **Lines**: 130–133, definition (4 lines)
- **Notes**: noncomputable

### `theorem primeCoxMatrixEquiv_symm_apply_of_lt`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (i : Fin ((p : ℕ) + 1)) (hi : (i : ℕ) < (p : ℕ)) : (primeCoxMatrixEquiv p).symm i = primeLowerCoxMatrix p ⟨i, hi⟩`
- **What**: Public computation rule: the inverse enumeration sends an index `i < p` to `(1,i;0,p)`.
- **How**: `(e.symm).symm = e`, so this is exactly `primeFinEquivCoxMatrix_apply_of_lt`.
- **Hypotheses**: `p` prime; `i < p`.
- **Uses from project**: [`primeCoxMatrixEquiv`, `primeLowerCoxMatrix`, `primeFinEquivCoxMatrix_apply_of_lt`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 135–140, proof 1 line
- **Notes**: `@[simp]`

### `theorem primeCoxMatrixEquiv_symm_apply_last`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : (primeCoxMatrixEquiv p).symm (Fin.last (p : ℕ)) = sigmaZero p`
- **What**: Public computation rule: the inverse enumeration sends the last index to `σ₀ = (p,0;0,1)`.
- **How**: Direct application of `primeFinEquivCoxMatrix_apply_last`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`primeCoxMatrixEquiv`, `sigmaZero`, `primeFinEquivCoxMatrix_apply_last`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 142–146, proof 1 line
- **Notes**: `@[simp]`

### `theorem jIntCoeff_eq_zero_of_lt`
- **Type**: `{n : ℤ} (hn : n < -(1 : ℤ)) : jIntCoeff n = 0`
- **What**: The integer q-expansion coefficients of the `j`-function vanish in degrees below `-1`, i.e. `j` has only a simple pole at the cusp.
- **How**: The complex Laurent coefficient vanishes below the pole order by `laurentqExpansion.coeff_eq_zero_of_lt` together with `j_poleOrder = -1`; the integrality spec `jIntCoeff_spec` transfers this to `ℤ` since `ℤ → ℂ` is injective (`exact_mod_cast`).
- **Hypotheses**: `n < -1`.
- **Uses from project**: [`jIntCoeff`, `laurentqExpansion`, `laurentqExpansion.coeff_eq_zero_of_lt`, `j`, `j_poleOrder`, `jIntCoeff_spec`]
- **Used by**: `jIntegralLaurentSeries`, `jIntegralLaurentSeriesWidth_coeff_mul_map_complex`, `jUnitLaurentSeriesMod_coeff_eq_zero_of_lt`
- **Visibility**: public
- **Lines**: 148–157, proof 8 lines
- **Notes**: none

### `def jIntegralLaurentSeries`
- **Type**: `LaurentSeries ℤ`
- **What**: The formal Laurent series over `ℤ` whose coefficients are the integral q-expansion coefficients of `j`: `q⁻¹ + 744 + 196884q + …`.
- **How**: A `HahnSeries` with coefficient function `jIntCoeff`; well-orderedness of the support follows because the support is bounded below by `-1` (`jIntCoeff_eq_zero_of_lt`), so `BddBelow.isWF` and `Set.IsWF.isPWO` apply.
- **Hypotheses**: none.
- **Uses from project**: [`jIntCoeff`, `jIntCoeff_eq_zero_of_lt`]
- **Used by**: `jIntegralLaurentSeries_coeff`, `jIntegralLaurentSeries_map_complex`, `jUnitLaurentSeriesMod`
- **Visibility**: public
- **Lines**: 159–169, definition with 8-line support proof
- **Notes**: none

### `theorem jIntegralLaurentSeries_coeff`
- **Type**: `(n : ℤ) : jIntegralLaurentSeries.coeff n = jIntCoeff n`
- **What**: Coefficient-extraction rule for the integral `j`-series.
- **How**: Definitional (`rfl`).
- **Hypotheses**: none.
- **Uses from project**: [`jIntegralLaurentSeries`, `jIntCoeff`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 171–174, proof `rfl`
- **Notes**: `@[simp]`

### `theorem jIntegralLaurentSeries_map_complex`
- **Type**: `jIntegralLaurentSeries.map (Int.castRingHom ℂ) = laurentqExpansion 1 j`
- **What**: Pushing the integral `j`-series into `ℂ` recovers the analytic unit-width Laurent q-expansion of `j` — i.e. the integral series is a genuine lift of the analytic expansion.
- **How**: Coefficientwise via `HahnSeries.ext`; each coefficient identity is exactly the defining property `jIntCoeff_spec`.
- **Hypotheses**: none.
- **Uses from project**: [`jIntegralLaurentSeries`, `laurentqExpansion`, `j`, `jIntCoeff`, `jIntCoeff_spec`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 176–181, proof 4 lines
- **Notes**: none

### `def jIntegralLaurentSeriesWidth`
- **Type**: `(m : ℕ+) → LaurentSeries ℤ`
- **What**: The integral Laurent expansion of `j` written in the width-`m` local parameter `q_m = e^{2πiτ/m}`: coefficient at `k` is `jIntCoeff (k/m)` when `m ∣ k` and `k ≥ -m`, else `0` (so `j = q_m^{-m} + 744 + …`).
- **How**: A `HahnSeries` with the described piecewise coefficient function; support is bounded below by `-m` directly from the `if`-condition, giving `isPWO` via `BddBelow.isWF`.
- **Hypotheses**: none.
- **Uses from project**: [`jIntCoeff`]
- **Used by**: `jIntegralLaurentSeriesWidth_coeff`, `jIntegralLaurentSeriesWidth_coeff_mul_map_complex`, `jIntegralLaurentSeriesWidth_map_complex`, `jIntegralLaurentSeriesWidth_map_zmod`, `specializeJIntegral`, `specializeJIntegral_map_zmod`, `specializeJIntegral_map_complex`
- **Visibility**: public
- **Lines**: 183–195, definition with 9-line support proof
- **Notes**: none

### `theorem jIntegralLaurentSeriesWidth_coeff`
- **Type**: `(m : ℕ+) (k : ℤ) : (jIntegralLaurentSeriesWidth m).coeff k = if (m : ℤ) ∣ k ∧ -(m : ℤ) ≤ k then jIntCoeff (k / (m : ℤ)) else 0`
- **What**: Coefficient-extraction rule for the integral width-`m` series.
- **How**: Definitional (`rfl`).
- **Hypotheses**: none.
- **Uses from project**: [`jIntegralLaurentSeriesWidth`, `jIntCoeff`]
- **Used by**: `jIntegralLaurentSeriesWidth_coeff_mul_map_complex`, `jIntegralLaurentSeriesWidth_map_zmod`
- **Visibility**: public
- **Lines**: 197–202, proof `rfl`
- **Notes**: `@[simp]`

### `theorem jIntegralLaurentSeriesWidth_coeff_mul_map_complex`
- **Type**: `(m : ℕ+) (q : ℤ) : ((jIntegralLaurentSeriesWidth m).coeff ((m : ℤ) * q) : ℂ) = (laurentqExpansion ((m : ℕ) : ℝ) j).coeff ((m : ℤ) * q)`
- **What**: At exponents that are multiples of `m`, the complexified integral width-`m` coefficient agrees with the analytic width-`m` Laurent coefficient of `j`.
- **How**: The rescaling identity `laurentqExpansion_nat_mul_coeff` (applied with `j_cuspFunction_meromorphicAt` and `j_periodic`) reduces the width-`m` coefficient at `mq` to the unit-width coefficient at `q`; then split on `q ≥ -1` (agreeing via `jIntCoeff_spec`) versus `q < -1` (both sides vanish, using `jIntCoeff_eq_zero_of_lt`).
- **Hypotheses**: none (the divisible case is built into the exponent `m·q`).
- **Uses from project**: [`jIntegralLaurentSeriesWidth`, `jIntegralLaurentSeriesWidth_coeff`, `laurentqExpansion`, `laurentqExpansion_nat_mul_coeff`, `j`, `j_cuspFunction_meromorphicAt`, `j_periodic`, `jIntCoeff_spec`, `jIntCoeff_eq_zero_of_lt`, `jIntCoeff`]
- **Used by**: `jIntegralLaurentSeriesWidth_map_complex`
- **Visibility**: private
- **Lines**: 204–226, proof 21 lines
- **Notes**: none

### `theorem jIntegralLaurentSeriesWidth_map_complex`
- **Type**: `(m : ℕ+) : (jIntegralLaurentSeriesWidth m).map (Int.castRingHom ℂ) = laurentqExpansion ((m : ℕ) : ℝ) j`
- **What**: The integral width-`m` series is an integral lift of the full analytic width-`m` Laurent expansion of `j` over `ℂ`.
- **How**: Coefficientwise: exponents divisible by `m` are handled by `jIntegralLaurentSeriesWidth_coeff_mul_map_complex`; non-divisible exponents vanish on both sides, the analytic side by `laurentqExpansion_nat_mul_coeff_of_not_dvd` (a width-`m` expansion of a `1`-periodic function has support in `mℤ`).
- **Hypotheses**: none.
- **Uses from project**: [`jIntegralLaurentSeriesWidth`, `jIntegralLaurentSeriesWidth_coeff`, `jIntegralLaurentSeriesWidth_coeff_mul_map_complex`, `laurentqExpansion`, `laurentqExpansion_nat_mul_coeff_of_not_dvd`, `j`, `j_cuspFunction_meromorphicAt`, `j_periodic`]
- **Used by**: `specializeJIntegral_map_complex`
- **Visibility**: public
- **Lines**: 228–241, proof 12 lines
- **Notes**: none

### `def jUnitLaurentSeriesMod`
- **Type**: `(p : ℕ+) → LaurentSeries (ZMod (p : ℕ))`
- **What**: The mod-`p` reduction of the unit-width integral `j`-series: the Laurent series over `𝔽_p` with coefficients `jIntCoeff n mod p`.
- **How**: `HahnSeries.map` of `jIntegralLaurentSeries` along the reduction homomorphism `ℤ → ZMod p`.
- **Hypotheses**: none.
- **Uses from project**: [`jIntegralLaurentSeries`]
- **Used by**: `jUnitLaurentSeriesMod_coeff`, `jUnitLaurentSeriesMod_coeff_neg_one`, `jUnitLaurentSeriesMod_coeff_eq_zero_of_lt`, `jUnitLaurentSeriesMod_order`, `jUnitLaurentSeriesModPrimeNormalForm`, `jUnitLaurentSeriesMod_pow_prime_normalForm`, `jUnitPrimeNormalForm_coeff_mul_of_lower`, `jUnitLaurentSeriesMod_pow_prime`
- **Visibility**: public
- **Lines**: 243–245, definition (3 lines)
- **Notes**: none

### `theorem jUnitLaurentSeriesMod_coeff`
- **Type**: `(p : ℕ+) (n : ℤ) : (jUnitLaurentSeriesMod p).coeff n = (jIntCoeff n : ZMod (p : ℕ))`
- **What**: Coefficient-extraction rule for the mod-`p` unit-width `j`-series.
- **How**: Definitional (`rfl`) since `HahnSeries.map` acts coefficientwise.
- **Hypotheses**: none.
- **Uses from project**: [`jUnitLaurentSeriesMod`, `jIntCoeff`]
- **Used by**: `jUnitLaurentSeriesMod_coeff_neg_one`, `jUnitLaurentSeriesMod_coeff_eq_zero_of_lt`, `jUnitPrimeNormalForm_coeff_mul_of_lower`
- **Visibility**: public
- **Lines**: 247–250, proof `rfl`
- **Notes**: `@[simp]`

### `theorem jUnitLaurentSeriesMod_coeff_neg_one`
- **Type**: `(p : ℕ+) : (jUnitLaurentSeriesMod p).coeff (-1) = 1`
- **What**: The leading (pole) coefficient of `j mod p` at exponent `-1` is `1` — the pole survives reduction mod every `p`.
- **How**: Rewrites by `jUnitLaurentSeriesMod_coeff` and the project fact `jIntCoeff_neg_one : jIntCoeff (-1) = 1`.
- **Hypotheses**: none.
- **Uses from project**: [`jUnitLaurentSeriesMod`, `jUnitLaurentSeriesMod_coeff`, `jIntCoeff_neg_one`]
- **Used by**: `jUnitLaurentSeriesMod_order`
- **Visibility**: public
- **Lines**: 252–255, proof 2 lines
- **Notes**: none

### `theorem jUnitLaurentSeriesMod_coeff_eq_zero_of_lt`
- **Type**: `(p : ℕ+) {n : ℤ} (hn : n < -(1 : ℤ)) : (jUnitLaurentSeriesMod p).coeff n = 0`
- **What**: Coefficients of `j mod p` vanish below the simple pole at `-1`.
- **How**: Reduction mod `p` of the integral vanishing `jIntCoeff_eq_zero_of_lt`.
- **Hypotheses**: `n < -1`.
- **Uses from project**: [`jUnitLaurentSeriesMod`, `jUnitLaurentSeriesMod_coeff`, `jIntCoeff_eq_zero_of_lt`]
- **Used by**: `jUnitLaurentSeriesMod_order`
- **Visibility**: private
- **Lines**: 257–261, proof 2 lines
- **Notes**: none

### `theorem jUnitLaurentSeriesMod_order`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : (jUnitLaurentSeriesMod p).order = -1`
- **What**: The Hahn-series order of `j mod p` is exactly `-1`: `j` reduces to a series with a genuine simple pole in `𝔽_p((q))`.
- **How**: `HahnSeries.orderTop_eq_of_le` from the nonvanishing coefficient at `-1` (`jUnitLaurentSeriesMod_coeff_neg_one`) plus vanishing below (`jUnitLaurentSeriesMod_coeff_eq_zero_of_lt`); converted to `order` by `HahnSeries.order_eq_orderTop_of_ne_zero` with `HahnSeries.ne_zero_of_coeff_ne_zero`.
- **Hypotheses**: `p` prime (used only to get `1 < p`, so `ZMod p` is nontrivial and `1 ≠ 0`).
- **Uses from project**: [`jUnitLaurentSeriesMod`, `jUnitLaurentSeriesMod_coeff_neg_one`, `jUnitLaurentSeriesMod_coeff_eq_zero_of_lt`]
- **Used by**: `jUnitLaurentSeriesMod_pow_prime_normalForm`, `jUnitPrimeNormalForm_coeff_mul_of_lower`
- **Visibility**: private
- **Lines**: 263–280, proof 16 lines
- **Notes**: none

### `theorem powerSeries_pow_prime_eq_expand`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (F : PowerSeries (ZMod (p : ℕ))) : F ^ (p : ℕ) = F.expand (p : ℕ) (PNat.ne_zero p)`
- **What**: The freshman's dream for power series in characteristic `p`: raising a power series over `𝔽_p` to the `p`-th power equals substituting `q ↦ q^p` (Frobenius acts on `𝔽_p((q))` by expanding exponents).
- **How**: Instantiates mathlib's `MvPowerSeries.map_frobenius_expand` (`map frobenius (expand p F) = F^p`) at one variable, then observes that mapping by Frobenius is the identity on `ZMod p` coefficients by `ZMod.pow_card`.
- **Hypotheses**: `p` prime.
- **Uses from project**: []
- **Used by**: `jUnitLaurentSeriesMod_pow_prime_normalForm`
- **Visibility**: private
- **Lines**: 282–297, proof 14 lines
- **Notes**: none

### `def jLaurentSeriesMod`
- **Type**: `(p : ℕ+) → LaurentSeries (ZMod (p : ℕ))`
- **What**: The mod-`p` reduction of `j` written in the width-`p` parameter: coefficient at `k` is `jIntCoeff (k/p) mod p` when `p ∣ k` and `k ≥ -p`, else `0`. Its support lies in `pℤ`, and it will be identified with `(j mod p)^p`.
- **How**: A `HahnSeries` with the described piecewise coefficient function; support bounded below by `-p` from the `if`-condition, giving `isPWO` via `BddBelow.isWF`.
- **Hypotheses**: none.
- **Uses from project**: [`jIntCoeff`]
- **Used by**: `jLaurentSeriesMod_coeff`, `jIntegralLaurentSeriesWidth_map_zmod`, `jLaurentSeriesMod_coeff_neg_p`, `jLaurentSeriesMod_order`, `jLaurentSeriesMod_leadingCoeff`, `jUnitPrimeNormalForm_coeff_mul`, `jUnitPrimeNormalForm_coeff_of_not_dvd`, `jUnitLaurentSeriesMod_pow_prime`, `specializeJMod`, `specializeJMod_varY`, `specializeJIntegral_map_zmod`, `specializeJMod_injective`
- **Visibility**: public
- **Lines**: 299–311, definition with 9-line support proof
- **Notes**: none

### `theorem jLaurentSeriesMod_coeff`
- **Type**: `(p : ℕ+) (k : ℤ) : (jLaurentSeriesMod p).coeff k = if (p : ℤ) ∣ k ∧ -(p : ℤ) ≤ k then (jIntCoeff (k / (p : ℤ)) : ZMod (p : ℕ)) else 0`
- **What**: Coefficient-extraction rule for the width-`p` mod-`p` `j`-series.
- **How**: Definitional (`rfl`).
- **Hypotheses**: none.
- **Uses from project**: [`jLaurentSeriesMod`, `jIntCoeff`]
- **Used by**: `jIntegralLaurentSeriesWidth_map_zmod`, `jLaurentSeriesMod_coeff_neg_p`, `jLaurentSeriesMod_order`, `jUnitPrimeNormalForm_coeff_mul`, `jUnitPrimeNormalForm_coeff_of_not_dvd`
- **Visibility**: public
- **Lines**: 313–317, proof `rfl`
- **Notes**: none (not marked `@[simp]`, unlike the analogous coeff lemmas)

### `theorem jIntegralLaurentSeriesWidth_map_zmod`
- **Type**: `(p : ℕ+) : (jIntegralLaurentSeriesWidth p).map (Int.castRingHom (ZMod (p : ℕ))) = jLaurentSeriesMod p`
- **What**: Reducing the integral width-`p` `j`-series mod `p` gives the width-`p` series over `𝔽_p` — the two constructions of "`j` in the parameter `q_p`, mod `p`" agree.
- **How**: Coefficientwise: both sides are given by the same `if`-expression (via `jIntegralLaurentSeriesWidth_coeff` and `jLaurentSeriesMod_coeff`), with the cast `ℤ → ZMod p` commuting through both branches (`split_ifs <;> simp`).
- **Hypotheses**: none.
- **Uses from project**: [`jIntegralLaurentSeriesWidth`, `jIntegralLaurentSeriesWidth_coeff`, `jLaurentSeriesMod`, `jLaurentSeriesMod_coeff`]
- **Used by**: `specializeJIntegral_map_zmod`
- **Visibility**: public
- **Lines**: 319–328, proof 6 lines
- **Notes**: none

### `theorem jLaurentSeriesMod_coeff_neg_p`
- **Type**: `(p : ℕ+) : (jLaurentSeriesMod p).coeff (-(p : ℤ)) = 1`
- **What**: The lowest coefficient of the width-`p` series, at exponent `-p`, equals `1`.
- **How**: The `if`-condition holds at `k = -p` (`p ∣ -p` and `-p ≤ -p`); `(-p)/p = -1` is computed by `Int.ediv_eq_of_eq_mul_left`, and `jIntCoeff (-1) = 1` by `jIntCoeff_neg_one`.
- **Hypotheses**: none.
- **Uses from project**: [`jLaurentSeriesMod`, `jLaurentSeriesMod_coeff`, `jIntCoeff_neg_one`]
- **Used by**: `jLaurentSeriesMod_order`, `jLaurentSeriesMod_leadingCoeff`
- **Visibility**: private
- **Lines**: 330–337, proof 6 lines
- **Notes**: none

### `theorem jLaurentSeriesMod_order`
- **Type**: `(p : ℕ+) (hp : 1 < (p : ℕ)) : (jLaurentSeriesMod p).order = -(p : ℤ)`
- **What**: The width-`p` mod-`p` `j`-series has order exactly `-p`: a pole of order `p` in the width-`p` parameter.
- **How**: Same order machinery as `jUnitLaurentSeriesMod_order`: `HahnSeries.orderTop_eq_of_le` from the unit coefficient at `-p` (`jLaurentSeriesMod_coeff_neg_p`) and vanishing below `-p` (built into the `if`-condition), then `HahnSeries.order_eq_orderTop_of_ne_zero`.
- **Hypotheses**: `1 < p` (so `ZMod p` is nontrivial; stated with an explicit hypothesis rather than a primality instance).
- **Uses from project**: [`jLaurentSeriesMod`, `jLaurentSeriesMod_coeff`, `jLaurentSeriesMod_coeff_neg_p`]
- **Used by**: `jLaurentSeriesMod_leadingCoeff`, `specializeJMod_injective`
- **Visibility**: public
- **Lines**: 339–359, proof 19 lines
- **Notes**: none

### `theorem jLaurentSeriesMod_leadingCoeff`
- **Type**: `(p : ℕ+) (hp : 1 < (p : ℕ)) : (jLaurentSeriesMod p).leadingCoeff = 1`
- **What**: The width-`p` mod-`p` `j`-series has leading coefficient `1` (it is "monic at its pole").
- **How**: `HahnSeries.leadingCoeff_eq` reduces to the coefficient at the order, which is `-p` by `jLaurentSeriesMod_order`, and that coefficient is `1` by `jLaurentSeriesMod_coeff_neg_p`.
- **Hypotheses**: `1 < p`.
- **Uses from project**: [`jLaurentSeriesMod`, `jLaurentSeriesMod_order`, `jLaurentSeriesMod_coeff_neg_p`]
- **Used by**: `specializeJMod_injective`
- **Visibility**: public
- **Lines**: 361–364, proof 2 lines
- **Notes**: none

### `def jUnitLaurentSeriesModPrimeNormalForm`
- **Type**: `(p : ℕ+) → LaurentSeries (ZMod (p : ℕ))`
- **What**: A normal form for `(j mod p)^p`: the series `q^{-p} · (expand_p P)(q)` where `P` is the regular power-series part of `j mod p`. Auxiliary midpoint between `(j mod p)^p` and `jLaurentSeriesMod p`.
- **How**: `HahnSeries.single (-p) 1` times the coercion to Laurent series of `PowerSeries.expand` applied to `(jUnitLaurentSeriesMod p).powerSeriesPart`.
- **Hypotheses**: none.
- **Uses from project**: [`jUnitLaurentSeriesMod`]
- **Used by**: `jUnitLaurentSeriesMod_pow_prime_normalForm`, `jUnitPrimeNormalForm_coeff_mul_of_lower`, `jUnitPrimeNormalForm_coeff_mul_of_lt`, `jUnitPrimeNormalForm_coeff_mul`, `jUnitPrimeNormalForm_coeff_of_not_dvd`, `jUnitLaurentSeriesMod_pow_prime`
- **Visibility**: private
- **Lines**: 366–371, definition (6 lines)
- **Notes**: noncomputable

### `theorem jUnitLaurentSeriesMod_pow_prime_normalForm`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : jUnitLaurentSeriesMod p ^ (p : ℕ) = jUnitLaurentSeriesModPrimeNormalForm p`
- **What**: The `p`-th power of `j mod p` equals the normal form `q^{-p} · expand_p(P)`: the Frobenius power of a Laurent series with simple pole is its single-pole factor to the `p` times the expanded regular part.
- **How**: Decompose `F = q^{-1} · P` via `HahnSeries.single_order_mul_powerSeriesPart` (with `order = -1` from `jUnitLaurentSeriesMod_order`); raise to the `p` using `mul_pow` and `HahnSeries.single_pow` to get `q^{-p} · P^p`; identify `P^p` with `expand_p P` in characteristic `p` by `powerSeries_pow_prime_eq_expand`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`jUnitLaurentSeriesMod`, `jUnitLaurentSeriesModPrimeNormalForm`, `jUnitLaurentSeriesMod_order`, `powerSeries_pow_prime_eq_expand`]
- **Used by**: `jUnitLaurentSeriesMod_pow_prime`
- **Visibility**: private
- **Lines**: 373–403, proof 29 lines (calc chain)
- **Notes**: proof ~30 lines (calc with 4 steps)

### `theorem jUnitPrimeNormalForm_coeff_mul_of_lower`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (q : ℤ) (hq : -(1 : ℤ) ≤ q) : (jUnitLaurentSeriesModPrimeNormalForm p).coeff ((p : ℤ) * q) = (jIntCoeff q : ZMod (p : ℕ))`
- **What**: At an exponent `p·q` with `q ≥ -1`, the normal form's coefficient is `jIntCoeff q mod p` — expansion multiplies exponents by `p` without changing coefficients.
- **How**: `HahnSeries.coeff_single_mul` shifts the exponent by `p`; writing `pq + p = p·n` for `n = (q+1).toNat`, the expanded coefficient is read off with `PowerSeries.coeff_expand_mul` and `LaurentSeries.powerSeriesPart_coeff`, using `jUnitLaurentSeriesMod_order = -1` to relate the power-series part index back to `q`.
- **Hypotheses**: `p` prime; `q ≥ -1`.
- **Uses from project**: [`jUnitLaurentSeriesModPrimeNormalForm`, `jUnitLaurentSeriesMod_order`, `jUnitLaurentSeriesMod_coeff`, `jIntCoeff`]
- **Used by**: `jUnitPrimeNormalForm_coeff_mul`
- **Visibility**: private
- **Lines**: 405–426, proof 20 lines
- **Notes**: none

### `theorem jUnitPrimeNormalForm_coeff_mul_of_lt`
- **Type**: `(p : ℕ+) (q : ℤ) (hq : q < -(1 : ℤ)) : (jUnitLaurentSeriesModPrimeNormalForm p).coeff ((p : ℤ) * q) = 0`
- **What**: At an exponent `p·q` with `q < -1` (below the pole), the normal form's coefficient vanishes.
- **How**: After shifting by `HahnSeries.coeff_single_mul`, the index `p(q+1)` is negative, hence outside the range of the `ℕ → ℤ` embedding of the power-series part; `HahnSeries.embDomain_notin_range` gives `0`.
- **Hypotheses**: `q < -1`.
- **Uses from project**: [`jUnitLaurentSeriesModPrimeNormalForm`]
- **Used by**: `jUnitPrimeNormalForm_coeff_mul`
- **Visibility**: private
- **Lines**: 428–440, proof 11 lines
- **Notes**: none

### `theorem jUnitPrimeNormalForm_coeff_mul`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (q : ℤ) : (jUnitLaurentSeriesModPrimeNormalForm p).coeff ((p : ℤ) * q) = (jLaurentSeriesMod p).coeff ((p : ℤ) * q)`
- **What**: On exponents divisible by `p`, the normal form of `(j mod p)^p` agrees coefficientwise with the width-`p` series `jLaurentSeriesMod p`.
- **How**: Case split on `q ≥ -1`: in range, both sides equal `jIntCoeff q mod p` by `jUnitPrimeNormalForm_coeff_mul_of_lower` (with `Int.mul_ediv_cancel_left` to simplify `pq/p`); out of range, both vanish by `jUnitPrimeNormalForm_coeff_mul_of_lt` and the `if`-condition.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`jUnitLaurentSeriesModPrimeNormalForm`, `jLaurentSeriesMod`, `jLaurentSeriesMod_coeff`, `jUnitPrimeNormalForm_coeff_mul_of_lower`, `jUnitPrimeNormalForm_coeff_mul_of_lt`]
- **Used by**: `jUnitLaurentSeriesMod_pow_prime`
- **Visibility**: private
- **Lines**: 442–458, proof 15 lines
- **Notes**: none

### `theorem jUnitPrimeNormalForm_coeff_of_not_dvd`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] {k : ℤ} (hdiv : ¬(p : ℤ) ∣ k) : (jUnitLaurentSeriesModPrimeNormalForm p).coeff k = (jLaurentSeriesMod p).coeff k`
- **What**: On exponents not divisible by `p`, both the normal form and the width-`p` series have zero coefficient, so they agree.
- **How**: The right side is `0` by its `if`-condition; the left side is `0` because an expanded power series has support in `pℕ` (`PowerSeries.coeff_expand_of_not_dvd`), plus `HahnSeries.embDomain_notin_range` for negative shifted indices; a `Int.toNat` bookkeeping argument moves the divisibility obstruction across the shift by `p`.
- **Hypotheses**: `p` prime; `p ∤ k`.
- **Uses from project**: [`jUnitLaurentSeriesModPrimeNormalForm`, `jLaurentSeriesMod`, `jLaurentSeriesMod_coeff`]
- **Used by**: `jUnitLaurentSeriesMod_pow_prime`
- **Visibility**: private
- **Lines**: 460–480, proof 19 lines
- **Notes**: none

### `theorem jUnitLaurentSeriesMod_pow_prime`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : jUnitLaurentSeriesMod p ^ (p : ℕ) = jLaurentSeriesMod p`
- **What**: The key Frobenius identity: over `𝔽_p`, the `p`-th power of the unit-width `j`-series equals the width-`p` `j`-series, i.e. `j(q)^p = j(q^p) mod p` as formal Laurent series (the series form of Fermat/Frobenius on q-expansions).
- **How**: Rewrites the power as the normal form (`jUnitLaurentSeriesMod_pow_prime_normalForm`), then compares coefficients: exponents `pq` by `jUnitPrimeNormalForm_coeff_mul`, non-divisible exponents by `jUnitPrimeNormalForm_coeff_of_not_dvd`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`jUnitLaurentSeriesMod`, `jLaurentSeriesMod`, `jUnitLaurentSeriesMod_pow_prime_normalForm`, `jUnitPrimeNormalForm_coeff_mul`, `jUnitPrimeNormalForm_coeff_of_not_dvd`]
- **Used by**: unused in file (consumed by `KroneckerFrobenius.lean`)
- **Visibility**: public
- **Lines**: 482–490, proof 7 lines
- **Notes**: none

### `def specializeJMod`
- **Type**: `(p : ℕ+) : BivariatePolynomial (ZMod (p : ℕ)) →+* Polynomial (LaurentSeries (ZMod (p : ℕ)))`
- **What**: The ring homomorphism substituting the width-`p` mod-`p` `j`-series for the coefficient variable `Y` of a bivariate polynomial over `𝔽_p`, leaving `X` as a polynomial variable over `𝔽_p((q))`.
- **How**: Instance of the general specialization map `bivariateSpecializeLaurent` at the series `jLaurentSeriesMod p`.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial`, `bivariateSpecializeLaurent`, `jLaurentSeriesMod`]
- **Used by**: `specializeJMod_varX`, `specializeJMod_varY`, `specializeJIntegral_map_zmod`, `specializeJMod_injective`, `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 492–496, definition (5 lines)
- **Notes**: noncomputable

### `theorem specializeJMod_varX`
- **Type**: `(p : ℕ+) : specializeJMod p (BivariatePolynomial.varX : BivariatePolynomial (ZMod (p : ℕ))) = Polynomial.X`
- **What**: The specialization sends the outer variable `X` to the polynomial variable `X`.
- **How**: Unfolds `specializeJMod`, `bivariateSpecializeLaurent`, and `BivariatePolynomial.varX` by `simp`.
- **Hypotheses**: none.
- **Uses from project**: [`specializeJMod`, `bivariateSpecializeLaurent`, `BivariatePolynomial.varX`, `BivariatePolynomial`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 498–503, proof 1 line
- **Notes**: `@[simp]`

### `theorem specializeJMod_varY`
- **Type**: `(p : ℕ+) : specializeJMod p (BivariatePolynomial.varY : BivariatePolynomial (ZMod (p : ℕ))) = Polynomial.C (jLaurentSeriesMod p)`
- **What**: The specialization sends the coefficient variable `Y` to the constant polynomial with value the width-`p` `j`-series.
- **How**: Unfolds `specializeJMod`, `bivariateSpecializeLaurent`, and `BivariatePolynomial.varY` by `simp`.
- **Hypotheses**: none.
- **Uses from project**: [`specializeJMod`, `bivariateSpecializeLaurent`, `BivariatePolynomial.varY`, `BivariatePolynomial`, `jLaurentSeriesMod`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 505–510, proof 1 line
- **Notes**: `@[simp]`

### `def specializeJIntegral`
- **Type**: `(m : ℕ+) : BivariatePolynomial ℤ →+* Polynomial (LaurentSeries ℤ)`
- **What**: The integral analogue of `specializeJMod`: substitute the integral width-`m` expansion of `j` for the variable `Y` of an integer bivariate polynomial.
- **How**: Instance of `bivariateSpecializeLaurent` at `jIntegralLaurentSeriesWidth m`.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial`, `bivariateSpecializeLaurent`, `jIntegralLaurentSeriesWidth`]
- **Used by**: `specializeJIntegral_map_zmod`, `specializeJIntegral_map_complex`, `specializeJIntegral_modularPolynomial_map_complex`, `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 512–515, definition (4 lines)
- **Notes**: none

### `theorem specializeJIntegral_map_zmod`
- **Type**: `(p : ℕ+) (F : BivariatePolynomial ℤ) : (specializeJIntegral p F).map (laurentSeriesMapRingHom (Int.castRingHom (ZMod (p : ℕ)))) = specializeJMod p (BivariatePolynomial.map (Int.castRingHom (ZMod (p : ℕ))) F)`
- **What**: Reduction mod `p` commutes with `j`-specialization: reducing the integral specialization of `F` coefficientwise equals specializing the mod-`p` reduction of `F` at the mod-`p` series.
- **How**: The general naturality lemma `bivariateSpecializeLaurent_map_apply` for the base-change `ℤ → ZMod p`, whose series-compatibility hypothesis is exactly `jIntegralLaurentSeriesWidth_map_zmod`.
- **Hypotheses**: none (works for all `p : ℕ+`).
- **Uses from project**: [`specializeJIntegral`, `specializeJMod`, `laurentSeriesMapRingHom`, `BivariatePolynomial.map`, `BivariatePolynomial`, `jIntegralLaurentSeriesWidth`, `jLaurentSeriesMod`, `jIntegralLaurentSeriesWidth_map_zmod`, `bivariateSpecializeLaurent_map_apply`]
- **Used by**: `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 517–529, proof 10 lines
- **Notes**: none

### `theorem specializeJIntegral_map_complex`
- **Type**: `(m : ℕ+) (F : BivariatePolynomial ℤ) : (specializeJIntegral m F).map (laurentSeriesMapRingHom (Int.castRingHom ℂ)) = Polynomial.map (Polynomial.eval₂RingHom HahnSeries.C (laurentqExpansion ((m : ℕ) : ℝ) j)) (BivariatePolynomial.map (Int.castRingHom ℂ) F)`
- **What**: Base-changing the integral specialization to `ℂ` yields specialization of the complexified polynomial at the analytic width-`m` Laurent expansion of `j`.
- **How**: Again the naturality lemma `bivariateSpecializeLaurent_map_apply`, now along `ℤ → ℂ`, with compatibility supplied by `jIntegralLaurentSeriesWidth_map_complex`.
- **Hypotheses**: none.
- **Uses from project**: [`specializeJIntegral`, `laurentSeriesMapRingHom`, `laurentqExpansion`, `j`, `BivariatePolynomial.map`, `BivariatePolynomial`, `bivariateSpecializeLaurent`, `jIntegralLaurentSeriesWidth`, `jIntegralLaurentSeriesWidth_map_complex`, `bivariateSpecializeLaurent_map_apply`]
- **Used by**: `specializeJIntegral_modularPolynomial_map_complex`
- **Visibility**: public
- **Lines**: 531–548, proof 9 lines
- **Notes**: none

### `theorem specializeJIntegral_modularPolynomial_map_complex`
- **Type**: `(m : ℕ+) : (specializeJIntegral m (modularPolynomial m)).map (laurentSeriesMapRingHom (Int.castRingHom ℂ)) = formalCoxPolynomial m (zeta m)`
- **What**: The complexification of the integrally specialized modular polynomial `Φ_m(X, j)` equals the formal Cox product `∏_σ (X − j∘σ)` (as a polynomial over complex Laurent series) at the primitive root `ζ_m`.
- **How**: Chains `specializeJIntegral_map_complex` with the defining property `modularPolynomial_map_complex` and the identity `formalCoxPolynomial_eq_modularPolynomialC_map_j` relating the Cox product to the specialized complex modular polynomial.
- **Hypotheses**: none.
- **Uses from project**: [`specializeJIntegral`, `modularPolynomial`, `laurentSeriesMapRingHom`, `formalCoxPolynomial`, `zeta`, `specializeJIntegral_map_complex`, `modularPolynomial_map_complex`, `formalCoxPolynomial_eq_modularPolynomialC_map_j`]
- **Used by**: `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 550–557, proof 3 lines
- **Notes**: none

### `theorem specializeJMod_injective`
- **Type**: `(p : ℕ+) [hp : Fact (Nat.Prime (p : ℕ))] : Function.Injective (specializeJMod p)`
- **What**: Cox Exercise 11.15 mod `p` (Hasse q-expansion principle): a bivariate polynomial over `𝔽_p` is determined by its specialization at the width-`p` `j`-series — evaluation at `j` is injective on coefficient polynomials.
- **How**: `Polynomial.map_injective` reduces to injectivity of `Y ↦ jLaurentSeriesMod p` on `𝔽_p[Y]`, which is the general project lemma `polynomial_eval₂_laurentSeries_injective` applied with the order `-p` (`jLaurentSeriesMod_order`) and unit leading coefficient (`jLaurentSeriesMod_leadingCoeff`) — a series with a genuine pole of exact order `p` and invertible leading coefficient is transcendental-enough for polynomial evaluation to be injective.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`specializeJMod`, `polynomial_eval₂_laurentSeries_injective`, `jLaurentSeriesMod`, `jLaurentSeriesMod_order`, `jLaurentSeriesMod_leadingCoeff`]
- **Used by**: unused in file (consumed by `KroneckerFrobenius.lean`)
- **Visibility**: public
- **Lines**: 559–567, proof 6 lines
- **Notes**: none

### `def phasePolynomial`
- **Type**: `(p : ℕ+) (e : ℤ) : Polynomial ℤ`
- **What**: An integral polynomial lift `T^{e mod p}` of the root-of-unity power `ζ_p^e`: evaluating at `T = ζ_p` recovers `ζ_p^e`, and reducing at `T = 1` gives `1`.
- **How**: `Polynomial.X ^ (e % p).toNat`, using the nonnegative remainder of `e` mod `p`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `phasePolynomial_eval_zeta`, `phasePolynomial_eval_one`, `cyclotomicTransformedJSeries`, `cyclotomicTransformedJSeries_coeff`
- **Visibility**: public
- **Lines**: 569–571, definition (2 lines)
- **Notes**: none

### `theorem phasePolynomial_eval_zeta`
- **Type**: `(p : ℕ+) (e : ℤ) : Polynomial.eval₂ (Int.castRingHom ℂ) (zeta p) (phasePolynomial p e) = zeta p ^ e`
- **What**: Evaluating the phase lift at the primitive `p`-th root of unity gives the integer-power `ζ_p^e` (with `zpow`).
- **How**: Since `ζ_p` has order dividing `p` (from `zeta_isPrimitiveRoot`, promoted to a unit of `ℂ`), `ζ_p^e = ζ_p^{e mod p}` by `zpow_eq_zpow_emod'`; the `toNat` conversion is justified by `Int.emod_nonneg`.
- **Hypotheses**: none (works for all `e : ℤ`).
- **Uses from project**: [`phasePolynomial`, `zeta`, `zeta_isPrimitiveRoot`]
- **Used by**: `cyclotomicTransformedJSeries_map_complex`
- **Visibility**: private
- **Lines**: 573–586, proof 12 lines
- **Notes**: none

### `theorem phasePolynomial_eval_one`
- **Type**: `(p : ℕ+) (e : ℤ) : Polynomial.eval₂ (Int.castRingHom (ZMod (p : ℕ))) 1 (phasePolynomial p e) = 1`
- **What**: Setting the phase variable to `1` (over `ZMod p`) kills the phase: the polynomial `T^{e mod p}` evaluates to `1`.
- **How**: `1^n = 1`; discharged by `simp` on the definition.
- **Hypotheses**: none.
- **Uses from project**: [`phasePolynomial`]
- **Used by**: `cyclotomicTransformedJSeries_map_mod`
- **Visibility**: private
- **Lines**: 588–591, proof 1 line
- **Notes**: none

### `def cyclotomicTransformedJSeries`
- **Type**: `(p : ℕ+) (σ : CoxMatrix p) : LaurentSeries (Polynomial ℤ)`
- **What**: The integral cyclotomic lift of the transformed series `j∘σ`: a Laurent series with coefficients in `ℤ[T]`, with coefficient at `k = a²·q` equal to `jIntCoeff(q) · T^{abq mod p}` — the phase `ζ^{abq}` is kept as a formal variable so the series specializes both to `ℂ` (at `T = ζ_p`) and to `ZMod p` (at `T = 1`).
- **How**: A `HahnSeries` whose coefficient at `k` is `C (jIntCoeff (k/a²)) * phasePolynomial p (ab·(k/a²))` when `a² ∣ k` and `k ≥ -a²`, else `0`; support bounded below by `-a²` gives `isPWO` via `BddBelow.isWF`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix`, `jIntCoeff`, `phasePolynomial`]
- **Used by**: `cyclotomicTransformedJSeries_coeff`, `cyclotomicTransformedJSeries_map_complex`, `cyclotomicTransformedJSeries_map_mod`, `cyclotomicCoxPolynomial`
- **Visibility**: public
- **Lines**: 593–609, definition with 8-line support proof
- **Notes**: noncomputable; defined by anonymous-constructor syntax rather than `where`

### `theorem cyclotomicTransformedJSeries_coeff`
- **Type**: `(p : ℕ+) (σ : CoxMatrix p) (k : ℤ) : (cyclotomicTransformedJSeries p σ).coeff k = if (σ.a : ℤ)^2 ∣ k ∧ -((σ.a : ℤ)^2) ≤ k then Polynomial.C (jIntCoeff (k / (σ.a : ℤ)^2)) * phasePolynomial p ((σ.a * σ.b) * (k / (σ.a : ℤ)^2)) else 0`
- **What**: Coefficient-extraction rule for the cyclotomic lift of `j∘σ`.
- **How**: Definitional (`rfl`).
- **Hypotheses**: none.
- **Uses from project**: [`cyclotomicTransformedJSeries`, `CoxMatrix`, `jIntCoeff`, `phasePolynomial`]
- **Used by**: `cyclotomicTransformedJSeries_map_complex`, `cyclotomicTransformedJSeries_map_mod`
- **Visibility**: public
- **Lines**: 611–619, proof `rfl`
- **Notes**: none

### `def phaseEvalComplex`
- **Type**: `(p : ℕ+) : Polynomial ℤ →+* ℂ`
- **What**: The ring homomorphism `ℤ[T] → ℂ` evaluating the phase variable at the primitive root `ζ_p` (and casting integer coefficients).
- **How**: `Polynomial.eval₂RingHom (Int.castRingHom ℂ) (zeta p)`.
- **Hypotheses**: none.
- **Uses from project**: [`zeta`]
- **Used by**: `cyclotomicTransformedJSeries_map_complex`, `cyclotomicCoxPolynomial_map_complex`, `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 621–623, definition (2 lines)
- **Notes**: none

### `def phaseEvalMod`
- **Type**: `(p : ℕ+) : Polynomial ℤ →+* ZMod (p : ℕ)`
- **What**: The ring homomorphism `ℤ[T] → 𝔽_p` reducing coefficients mod `p` and setting the phase variable to `1`.
- **How**: `Polynomial.eval₂RingHom (Int.castRingHom (ZMod p)) 1`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `cyclotomicTransformedJSeries_map_mod`, `cyclotomicCoxPolynomial_map_mod`
- **Visibility**: public
- **Lines**: 625–627, definition (2 lines)
- **Notes**: none

### `theorem cyclotomicTransformedJSeries_map_complex`
- **Type**: `(p : ℕ+) (σ : CoxMatrix p) : laurentSeriesMapRingHom (phaseEvalComplex p) (cyclotomicTransformedJSeries p σ) = transformedJSeries (zeta p) σ`
- **What**: Evaluating the phase at `ζ_p` recovers the analytic transformed `j`-series `j∘σ` (with root-of-unity phases) — the cyclotomic lift is a genuine lift of the complex object.
- **How**: Coefficientwise: in the nonzero branch, `Polynomial.eval₂_C` handles the constant factor and `phasePolynomial_eval_zeta` turns `T^{abq mod p}` into `ζ_p^{abq}`, matching `transformedJSeries_coeff`.
- **Hypotheses**: none.
- **Uses from project**: [`cyclotomicTransformedJSeries`, `cyclotomicTransformedJSeries_coeff`, `laurentSeriesMapRingHom`, `laurentSeriesMapRingHom_coeff`, `phaseEvalComplex`, `transformedJSeries`, `transformedJSeries_coeff`, `zeta`, `phasePolynomial`, `phasePolynomial_eval_zeta`, `jIntCoeff`, `CoxMatrix`]
- **Used by**: `cyclotomicCoxPolynomial_map_complex`
- **Visibility**: public
- **Lines**: 629–646, proof 16 lines
- **Notes**: none

### `theorem cyclotomicTransformedJSeries_map_mod`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (σ : CoxMatrix p) : laurentSeriesMapRingHom (phaseEvalMod p) (cyclotomicTransformedJSeries p σ) = transformedJSeries (1 : ZMod (p : ℕ)) σ`
- **What**: Reducing the cyclotomic lift mod `p` with phase set to `1` recovers the phase-one transformed series over `𝔽_p` — the mod-`p` shadow in which all root-of-unity phases collapse.
- **How**: Coefficientwise, mirroring the complex case: `Polynomial.eval₂_C` plus `phasePolynomial_eval_one` (phases become `1`), matching `transformedJSeries_coeff` at phase `1`.
- **Hypotheses**: `p` prime (instance; used for the `ZMod p` ring structure side conditions).
- **Uses from project**: [`cyclotomicTransformedJSeries`, `cyclotomicTransformedJSeries_coeff`, `laurentSeriesMapRingHom`, `laurentSeriesMapRingHom_coeff`, `phaseEvalMod`, `transformedJSeries`, `transformedJSeries_coeff`, `phasePolynomial`, `phasePolynomial_eval_one`, `jIntCoeff`, `CoxMatrix`]
- **Used by**: `cyclotomicCoxPolynomial_map_mod`
- **Visibility**: public
- **Lines**: 648–665, proof 16 lines
- **Notes**: none

### `def cyclotomicCoxPolynomial`
- **Type**: `(p : ℕ+) : Polynomial (LaurentSeries (Polynomial ℤ))`
- **What**: The integral cyclotomic lift of the Cox product: `∏_{σ} (X − (cyclotomic lift of j∘σ))` over all prime-level Cox matrices, with coefficients Laurent series over `ℤ[T]`.
- **How**: Finite product over the `Fintype` of `CoxMatrix p` of the linear factors `X − C(cyclotomicTransformedJSeries p σ)`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix`, `cyclotomicTransformedJSeries`]
- **Used by**: `cyclotomicCoxPolynomial_map_complex`, `cyclotomicCoxPolynomial_map_mod`, `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 667–671, definition (5 lines)
- **Notes**: noncomputable

### `theorem cyclotomicCoxPolynomial_map_complex`
- **Type**: `(p : ℕ+) : (cyclotomicCoxPolynomial p).map (laurentSeriesMapRingHom (phaseEvalComplex p)) = formalCoxPolynomial p (zeta p)`
- **What**: Evaluating the phase at `ζ_p` in the integral cyclotomic Cox product yields the analytic formal Cox product `∏_σ (X − j∘σ)` at `ζ_p`.
- **How**: `Polynomial.map_prod` pushes the ring map through the finite product; each factor is handled by `cyclotomicTransformedJSeries_map_complex`.
- **Hypotheses**: none.
- **Uses from project**: [`cyclotomicCoxPolynomial`, `laurentSeriesMapRingHom`, `phaseEvalComplex`, `formalCoxPolynomial`, `zeta`, `cyclotomicTransformedJSeries_map_complex`]
- **Used by**: `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 673–679, proof 4 lines
- **Notes**: none

### `theorem cyclotomicCoxPolynomial_map_mod`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : (cyclotomicCoxPolynomial p).map (laurentSeriesMapRingHom (phaseEvalMod p)) = formalCoxPolynomial p (1 : ZMod (p : ℕ))`
- **What**: Reducing the integral cyclotomic Cox product mod `p` with phase `1` yields the phase-one formal Cox product over `𝔽_p`.
- **How**: `Polynomial.map_prod` through the product; each factor by `cyclotomicTransformedJSeries_map_mod`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`cyclotomicCoxPolynomial`, `laurentSeriesMapRingHom`, `phaseEvalMod`, `formalCoxPolynomial`, `cyclotomicTransformedJSeries_map_mod`]
- **Used by**: `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 681–688, proof 4 lines
- **Notes**: none

### `theorem cyclotomicDescent_dvd`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (F : Polynomial ℤ) (z : ℤ) (hF : Polynomial.eval₂ (Int.castRingHom ℂ) (zeta p) F = (z : ℂ)) : (p : ℤ) ∣ F.eval 1 - z`
- **What**: Cox Exercise 11.13: if an integer polynomial takes the integer value `z` at `ζ_p`, then its value at `1` is congruent to `z` mod `p` — the arithmetic heart of the cyclotomic descent (using `Φ_p(1) = p`).
- **How**: `F − z` vanishes at `ζ_p`, so over `ℚ` it is divisible by the minimal polynomial of `ζ_p`, which is `Φ_p` (`Polynomial.cyclotomic_eq_minpoly_rat` with `zeta_isPrimitiveRoot`, plus `minpoly.dvd`); Gauss descent to `ℤ` via `Polynomial.map_dvd_map` with `Polynomial.cyclotomic.monic`; evaluating the divisibility at `1` and using `Polynomial.eval_one_cyclotomic_prime` (`Φ_p(1) = p`) gives `p ∣ F(1) − z`.
- **Hypotheses**: `p` prime; `F(ζ_p) = z` with `z ∈ ℤ`.
- **Uses from project**: [`zeta`, `zeta_isPrimitiveRoot`]
- **Used by**: `cyclotomicDescent_zmod`
- **Visibility**: public
- **Lines**: 690–716, proof 25 lines
- **Notes**: none

### `theorem cyclotomicDescent_zmod`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (F : Polynomial ℤ) (z : ℤ) (hF : Polynomial.eval₂ (Int.castRingHom ℂ) (zeta p) F = (z : ℂ)) : ((F.eval 1 : ℤ) : ZMod (p : ℕ)) = (z : ZMod (p : ℕ))`
- **What**: Exercise 11.13 in reduction form: under the same hypothesis, `F(1)` and `z` have the same image in `𝔽_p`.
- **How**: `ZMod.intCast_eq_intCast_iff_dvd_sub` converts the divisibility from `cyclotomicDescent_dvd` into equality of residues.
- **Hypotheses**: `p` prime; `F(ζ_p) = z`, `z ∈ ℤ`.
- **Uses from project**: [`zeta`, `cyclotomicDescent_dvd`]
- **Used by**: `cyclotomicDescent_polynomialLaurentSeries`
- **Visibility**: public
- **Lines**: 718–724, proof 3 lines
- **Notes**: none

### `theorem cyclotomicDescent_polynomialLaurentSeries`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (A : Polynomial (LaurentSeries (Polynomial ℤ))) (B : Polynomial (LaurentSeries ℤ)) (h : A.map (laurentSeriesMapRingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (zeta p))) = B.map (laurentSeriesMapRingHom (Int.castRingHom ℂ))) : A.map (laurentSeriesMapRingHom (Polynomial.eval₂RingHom (Int.castRingHom (ZMod (p : ℕ))) 1)) = B.map (laurentSeriesMapRingHom (Int.castRingHom (ZMod (p : ℕ))))`
- **What**: Coefficientwise Exercise 11.13 for polynomials over Laurent series: if a cyclotomic-lifted object `A` agrees with an integral object `B` after phase-evaluation at `ζ_p` over `ℂ`, then it agrees with `B` mod `p` after setting the phase to `1`. This is the descent engine turning one complex identity into a mod-`p` identity.
- **How**: Reduces to a single Laurent coefficient of a single polynomial coefficient — a pair `(F, z)` with `F(ζ_p) = z` — extracted from `h` by `congrArg`; each such pair is exactly the hypothesis of `cyclotomicDescent_zmod`, applied via `Polynomial.eval₂_at_apply`.
- **Hypotheses**: `p` prime; the complex-phase identity `h`.
- **Uses from project**: [`laurentSeriesMapRingHom`, `laurentSeriesMapRingHom_coeff`, `zeta`, `cyclotomicDescent_zmod`]
- **Used by**: `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 726–755, proof 22 lines
- **Notes**: none

### `theorem specializeJMod_modularPolynomial_eq_formal`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] : specializeJMod p (BivariatePolynomial.map (Int.castRingHom (ZMod (p : ℕ))) (modularPolynomial p)) = formalCoxPolynomial p (1 : ZMod (p : ℕ))`
- **What**: The main result of the file: the mod-`p` modular polynomial specialized at the width-`p` `j`-series equals the phase-one formal Cox product `∏_σ (X − (j∘σ at phase 1))` over `𝔽_p`. This is the series-level identity behind Kronecker's congruence.
- **How**: Sets `A` = cyclotomic Cox product and `B` = integral specialization of `Φ_p`; over `ℂ` they agree by `cyclotomicCoxPolynomial_map_complex` and `specializeJIntegral_modularPolynomial_map_complex`; the descent `cyclotomicDescent_polynomialLaurentSeries` transfers this to `ZMod p` with phase `1`; a `calc` chain rewrites both ends via `specializeJIntegral_map_zmod` and `cyclotomicCoxPolynomial_map_mod`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`specializeJMod`, `BivariatePolynomial.map`, `modularPolynomial`, `formalCoxPolynomial`, `cyclotomicCoxPolynomial`, `specializeJIntegral`, `laurentSeriesMapRingHom`, `zeta`, `phaseEvalComplex`, `cyclotomicCoxPolynomial_map_complex`, `specializeJIntegral_modularPolynomial_map_complex`, `cyclotomicDescent_polynomialLaurentSeries`, `specializeJIntegral_map_zmod`, `cyclotomicCoxPolynomial_map_mod`]
- **Used by**: unused in file (consumed by `KroneckerFrobenius.lean`)
- **Visibility**: public
- **Lines**: 757–792, proof 33 lines
- **Notes**: proof >30 lines (33)

---

### File Summary
- Total declarations: 63 (16 defs, 47 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): `primeLowerCoxMatrix`, `primeFinToCoxMatrix`, `primeFinToCoxMatrix_castSucc`, `primeFinToCoxMatrix_last`, `primeFinEquivCoxMatrix`, `jIntCoeff_eq_zero_of_lt`, `jIntegralLaurentSeries`, `jIntegralLaurentSeriesWidth`, `jUnitLaurentSeriesMod`, `jUnitLaurentSeriesMod_coeff`, `jLaurentSeriesMod`, `jLaurentSeriesMod_coeff`, `jUnitLaurentSeriesModPrimeNormalForm`, `specializeJMod`, `specializeJIntegral`, `phasePolynomial`, `cyclotomicTransformedJSeries`, `phaseEvalComplex`, `cyclotomicCoxPolynomial`
- Unused declarations (not used by anything in this file): `primeCoxMatrixEquiv_symm_apply_of_lt`, `primeCoxMatrixEquiv_symm_apply_last`, `jIntegralLaurentSeries_coeff`, `jIntegralLaurentSeries_map_complex`, `specializeJMod_varX`, `specializeJMod_varY`, `jUnitLaurentSeriesMod_pow_prime`, `specializeJMod_injective`, `specializeJMod_modularPolynomial_eq_formal` (the last three are the file's exports, consumed in `KroneckerFrobenius.lean`)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `specializeJMod_modularPolynomial_eq_formal` (33 lines; lines 757–792)
