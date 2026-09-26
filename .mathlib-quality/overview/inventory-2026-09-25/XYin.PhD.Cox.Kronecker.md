# Inventory: XYin/PhD/Cox/Kronecker.lean  (771 lines)

Infrastructure for Cox Theorem 11.18(v): (i) enumeration of the prime-level Cox representatives `(1,i;0,p)`, `(p,0;0,1)` as `CoxMatrix p ≃ Fin (p+1)`; (ii) integral and mod-`p` Laurent series of `j` at widths `1` and `m`/`p`, with `(j mod p)^p = j` at width `p` via `PowerSeries.expand`/Frobenius; (iii) the specialisation homs `specializeJIntegral m`, `specializeJMod p` (`Y ↦ j`-series) and their compatibility with base change to ℂ and to `ZMod p`, plus injectivity of `specializeJMod` (Exercise 11.15); (iv) an integral cyclotomic lift of the Cox product over `ℤ[X]` and the descent `ζ_p ↦ 1 (mod p)` (Exercise 11.13), culminating in `specializeJMod p (Φ_p mod p) = formalCoxPolynomial p 1`. The Frobenius factorisation is finished in KroneckerFrobenius.lean.

## Declarations

### `def Cox.primeLowerCoxMatrix`
- **Type**: `(p : ℕ+) (i : Fin (p : ℕ)) : CoxMatrix p`
- **What**: The Cox representative `(1, i; 0, p)`.
- **How**: structure literal with `a = 1, b = i, d = p`; `primitive` by `simp`.
- **Hypotheses**: none (any `p : ℕ+`).
- **Uses from project**: `CoxMatrix`
- **Used by**: `primeFinToCoxMatrix`, `primeFinToCoxMatrix_castSucc`, `primeFinToCoxMatrix_surjective`, `primeFinToCoxMatrix_injective`, `primeFinEquivCoxMatrix_apply_of_lt`, `primeCoxMatrixEquiv_symm_apply_of_lt`
- **Visibility**: public
- **Lines**: 32–39
- **Notes**: no other `a = 1` constructor in the project (grep `a := 1`); `sigmaZero` (CoxMatrices/Basic.lean:113) is its dual.

### `def Cox.primeFinToCoxMatrix` (private)
- **Type**: `(p : ℕ+) : Fin ((p : ℕ) + 1) → CoxMatrix p`
- **What**: `i ↦ (1,i;0,p)` for `i < p`, `last ↦ σ₀ = (p,0;0,1)`.
- **How**: `Fin.lastCases (sigmaZero p) (primeLowerCoxMatrix p)`.
- **Hypotheses**: none.
- **Uses from project**: `sigmaZero`, `primeLowerCoxMatrix`
- **Used by**: `primeFinToCoxMatrix_castSucc`, `_last`, `_surjective`, `_injective`, `primeFinEquivCoxMatrix`, `primeFinEquivCoxMatrix_apply_of_lt`, `_apply_last`
- **Visibility**: private
- **Lines**: 41–42
- **Notes**: none.

### `theorem Cox.primeFinToCoxMatrix_castSucc` (private)
- **Type**: `(p) (i : Fin p) : primeFinToCoxMatrix p i.castSucc = primeLowerCoxMatrix p i`
- **What**: Evaluation on non-last indices.
- **How**: `simp [primeFinToCoxMatrix]` (`Fin.lastCases_castSucc`).
- **Hypotheses**: none.
- **Uses from project**: `primeFinToCoxMatrix`, `primeLowerCoxMatrix`
- **Used by**: `primeFinToCoxMatrix_surjective`, `_injective`, `primeFinEquivCoxMatrix_apply_of_lt`
- **Visibility**: private
- **Lines**: 45–47, proof 1 line
- **Notes**: `@[simp]`.

### `theorem Cox.primeFinToCoxMatrix_last` (private)
- **Type**: `(p) : primeFinToCoxMatrix p (Fin.last p) = sigmaZero p`
- **What**: Evaluation at the last index.
- **How**: `simp [primeFinToCoxMatrix]`.
- **Hypotheses**: none.
- **Uses from project**: `primeFinToCoxMatrix`, `sigmaZero`
- **Used by**: `primeFinToCoxMatrix_surjective`, `_injective`, `primeFinEquivCoxMatrix_apply_last`
- **Visibility**: private
- **Lines**: 50–52, proof 1 line
- **Notes**: `@[simp]`.

### `theorem Cox.primeFinToCoxMatrix_surjective` (private)
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : Function.Surjective (primeFinToCoxMatrix p)`
- **What**: Every Cox matrix of prime level is one of the `p + 1` listed ones.
- **How**: `σ.a ∣ p` (from `determinant`), so `Nat.Prime.eq_one_or_self_of_dvd` gives `a = 1` (then `d = p`, `b < p`, hit by `i.castSucc`) or `a = p` (then `d = 1`, `b = 0` by `b_lt`, hit by `Fin.last`); equalities via `CoxMatrix.toFin_injective` + `simp [CoxMatrix.toFin]`.
- **Hypotheses**: `p` prime.
- **Uses from project**: `primeFinToCoxMatrix`, `CoxMatrix` (fields `a b d determinant b_lt`), `CoxMatrix.toFin`, `CoxMatrix.toFin_injective`, `primeLowerCoxMatrix`, `sigmaZero`, `primeFinToCoxMatrix_castSucc`, `primeFinToCoxMatrix_last`
- **Used by**: `primeFinEquivCoxMatrix`
- **Visibility**: private
- **Lines**: 54–79, proof ≈ 23 lines
- **Notes**: `nlinarith` at 72 for `d = 1` from `p * d = p`.

### `theorem Cox.primeFinToCoxMatrix_injective` (private)
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : Function.Injective (primeFinToCoxMatrix p)`
- **What**: The listed representatives are pairwise distinct.
- **How**: `Fin.eq_castSucc_or_eq_last` (Data/Fin/SuccPred.lean:195) on both indices; two lower ones agree only if their `b` fields agree; a lower and `σ₀` differ in `a` (`1 ≠ p` by `Nat.Prime.ne_one`).
- **Hypotheses**: `p` prime.
- **Uses from project**: `primeFinToCoxMatrix`, `CoxMatrix` (fields), `primeLowerCoxMatrix`, `sigmaZero`, `primeFinToCoxMatrix_castSucc`, `_last`
- **Used by**: `primeFinEquivCoxMatrix`
- **Visibility**: private
- **Lines**: 81–103, proof ≈ 19 lines
- **Notes**: the two `exfalso` branches (90–95, 97–102) are mirror images.

### `def Cox.primeFinEquivCoxMatrix` (private)
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : Fin ((p : ℕ) + 1) ≃ CoxMatrix p`
- **What**: The bijection `Fin (p+1) ≃ CoxMatrix p`.
- **How**: `Equiv.ofBijective` from the two lemmas.
- **Hypotheses**: `p` prime.
- **Uses from project**: `primeFinToCoxMatrix`, `primeFinToCoxMatrix_injective`, `primeFinToCoxMatrix_surjective`
- **Used by**: `primeFinEquivCoxMatrix_apply_of_lt`, `_apply_last`, `primeCoxMatrixEquiv`
- **Visibility**: private
- **Lines**: 105–109
- **Notes**: `noncomputable`.

### `theorem Cox.primeFinEquivCoxMatrix_apply_of_lt` (private)
- **Type**: `(p) [Fact (Nat.Prime p)] (i : Fin (p+1)) (hi : (i : ℕ) < p) : primeFinEquivCoxMatrix p i = primeLowerCoxMatrix p ⟨i, hi⟩`
- **What**: Forward evaluation below the last index.
- **How**: rewrite `i = ⟨i,hi⟩.castSucc` (`Fin.ext rfl`) and `primeFinToCoxMatrix_castSucc`.
- **Hypotheses**: `i < p`.
- **Uses from project**: `primeFinEquivCoxMatrix`, `primeFinToCoxMatrix`, `primeLowerCoxMatrix`, `primeFinToCoxMatrix_castSucc`
- **Used by**: `primeCoxMatrixEquiv_symm_apply_of_lt`
- **Visibility**: private
- **Lines**: 112–119, proof ≈ 4 lines
- **Notes**: `@[simp]`.

### `theorem Cox.primeFinEquivCoxMatrix_apply_last` (private)
- **Type**: `(p) [Fact (Nat.Prime p)] : primeFinEquivCoxMatrix p (Fin.last p) = sigmaZero p`
- **What**: Forward evaluation at the last index.
- **How**: `change` + `primeFinToCoxMatrix_last`.
- **Hypotheses**: `p` prime.
- **Uses from project**: `primeFinEquivCoxMatrix`, `primeFinToCoxMatrix`, `sigmaZero`, `primeFinToCoxMatrix_last`
- **Used by**: `primeCoxMatrixEquiv_symm_apply_last`
- **Visibility**: private
- **Lines**: 122–126, proof 2 lines
- **Notes**: `@[simp]`.

### `def Cox.primeCoxMatrixEquiv`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : CoxMatrix p ≃ Fin ((p : ℕ) + 1)`
- **What**: Cox's prime-level representatives, as an equivalence in the direction `CoxMatrix p → Fin (p+1)`.
- **How**: `(primeFinEquivCoxMatrix p).symm`.
- **Hypotheses**: `p` prime.
- **Uses from project**: `primeFinEquivCoxMatrix`
- **Used by**: `primeCoxMatrixEquiv_symm_apply_of_lt`, `_symm_apply_last`
- **Visibility**: public
- **Lines**: 130–133
- **Notes**: `noncomputable`. Cross-file: KroneckerFrobenius.lean:51, LevelThree.lean. Only ever used through `.symm`; exposing `primeFinEquivCoxMatrix` directly would avoid the double `symm`.

### `theorem Cox.primeCoxMatrixEquiv_symm_apply_of_lt`
- **Type**: `(p) [Fact (Nat.Prime p)] (i : Fin (p+1)) (hi : (i : ℕ) < p) : (primeCoxMatrixEquiv p).symm i = primeLowerCoxMatrix p ⟨i, hi⟩`
- **What**: Inverse evaluation below the last index.
- **How**: `primeFinEquivCoxMatrix_apply_of_lt`.
- **Hypotheses**: `i < p`.
- **Uses from project**: `primeCoxMatrixEquiv`, `primeLowerCoxMatrix`, `primeFinEquivCoxMatrix_apply_of_lt`
- **Used by**: unused in file (KroneckerFrobenius.lean:61)
- **Visibility**: public
- **Lines**: 136–140, proof 1 line
- **Notes**: `@[simp]`.

### `theorem Cox.primeCoxMatrixEquiv_symm_apply_last`
- **Type**: `(p) [Fact (Nat.Prime p)] : (primeCoxMatrixEquiv p).symm (Fin.last p) = sigmaZero p`
- **What**: Inverse evaluation at the last index.
- **How**: `primeFinEquivCoxMatrix_apply_last`.
- **Hypotheses**: `p` prime.
- **Uses from project**: `primeCoxMatrixEquiv`, `sigmaZero`, `primeFinEquivCoxMatrix_apply_last`
- **Used by**: unused in file (KroneckerFrobenius.lean:62)
- **Visibility**: public
- **Lines**: 143–146, proof 1 line
- **Notes**: `@[simp]`.

### `theorem Cox.jIntCoeff_eq_zero_of_lt`
- **Type**: `{n : ℤ} (hn : n < -1) : jIntCoeff n = 0`
- **What**: The integral `q`-coefficients of `j` vanish below the simple pole.
- **How**: the complex coefficient vanishes by `laurentqExpansion.coeff_eq_zero_of_lt` with `j_poleOrder = 1`; transport through `jIntCoeff_spec` and `Int.cast_injective` (`exact_mod_cast`).
- **Hypotheses**: `n < -1`.
- **Uses from project**: `jIntCoeff`, `laurentqExpansion`, `j`, `laurentqExpansion.coeff_eq_zero_of_lt`, `j_poleOrder`, `jIntCoeff_spec`
- **Used by**: `jIntegralLaurentSeries`, `jIntegralLaurentSeriesWidth_coeff_mul_map_complex`, `jUnitLaurentSeriesMod_coeff_eq_zero_of_lt`
- **Visibility**: public
- **Lines**: 149–157, proof ≈ 7 lines
- **Notes**: basic property of `jIntCoeff` (CoxMatrices/LaurentExpansion.lean:31); belongs beside `jIntCoeff_neg_one` there (relocation). Also used by KroneckerFrobenius.lean:36, 93.

### `def Cox.jIntegralLaurentSeries`
- **Type**: `LaurentSeries ℤ`
- **What**: The integral Laurent series `∑ jIntCoeff(n) q^n` of `j` (width 1).
- **How**: anonymous `HahnSeries` structure with `coeff := jIntCoeff` and an `isPWO_support'` proof via `Set.IsWF.isPWO`, `BddBelow.isWF`, lower bound `-1` from `jIntCoeff_eq_zero_of_lt`.
- **Hypotheses**: none.
- **Uses from project**: `jIntCoeff`, `jIntCoeff_eq_zero_of_lt`
- **Used by**: `jIntegralLaurentSeries_coeff`, `jIntegralLaurentSeries_map_complex`, `jUnitLaurentSeriesMod`
- **Visibility**: public
- **Lines**: 160–169, body ≈ 8 lines
- **Notes**: anonymous construction #1 (should be `HahnSeries.ofSuppBddBelow`, Basic.lean:574). Mathematically equals `jIntegralLaurentSeriesWidth 1`.

### `theorem Cox.jIntegralLaurentSeries_coeff`
- **Type**: `(n : ℤ) : jIntegralLaurentSeries.coeff n = jIntCoeff n`
- **What**: Coefficient formula.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `jIntegralLaurentSeries`, `jIntCoeff`
- **Used by**: unused in file (unused project-wide)
- **Visibility**: public
- **Lines**: 172–174, proof 1 line
- **Notes**: `@[simp]`; never referenced (the proofs below use `change`).

### `theorem Cox.jIntegralLaurentSeries_map_complex`
- **Type**: `jIntegralLaurentSeries.map (Int.castRingHom ℂ) = laurentqExpansion 1 j`
- **What**: Casting the integral series to ℂ recovers the analytic width-1 expansion of `j`.
- **How**: `ext`; `jIntCoeff_spec`.
- **Hypotheses**: none.
- **Uses from project**: `jIntegralLaurentSeries`, `jIntCoeff`, `laurentqExpansion`, `j`, `jIntCoeff_spec`
- **Used by**: unused in file (unused project-wide)
- **Visibility**: public
- **Lines**: 176–181, proof ≈ 3 lines
- **Notes**: unused declaration; the `m = 1` case of `jIntegralLaurentSeriesWidth_map_complex`.

### `def Cox.jIntegralLaurentSeriesWidth`
- **Type**: `(m : ℕ+) : LaurentSeries ℤ`
- **What**: The integral expansion of `j` in the width-`m` parameter `q^{1/m}`: coefficient `jIntCoeff (k/m)` when `m ∣ k` and `k ≥ -m`, else `0`.
- **How**: anonymous `HahnSeries` structure; `isPWO_support'` via `Set.IsWF.isPWO`, `BddBelow.isWF`, lower bound `-m` read off the `if`.
- **Hypotheses**: none.
- **Uses from project**: `jIntCoeff`
- **Used by**: `jIntegralLaurentSeriesWidth_coeff`, `_coeff_mul_map_complex`, `_map_complex`, `_map_zmod`, `specializeJIntegral`, `specializeJIntegral_map_zmod`, `specializeJIntegral_map_complex`
- **Visibility**: public
- **Lines**: 184–195, body ≈ 10 lines
- **Notes**: anonymous construction #2. It is `HahnSeries.embDomain` (Basic.lean:441) of `jIntegralLaurentSeries` along `k ↦ m·k` (see Observations). Cross-file: LevelThree.lean:577–606.

### `theorem Cox.jIntegralLaurentSeriesWidth_coeff`
- **Type**: `(m) (k : ℤ) : (jIntegralLaurentSeriesWidth m).coeff k = if (m : ℤ) ∣ k ∧ -(m : ℤ) ≤ k then jIntCoeff (k / m) else 0`
- **What**: Coefficient formula.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `jIntegralLaurentSeriesWidth`, `jIntCoeff`
- **Used by**: `jIntegralLaurentSeriesWidth_coeff_mul_map_complex`, `_map_complex`, `_map_zmod`
- **Visibility**: public
- **Lines**: 198–202, proof 1 line
- **Notes**: `@[simp]`.

### `theorem Cox.jIntegralLaurentSeriesWidth_coeff_mul_map_complex` (private)
- **Type**: `(m : ℕ+) (q : ℤ) : ((jIntegralLaurentSeriesWidth m).coeff (m * q) : ℂ) = (laurentqExpansion m j).coeff (m * q)`
- **What**: At exponents divisible by `m`, the cast integral coefficient equals the analytic width-`m` coefficient.
- **How**: `laurentqExpansion_nat_mul_coeff` reduces the analytic side to the width-1 coefficient at `q`; split on `-1 ≤ q`: if so the `if` fires (`Int.mul_ediv_cancel_left`) and `jIntCoeff_spec` closes; otherwise both sides are `0` by `jIntCoeff_eq_zero_of_lt`.
- **Hypotheses**: none.
- **Uses from project**: `jIntegralLaurentSeriesWidth`, `jIntegralLaurentSeriesWidth_coeff`, `laurentqExpansion`, `j`, `laurentqExpansion_nat_mul_coeff`, `j_cuspFunction_meromorphicAt`, `ModularFunction.j_periodic`, `jIntCoeff_spec`, `jIntCoeff_eq_zero_of_lt`
- **Used by**: `jIntegralLaurentSeriesWidth_map_complex`
- **Visibility**: private
- **Lines**: 204–226, proof ≈ 19 lines
- **Notes**: the `by_cases hq : -1 ≤ q` block (217–226) is repeated verbatim in `jUnitPrimeNormalForm_coeff_mul` (433–442).

### `theorem Cox.jIntegralLaurentSeriesWidth_map_complex`
- **Type**: `(m : ℕ+) : (jIntegralLaurentSeriesWidth m).map (Int.castRingHom ℂ) = laurentqExpansion m j`
- **What**: The integral width-`m` series casts to the analytic width-`m` expansion.
- **How**: `ext k`; if `m ∣ k` use the previous lemma; else both vanish (`if_neg` and `laurentqExpansion_nat_mul_coeff_of_not_dvd`).
- **Hypotheses**: none.
- **Uses from project**: `jIntegralLaurentSeriesWidth`, `jIntegralLaurentSeriesWidth_coeff`, `jIntegralLaurentSeriesWidth_coeff_mul_map_complex`, `laurentqExpansion`, `j`, `laurentqExpansion_nat_mul_coeff_of_not_dvd`, `j_cuspFunction_meromorphicAt`, `ModularFunction.j_periodic`
- **Used by**: `specializeJIntegral_map_complex`
- **Visibility**: public
- **Lines**: 229–241, proof ≈ 10 lines
- **Notes**: cross-file LevelThree.lean:605.

### `def Cox.jUnitLaurentSeriesMod`
- **Type**: `(p : ℕ+) : LaurentSeries (ZMod (p : ℕ))`
- **What**: The width-1 integral `j`-series reduced mod `p`.
- **How**: `jIntegralLaurentSeries.map (Int.castRingHom (ZMod p))`.
- **Hypotheses**: none.
- **Uses from project**: `jIntegralLaurentSeries`
- **Used by**: `jUnitLaurentSeriesMod_coeff`, `_coeff_neg_one`, `_coeff_eq_zero_of_lt`, `_order`, `jUnitLaurentSeriesModPrimeNormalForm`, `jUnitLaurentSeriesMod_pow_prime_normalForm`, `jUnitLaurentSeriesMod_pow_prime`
- **Visibility**: public
- **Lines**: 244–245
- **Notes**: cross-file KroneckerFrobenius.lean (6 uses).

### `theorem Cox.jUnitLaurentSeriesMod_coeff`
- **Type**: `(p) (n : ℤ) : (jUnitLaurentSeriesMod p).coeff n = (jIntCoeff n : ZMod p)`
- **What**: Coefficient formula.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `jUnitLaurentSeriesMod`, `jIntCoeff`
- **Used by**: `jUnitLaurentSeriesMod_coeff_neg_one`, `_coeff_eq_zero_of_lt`, `jUnitPrimeNormalForm_coeff_mul_of_lower`
- **Visibility**: public
- **Lines**: 248–250, proof 1 line
- **Notes**: `@[simp]`.

### `theorem Cox.jUnitLaurentSeriesMod_coeff_neg_one`
- **Type**: `(p) : (jUnitLaurentSeriesMod p).coeff (-1) = 1`
- **What**: The pole coefficient is one.
- **How**: `jIntCoeff_neg_one` + cast.
- **Hypotheses**: none.
- **Uses from project**: `jUnitLaurentSeriesMod_coeff`, `jIntCoeff_neg_one`
- **Used by**: `jUnitLaurentSeriesMod_order`
- **Visibility**: public
- **Lines**: 252–255, proof 2 lines
- **Notes**: none.

### `theorem Cox.jUnitLaurentSeriesMod_coeff_eq_zero_of_lt` (private)
- **Type**: `(p) {n : ℤ} (hn : n < -1) : (jUnitLaurentSeriesMod p).coeff n = 0`
- **What**: Vanishing below the pole.
- **How**: `jIntCoeff_eq_zero_of_lt` + cast.
- **Hypotheses**: `n < -1`.
- **Uses from project**: `jUnitLaurentSeriesMod_coeff`, `jIntCoeff_eq_zero_of_lt`
- **Used by**: `jUnitLaurentSeriesMod_order`
- **Visibility**: private
- **Lines**: 257–261, proof 2 lines
- **Notes**: none.

### `theorem Cox.jUnitLaurentSeriesMod_order` (private)
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : (jUnitLaurentSeriesMod p).order = -1`
- **What**: The reduced series has order `-1`.
- **How**: `HahnSeries.orderTop_eq_of_le` (Basic.lean:275) with the nonzero coefficient at `-1` and vanishing below (`by_contra`), then `order_eq_orderTop_of_ne_zero` + `exact_mod_cast`; needs `Fact (1 < p)` (installed by `letI`) for `1 ≠ 0` in `ZMod p`.
- **Hypotheses**: `p` prime (only `1 < p` is used).
- **Uses from project**: `jUnitLaurentSeriesMod`, `jUnitLaurentSeriesMod_coeff_neg_one`, `jUnitLaurentSeriesMod_coeff_eq_zero_of_lt`
- **Used by**: `jUnitLaurentSeriesMod_pow_prime_normalForm`, `jUnitPrimeNormalForm_coeff_mul_of_lower`
- **Visibility**: private
- **Lines**: 263–280, proof ≈ 15 lines
- **Notes**: same skeleton as `jLaurentSeriesMod_order` (339–359) and DiagonalLaurent.lean:257–266; hypothesis style differs from its sibling (`Fact Prime` vs explicit `1 < p`).

### `theorem Cox.powerSeries_pow_prime_eq_expand` (private)
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] (F : PowerSeries (ZMod p)) : F ^ (p : ℕ) = F.expand p _`
- **What**: Over `ZMod p`, the `p`-th power of a power series is its `p`-fold expansion (Frobenius acts trivially on coefficients).
- **How**: `@MvPowerSeries.map_frobenius_expand Unit` (MvPowerSeries/Expand.lean:232, `[ExpChar R p]`) transported by `change` through the defeq `PowerSeries R = MvPowerSeries Unit R`; the Frobenius map on coefficients is the identity by `ZMod.pow_card` (`hmap`, 290–295).
- **Hypotheses**: `p` prime.
- **Uses from project**: `[]`
- **Used by**: `jUnitLaurentSeriesMod_pow_prime_normalForm`
- **Visibility**: private
- **Lines**: 282–297, proof ≈ 13 lines
- **Notes**: `hmap` is `ZMod.frobenius_zmod` (FieldTheory/Finite/Basic.lean:593) + `PowerSeries.map_id` (PowerSeries/Basic.lean:448) in two rewrites. No `PowerSeries.map_frobenius_expand` in mathlib (verified). `n = 2` twin at KroneckerFrobenius.lean:141–155.

### `def Cox.jLaurentSeriesMod`
- **Type**: `(p : ℕ+) : LaurentSeries (ZMod (p : ℕ))`
- **What**: The width-`p` expansion of `j` reduced mod `p` (exponents multiples of `p`).
- **How**: anonymous `HahnSeries` structure with the same `if` as `jIntegralLaurentSeriesWidth p` cast to `ZMod p`; same `isPWO_support'` skeleton.
- **Hypotheses**: none.
- **Uses from project**: `jIntCoeff`
- **Used by**: `jLaurentSeriesMod_coeff`, `jIntegralLaurentSeriesWidth_map_zmod`, `jLaurentSeriesMod_coeff_neg_p`, `_order`, `_leadingCoeff`, `jUnitPrimeNormalForm_coeff_mul`, `_of_not_dvd`, `jUnitLaurentSeriesMod_pow_prime`, `specializeJMod`, `specializeJMod_varY`, `specializeJIntegral_map_zmod`, `specializeJMod_injective`
- **Visibility**: public
- **Lines**: 300–311, body ≈ 10 lines
- **Notes**: anonymous construction #3. Could be DEFINED as `(jIntegralLaurentSeriesWidth p).map (Int.castRingHom (ZMod p))` (exactly what `jIntegralLaurentSeriesWidth_map_zmod` proves), mirroring how `jUnitLaurentSeriesMod` is defined from `jIntegralLaurentSeries` — the two pairs are treated inconsistently.

### `theorem Cox.jLaurentSeriesMod_coeff`
- **Type**: `(p) (k : ℤ) : (jLaurentSeriesMod p).coeff k = if (p : ℤ) ∣ k ∧ -(p : ℤ) ≤ k then (jIntCoeff (k / p) : ZMod p) else 0`
- **What**: Coefficient formula.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `jLaurentSeriesMod`, `jIntCoeff`
- **Used by**: `jIntegralLaurentSeriesWidth_map_zmod`, `jLaurentSeriesMod_coeff_neg_p`, `_order`, `jUnitPrimeNormalForm_coeff_mul`, `_of_not_dvd`
- **Visibility**: public
- **Lines**: 313–317, proof 1 line
- **Notes**: NOT `@[simp]` although its three sibling `_coeff` rfl-lemmas are (July flag; unchanged).

### `theorem Cox.jIntegralLaurentSeriesWidth_map_zmod`
- **Type**: `(p : ℕ+) : (jIntegralLaurentSeriesWidth p).map (Int.castRingHom (ZMod p)) = jLaurentSeriesMod p`
- **What**: Reducing the integral width-`p` series mod `p` gives `jLaurentSeriesMod p`.
- **How**: `ext`; both coefficient formulas; `split_ifs <;> simp`.
- **Hypotheses**: none.
- **Uses from project**: `jIntegralLaurentSeriesWidth`, `jIntegralLaurentSeriesWidth_coeff`, `jLaurentSeriesMod`, `jLaurentSeriesMod_coeff`
- **Used by**: `specializeJIntegral_map_zmod`
- **Visibility**: public
- **Lines**: 320–328, proof ≈ 4 lines
- **Notes**: would be `rfl` if `jLaurentSeriesMod` were defined as this map.

### `theorem Cox.jLaurentSeriesMod_coeff_neg_p` (private)
- **Type**: `(p) : (jLaurentSeriesMod p).coeff (-(p : ℤ)) = 1`
- **What**: The pole coefficient is one.
- **How**: `if_pos` (`dvd_neg`, `le_rfl`), `Int.ediv_eq_of_eq_mul_left` to get `-p / p = -1`, `jIntCoeff_neg_one`.
- **Hypotheses**: none.
- **Uses from project**: `jLaurentSeriesMod_coeff`, `jIntCoeff_neg_one`
- **Used by**: `jLaurentSeriesMod_order`, `jLaurentSeriesMod_leadingCoeff`
- **Visibility**: private
- **Lines**: 330–337, proof ≈ 5 lines
- **Notes**: none.

### `theorem Cox.jLaurentSeriesMod_order`
- **Type**: `(p : ℕ+) (hp : 1 < (p : ℕ)) : (jLaurentSeriesMod p).order = -(p : ℤ)`
- **What**: The reduced width-`p` series has order `-p`.
- **How**: as `jUnitLaurentSeriesMod_order`: `orderTop_eq_of_le` with the nonzero coefficient at `-p` and the `if` bound, `order_eq_orderTop_of_ne_zero`, `exact_mod_cast`.
- **Hypotheses**: `1 < p` (nontriviality of `ZMod p`).
- **Uses from project**: `jLaurentSeriesMod`, `jLaurentSeriesMod_coeff_neg_p`, `jLaurentSeriesMod_coeff`
- **Used by**: `jLaurentSeriesMod_leadingCoeff`, `specializeJMod_injective`
- **Visibility**: public
- **Lines**: 339–359, proof ≈ 18 lines
- **Notes**: repeated skeleton (see Observations).

### `theorem Cox.jLaurentSeriesMod_leadingCoeff`
- **Type**: `(p) (hp : 1 < p) : (jLaurentSeriesMod p).leadingCoeff = 1`
- **What**: Leading coefficient one.
- **How**: `HahnSeries.leadingCoeff_eq` + order + `_coeff_neg_p`.
- **Hypotheses**: `1 < p`.
- **Uses from project**: `jLaurentSeriesMod_order`, `jLaurentSeriesMod_coeff_neg_p`
- **Used by**: `specializeJMod_injective`
- **Visibility**: public
- **Lines**: 361–364, proof 2 lines
- **Notes**: none.

### `def Cox.jUnitLaurentSeriesModPrimeNormalForm` (private)
- **Type**: `(p : ℕ+) : LaurentSeries (ZMod p)`
- **What**: `q^{-p} · expand_p(powerSeriesPart (jUnit))`, the predicted normal form of `(jUnit)^p`.
- **How**: `HahnSeries.single (-p) 1 * ↑((jUnitLaurentSeriesMod p).powerSeriesPart.expand p _)`.
- **Hypotheses**: none.
- **Uses from project**: `jUnitLaurentSeriesMod`
- **Used by**: `jUnitLaurentSeriesMod_pow_prime_normalForm`, `jUnitPrimeNormalForm_coeff_mul_of_lower`, `_of_lt`, `_coeff_mul`, `_of_not_dvd`, `jUnitLaurentSeriesMod_pow_prime`
- **Visibility**: private
- **Lines**: 366–371
- **Notes**: `noncomputable`.

### `theorem Cox.jUnitLaurentSeriesMod_pow_prime_normalForm` (private)
- **Type**: `(p) [Fact (Nat.Prime p)] : jUnitLaurentSeriesMod p ^ (p : ℕ) = jUnitLaurentSeriesModPrimeNormalForm p`
- **What**: `(jUnit)^p` equals the normal form.
- **How**: `LaurentSeries.single_order_mul_powerSeriesPart` (LaurentSeries.lean:237) with `order = -1`, then `mul_pow`, `HahnSeries.single_pow` (Multiplication.lean:795), `PowerSeries.coe_pow`, and `powerSeries_pow_prime_eq_expand`.
- **Hypotheses**: `p` prime.
- **Uses from project**: `jUnitLaurentSeriesMod`, `jUnitLaurentSeriesMod_order`, `powerSeries_pow_prime_eq_expand`, `jUnitLaurentSeriesModPrimeNormalForm`
- **Used by**: `jUnitLaurentSeriesMod_pow_prime`
- **Visibility**: private
- **Lines**: 373–387, proof ≈ 12 lines
- **Notes**: this is the mathlib-native route that KroneckerFrobenius.lean:77–96 re-derives by hand with `unitJPowerSeries`.

### `theorem Cox.jUnitPrimeNormalForm_coeff_mul_of_lower` (private)
- **Type**: `(p) [Fact (Nat.Prime p)] (q : ℤ) (hq : -1 ≤ q) : (jUnitLaurentSeriesModPrimeNormalForm p).coeff (p * q) = (jIntCoeff q : ZMod p)`
- **What**: Coefficient of the normal form at `p·q` for `q ≥ -1`.
- **How**: `HahnSeries.coeff_single_mul` shifts by `p`; write `p·q + p = p·n` with `n = (q+1).toNat`; `LaurentSeries.coeff_coe_powerSeries` (LaurentSeries.lean:204), `PowerSeries.coeff_expand_mul` (PowerSeries/Expand.lean:87), `powerSeriesPart_coeff`, `jUnitLaurentSeriesMod_order`.
- **Hypotheses**: `q ≥ -1`, `p` prime (via `_order`).
- **Uses from project**: `jUnitLaurentSeriesModPrimeNormalForm`, `jUnitLaurentSeriesMod_order`, `jUnitLaurentSeriesMod_coeff`, `jIntCoeff`
- **Used by**: `jUnitPrimeNormalForm_coeff_mul`
- **Visibility**: private
- **Lines**: 389–410, proof ≈ 19 lines
- **Notes**: none.

### `theorem Cox.jUnitPrimeNormalForm_coeff_mul_of_lt` (private)
- **Type**: `(p : ℕ+) (q : ℤ) (hq : q < -1) : (jUnitLaurentSeriesModPrimeNormalForm p).coeff (p * q) = 0`
- **What**: Coefficient at `p·q` for `q < -1` vanishes.
- **How**: `coeff_single_mul`; the shifted index `p(q+1) < 0` is not in the range of `ℕ → ℤ`, so `HahnSeries.embDomain_notin_range` (Basic.lean:477).
- **Hypotheses**: `q < -1`.
- **Uses from project**: `jUnitLaurentSeriesModPrimeNormalForm`
- **Used by**: `jUnitPrimeNormalForm_coeff_mul`
- **Visibility**: private
- **Lines**: 412–424, proof ≈ 10 lines
- **Notes**: none.

### `theorem Cox.jUnitPrimeNormalForm_coeff_mul` (private)
- **Type**: `(p) [Fact (Nat.Prime p)] (q : ℤ) : (jUnitLaurentSeriesModPrimeNormalForm p).coeff (p * q) = (jLaurentSeriesMod p).coeff (p * q)`
- **What**: At multiples of `p` the normal form agrees with `jLaurentSeriesMod p`.
- **How**: `by_cases -1 ≤ q` with `Int.mul_le_mul_of_nonneg_left`/`Int.mul_lt_mul_of_pos_left` and `Int.mul_ediv_cancel_left`, dispatching to `_of_lower`/`_of_lt`.
- **Hypotheses**: `p` prime.
- **Uses from project**: `jLaurentSeriesMod_coeff`, `jUnitPrimeNormalForm_coeff_mul_of_lower`, `_of_lt`, `jUnitLaurentSeriesModPrimeNormalForm`, `jLaurentSeriesMod`
- **Used by**: `jUnitLaurentSeriesMod_pow_prime`
- **Visibility**: private
- **Lines**: 426–442, proof ≈ 13 lines
- **Notes**: lines 433–442 duplicate 217–226.

### `theorem Cox.jUnitPrimeNormalForm_coeff_of_not_dvd` (private)
- **Type**: `(p) [Fact (Nat.Prime p)] {k : ℤ} (hdiv : ¬(p : ℤ) ∣ k) : (jUnitLaurentSeriesModPrimeNormalForm p).coeff k = (jLaurentSeriesMod p).coeff k`
- **What**: Off the multiples of `p` both vanish.
- **How**: right side by `if_neg`; left side via `coeff_single_mul`, then either `PowerSeries.coeff_expand_of_not_dvd` (PowerSeries/Expand.lean:97, with `Int.natCast_dvd_natCast`, `dvd_add_self_right`) or `embDomain_notin_range` for negative shifted index.
- **Hypotheses**: `¬ p ∣ k` (`Fact Prime` unused).
- **Uses from project**: `jLaurentSeriesMod_coeff`, `jUnitLaurentSeriesModPrimeNormalForm`, `jLaurentSeriesMod`
- **Used by**: `jUnitLaurentSeriesMod_pow_prime`
- **Visibility**: private
- **Lines**: 444–458, proof ≈ 12 lines
- **Notes**: `[Fact (Nat.Prime p)]` unused.

### `theorem Cox.jUnitLaurentSeriesMod_pow_prime`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : jUnitLaurentSeriesMod p ^ (p : ℕ) = jLaurentSeriesMod p`
- **What**: Over `ZMod p`, the `p`-th power of the width-1 reduced `j`-series is the width-`p` reduced series (`j(q)^p = j(q^p) mod p`).
- **How**: rewrite by the normal form and compare coefficients by cases `p ∣ k` (`jUnitPrimeNormalForm_coeff_mul`) / not (`_of_not_dvd`).
- **Hypotheses**: `p` prime.
- **Uses from project**: `jUnitLaurentSeriesMod_pow_prime_normalForm`, `jUnitPrimeNormalForm_coeff_mul`, `jUnitPrimeNormalForm_coeff_of_not_dvd`, `jUnitLaurentSeriesMod`, `jLaurentSeriesMod`
- **Used by**: unused in file (KroneckerFrobenius.lean:187, 200)
- **Visibility**: public
- **Lines**: 460–468, proof ≈ 6 lines
- **Notes**: none.

### `def Cox.specializeJMod`
- **Type**: `(p : ℕ+) : BivariatePolynomial (ZMod p) →+* Polynomial (LaurentSeries (ZMod p))`
- **What**: `Y ↦ jLaurentSeriesMod p`, `X` free.
- **How**: `bivariateSpecializeLaurent (jLaurentSeriesMod p)`.
- **Hypotheses**: none.
- **Uses from project**: `bivariateSpecializeLaurent`, `jLaurentSeriesMod`, `BivariatePolynomial`
- **Used by**: `specializeJMod_varX`, `_varY`, `specializeJIntegral_map_zmod`, `specializeJMod_injective`, `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 471–474
- **Notes**: `noncomputable`.

### `theorem Cox.specializeJMod_varX`
- **Type**: `(p) : specializeJMod p varX = Polynomial.X`
- **What**: `X` is fixed.
- **How**: `simp [specializeJMod, bivariateSpecializeLaurent, varX]`.
- **Hypotheses**: none.
- **Uses from project**: `specializeJMod`, `bivariateSpecializeLaurent`, `BivariatePolynomial.varX`
- **Used by**: unused in file (implicitly via `simp` in KroneckerFrobenius.lean:218)
- **Visibility**: public
- **Lines**: 477–481, proof 1 line
- **Notes**: `@[simp]`.

### `theorem Cox.specializeJMod_varY`
- **Type**: `(p) : specializeJMod p varY = Polynomial.C (jLaurentSeriesMod p)`
- **What**: `Y` goes to the constant `jLaurentSeriesMod p`.
- **How**: `simp`.
- **Hypotheses**: none.
- **Uses from project**: `specializeJMod`, `bivariateSpecializeLaurent`, `BivariatePolynomial.varY`, `jLaurentSeriesMod`
- **Used by**: unused in file (implicitly via `simp` in KroneckerFrobenius.lean:218)
- **Visibility**: public
- **Lines**: 484–488, proof 1 line
- **Notes**: `@[simp]`.

### `def Cox.specializeJIntegral`
- **Type**: `(m : ℕ+) : BivariatePolynomial ℤ →+* Polynomial (LaurentSeries ℤ)`
- **What**: `Y ↦ jIntegralLaurentSeriesWidth m` over ℤ.
- **How**: `bivariateSpecializeLaurent (jIntegralLaurentSeriesWidth m)`.
- **Hypotheses**: none.
- **Uses from project**: `bivariateSpecializeLaurent`, `jIntegralLaurentSeriesWidth`, `BivariatePolynomial`
- **Used by**: `specializeJIntegral_map_zmod`, `_map_complex`, `_modularPolynomial_map_complex`, `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 491–493
- **Notes**: none.

### `theorem Cox.specializeJIntegral_map_zmod`
- **Type**: `(p) (F : BivariatePolynomial ℤ) : (specializeJIntegral p F).map (laurentSeriesMapRingHom (Int.castRingHom (ZMod p))) = specializeJMod p (BivariatePolynomial.map (Int.castRingHom (ZMod p)) F)`
- **What**: Reduction mod `p` commutes with integral specialisation at width `p`.
- **How**: `bivariateSpecializeLaurent_map_apply` with `hJ := jIntegralLaurentSeriesWidth_map_zmod` (by `exact`, relying on `laurentSeriesMapRingHom f F = F.map f` defeq).
- **Hypotheses**: none.
- **Uses from project**: `specializeJIntegral`, `laurentSeriesMapRingHom`, `specializeJMod`, `BivariatePolynomial.map`, `jIntegralLaurentSeriesWidth`, `jLaurentSeriesMod`, `jIntegralLaurentSeriesWidth_map_zmod`, `bivariateSpecializeLaurent_map_apply`
- **Used by**: `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 496–507, proof ≈ 8 lines
- **Notes**: twin of `_map_complex` (same `simpa … using bivariateSpecializeLaurent_map_apply` shape).

### `theorem Cox.specializeJIntegral_map_complex`
- **Type**: `(m) (F : BivariatePolynomial ℤ) : (specializeJIntegral m F).map (laurentSeriesMapRingHom (Int.castRingHom ℂ)) = Polynomial.map (Polynomial.eval₂RingHom HahnSeries.C (laurentqExpansion m j)) (BivariatePolynomial.map (Int.castRingHom ℂ) F)`
- **What**: Casting the integral specialisation to ℂ gives specialisation at the analytic width-`m` series.
- **How**: `bivariateSpecializeLaurent_map_apply` with `hJ := jIntegralLaurentSeriesWidth_map_complex`.
- **Hypotheses**: none.
- **Uses from project**: `specializeJIntegral`, `laurentSeriesMapRingHom`, `laurentqExpansion`, `j`, `BivariatePolynomial.map`, `jIntegralLaurentSeriesWidth`, `jIntegralLaurentSeriesWidth_map_complex`, `bivariateSpecializeLaurent`, `bivariateSpecializeLaurent_map_apply`
- **Used by**: `specializeJIntegral_modularPolynomial_map_complex`
- **Visibility**: public
- **Lines**: 511–526, proof ≈ 9 lines
- **Notes**: none.

### `theorem Cox.specializeJIntegral_modularPolynomial_map_complex`
- **Type**: `(m : ℕ+) : (specializeJIntegral m (modularPolynomial m)).map (laurentSeriesMapRingHom (Int.castRingHom ℂ)) = formalCoxPolynomial m (zeta m)`
- **What**: The integral specialisation of `Φ_m` becomes the formal Cox product over ℂ.
- **How**: previous lemma + `modularPolynomial_map_complex` + `formalCoxPolynomial_eq_modularPolynomialC_map_j` (DiagonalLaurent).
- **Hypotheses**: none.
- **Uses from project**: `specializeJIntegral`, `modularPolynomial`, `laurentSeriesMapRingHom`, `formalCoxPolynomial`, `zeta`, `specializeJIntegral_map_complex`, `modularPolynomial_map_complex`, `formalCoxPolynomial_eq_modularPolynomialC_map_j`
- **Used by**: `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 530–535, proof 2 lines
- **Notes**: none.

### `theorem Cox.specializeJMod_injective`
- **Type**: `(p : ℕ+) [hp : Fact (Nat.Prime p)] : Function.Injective (specializeJMod p)`
- **What**: Exercise 11.15 mod `p`: substituting the width-`p` reduced `j`-series for `Y` is injective on `ZMod p[X][Y]`.
- **How**: `Polynomial.map_injective` (Eval/Coeff.lean:103) of `polynomial_eval₂_laurentSeries_injective` with `w = p`, using `jLaurentSeriesMod_order/_leadingCoeff`.
- **Hypotheses**: `p` prime (only `1 < p` used).
- **Uses from project**: `specializeJMod`, `polynomial_eval₂_laurentSeries_injective`, `jLaurentSeriesMod`, `jLaurentSeriesMod_order`, `jLaurentSeriesMod_leadingCoeff`
- **Used by**: unused in file (KroneckerFrobenius.lean:230)
- **Visibility**: public
- **Lines**: 538–545, proof ≈ 5 lines
- **Notes**: none.

### `def Cox.phasePolynomial`
- **Type**: `(p : ℕ+) (e : ℤ) : Polynomial ℤ`
- **What**: `X^{e mod p}`, an integral lift of the phase `ζ_p^e`.
- **How**: `Polynomial.X ^ Int.toNat (e % p)`.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: `phasePolynomial_eval_zeta`, `_eval_one`, `cyclotomicTransformedJSeries`, `cyclotomicTransformedJSeries_coeff`, `_map_complex`, `_map_mod`
- **Visibility**: public
- **Lines**: 548–549
- **Notes**: no mathlib analogue (searched `zpow_emod`, `IsPrimitiveRoot` API: only `zpow_eq_zpow_emod'` Algebra/Group/Basic.lean:858, used below).

### `theorem Cox.phasePolynomial_eval_zeta` (private)
- **Type**: `(p) (e : ℤ) : Polynomial.eval₂ (Int.castRingHom ℂ) (zeta p) (phasePolynomial p e) = zeta p ^ e`
- **What**: Evaluating the lift at `ζ_p` gives `ζ_p^e`.
- **How**: `eval₂_pow`, `eval₂_X`, `zpow_natCast`, `Int.toNat_of_nonneg` (`Int.emod_nonneg`); then `zpow_eq_zpow_emod'` on the unit `Units.mk0 (zeta p)` with `(zeta_isPrimitiveRoot p).pow_eq_one`, transported by `Units.val_zpow_eq_zpow_val`.
- **Hypotheses**: none.
- **Uses from project**: `phasePolynomial`, `zeta`, `zeta_isPrimitiveRoot`
- **Used by**: `cyclotomicTransformedJSeries_map_complex`
- **Visibility**: private
- **Lines**: 551–564, proof ≈ 11 lines
- **Notes**: none.

### `theorem Cox.phasePolynomial_eval_one` (private)
- **Type**: `(p) (e) : Polynomial.eval₂ (Int.castRingHom (ZMod p)) 1 (phasePolynomial p e) = 1`
- **What**: Evaluating the lift at `1` gives `1`.
- **How**: `simp [phasePolynomial]`.
- **Hypotheses**: none.
- **Uses from project**: `phasePolynomial`
- **Used by**: `cyclotomicTransformedJSeries_map_mod`
- **Visibility**: private
- **Lines**: 566–569, proof 1 line
- **Notes**: none.

### `def Cox.cyclotomicTransformedJSeries`
- **Type**: `(p : ℕ+) (σ : CoxMatrix p) : LaurentSeries (Polynomial ℤ)`
- **What**: The integral cyclotomic lift of `transformedJSeries ζ_p σ`: coefficients `C (jIntCoeff (k/a²)) · phasePolynomial p (ab · k/a²)` on `a² ∣ k ≥ -a²`.
- **How**: anonymous `HahnSeries` structure (same `if`/`isPWO_support'` skeleton as `transformedJSeries`, CoxMatrices/LaurentExpansion.lean:50–63).
- **Hypotheses**: none.
- **Uses from project**: `CoxMatrix`, `jIntCoeff`, `phasePolynomial`
- **Used by**: `cyclotomicTransformedJSeries_coeff`, `_map_complex`, `_map_mod`, `cyclotomicCoxPolynomial`
- **Visibility**: public
- **Lines**: 572–587, body ≈ 14 lines
- **Notes**: anonymous construction #4; `noncomputable`. Would be an instance of a phase-generalised `transformedJSeries` (see Generalization).

### `theorem Cox.cyclotomicTransformedJSeries_coeff`
- **Type**: `(p) (σ) (k : ℤ) : (cyclotomicTransformedJSeries p σ).coeff k = if (σ.a : ℤ)^2 ∣ k ∧ -(σ.a : ℤ)^2 ≤ k then C (jIntCoeff (k / σ.a^2)) * phasePolynomial p (σ.a * σ.b * (k / σ.a^2)) else 0`
- **What**: Coefficient formula.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `cyclotomicTransformedJSeries`, `jIntCoeff`, `phasePolynomial`, `CoxMatrix`
- **Used by**: `cyclotomicTransformedJSeries_map_complex`, `_map_mod`
- **Visibility**: public
- **Lines**: 589–597, proof 1 line
- **Notes**: NOT `@[simp]` (July flag; unchanged).

### `def Cox.phaseEvalComplex`
- **Type**: `(p : ℕ+) : Polynomial ℤ →+* ℂ`
- **What**: Evaluate integral phase polynomials at `ζ_p`.
- **How**: `Polynomial.eval₂RingHom (Int.castRingHom ℂ) (zeta p)`.
- **Hypotheses**: none.
- **Uses from project**: `zeta`
- **Used by**: `cyclotomicTransformedJSeries_map_complex`, `cyclotomicCoxPolynomial_map_complex`, `specializeJMod_modularPolynomial_eq_formal` (via `change`)
- **Visibility**: public
- **Lines**: 600–601
- **Notes**: none.

### `def Cox.phaseEvalMod`
- **Type**: `(p : ℕ+) : Polynomial ℤ →+* ZMod p`
- **What**: Reduce coefficients mod `p` and set the phase variable to `1`.
- **How**: `Polynomial.eval₂RingHom (Int.castRingHom (ZMod p)) 1`.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: `cyclotomicTransformedJSeries_map_mod`, `cyclotomicCoxPolynomial_map_mod`
- **Visibility**: public
- **Lines**: 604–605
- **Notes**: none.

### `theorem Cox.cyclotomicTransformedJSeries_map_complex`
- **Type**: `(p) (σ) : laurentSeriesMapRingHom (phaseEvalComplex p) (cyclotomicTransformedJSeries p σ) = transformedJSeries (zeta p) σ`
- **What**: Evaluating the lift at `ζ_p` recovers the complex transformed root series.
- **How**: `ext k`; both coefficient formulas; `split_ifs`; `map_mul`, `Polynomial.eval₂_C`, `phasePolynomial_eval_zeta`.
- **Hypotheses**: none.
- **Uses from project**: `laurentSeriesMapRingHom`, `laurentSeriesMapRingHom_coeff`, `phaseEvalComplex`, `cyclotomicTransformedJSeries`, `cyclotomicTransformedJSeries_coeff`, `transformedJSeries`, `transformedJSeries_coeff`, `zeta`, `phasePolynomial`, `phasePolynomial_eval_zeta`, `jIntCoeff`
- **Used by**: `cyclotomicCoxPolynomial_map_complex`
- **Visibility**: public
- **Lines**: 607–624, proof ≈ 12 lines
- **Notes**: same 12-line skeleton as `_map_mod`.

### `theorem Cox.cyclotomicTransformedJSeries_map_mod`
- **Type**: `(p) [Fact (Nat.Prime p)] (σ) : laurentSeriesMapRingHom (phaseEvalMod p) (cyclotomicTransformedJSeries p σ) = transformedJSeries (1 : ZMod p) σ`
- **What**: Reducing the lift mod `p` with phase `1` gives the phase-one root series.
- **How**: as above with `phasePolynomial_eval_one` and `simp` (`one_zpow`).
- **Hypotheses**: `p` prime (unused; `ZMod p` is a field only for `transformedJSeries`'s `Field` requirement — that IS why `Fact Prime` is needed).
- **Uses from project**: `laurentSeriesMapRingHom`, `laurentSeriesMapRingHom_coeff`, `phaseEvalMod`, `cyclotomicTransformedJSeries`, `cyclotomicTransformedJSeries_coeff`, `transformedJSeries`, `transformedJSeries_coeff`, `phasePolynomial`, `phasePolynomial_eval_one`, `jIntCoeff`
- **Used by**: `cyclotomicCoxPolynomial_map_mod`
- **Visibility**: public
- **Lines**: 626–643, proof ≈ 12 lines
- **Notes**: duplicate skeleton of 607–624.

### `def Cox.cyclotomicCoxPolynomial`
- **Type**: `(p : ℕ+) : Polynomial (LaurentSeries (Polynomial ℤ))`
- **What**: `∏_σ (X − cyclotomicTransformedJSeries p σ)`, the integral cyclotomic lift of the formal Cox product.
- **How**: `Finset.prod` over `CoxMatrix p`.
- **Hypotheses**: none.
- **Uses from project**: `CoxMatrix`, `cyclotomicTransformedJSeries`
- **Used by**: `cyclotomicCoxPolynomial_map_complex`, `_map_mod`, `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 646–649
- **Notes**: `noncomputable`; same shape as `formalCoxPolynomial` (FormalCoxProduct.lean:24) over a non-field.

### `theorem Cox.cyclotomicCoxPolynomial_map_complex`
- **Type**: `(p) : (cyclotomicCoxPolynomial p).map (laurentSeriesMapRingHom (phaseEvalComplex p)) = formalCoxPolynomial p (zeta p)`
- **What**: The lift maps to the complex formal Cox product.
- **How**: `Polynomial.map_prod` + `cyclotomicTransformedJSeries_map_complex` under `simp`.
- **Hypotheses**: none.
- **Uses from project**: `cyclotomicCoxPolynomial`, `laurentSeriesMapRingHom`, `phaseEvalComplex`, `formalCoxPolynomial`, `zeta`, `cyclotomicTransformedJSeries_map_complex`
- **Used by**: `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 651–657, proof ≈ 3 lines
- **Notes**: `classical`; twin of `_map_mod`.

### `theorem Cox.cyclotomicCoxPolynomial_map_mod`
- **Type**: `(p) [Fact (Nat.Prime p)] : (cyclotomicCoxPolynomial p).map (laurentSeriesMapRingHom (phaseEvalMod p)) = formalCoxPolynomial p (1 : ZMod p)`
- **What**: The lift maps to the phase-one formal Cox product mod `p`.
- **How**: as above with `_map_mod`.
- **Hypotheses**: `p` prime.
- **Uses from project**: `cyclotomicCoxPolynomial`, `laurentSeriesMapRingHom`, `phaseEvalMod`, `formalCoxPolynomial`, `cyclotomicTransformedJSeries_map_mod`
- **Used by**: `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 659–666, proof ≈ 3 lines
- **Notes**: none.

### `theorem Cox.cyclotomicDescent_dvd`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] (F : Polynomial ℤ) (z : ℤ) (hF : eval₂ (Int.castRingHom ℂ) (zeta p) F = z) : (p : ℤ) ∣ F.eval 1 − z`
- **What**: Cox Exercise 11.13: if an integral polynomial takes an integer value at `ζ_p`, its value at `1` is congruent to it mod `p`.
- **How**: `F − C z` has `ζ_p` as a root, so over ℚ the cyclotomic polynomial (`Polynomial.cyclotomic_eq_minpoly_rat`, Cyclotomic/Roots.lean:178, + `minpoly.dvd`) divides it; descend to ℤ by `Polynomial.map_dvd_map` (Div.lean:415) with `cyclotomic.monic` and `map_cyclotomic`; evaluate at `1` (`Polynomial.eval_dvd`) and use `eval_one_cyclotomic_prime = p` (Cyclotomic/Eval.lean:32).
- **Hypotheses**: `p` prime.
- **Uses from project**: `zeta`, `zeta_isPrimitiveRoot`
- **Used by**: `cyclotomicDescent_zmod`
- **Visibility**: public
- **Lines**: 669–694, proof ≈ 22 lines
- **Notes**: the ℚ detour (`hcast` 676–679, `map_dvd_map` 688–691) can be avoided with `Polynomial.cyclotomic_eq_minpoly` over ℤ (Cyclotomic/Roots.lean:171) + `minpoly.isIntegrallyClosed_dvd` (FieldTheory/Minpoly/IsIntegrallyClosed.lean:71) + `(zeta_isPrimitiveRoot p).isIntegral` (RootsOfUnity/Minpoly.lean:41).

### `theorem Cox.cyclotomicDescent_zmod`
- **Type**: `(p) [Fact (Nat.Prime p)] (F) (z) (hF) : ((F.eval 1 : ℤ) : ZMod p) = (z : ZMod p)`
- **What**: Exercise 11.13 as an equality in `ZMod p`.
- **How**: `ZMod.intCast_eq_intCast_iff_dvd_sub` (Data/ZMod/Basic.lean:514) + `dvd_neg` + previous lemma.
- **Hypotheses**: `p` prime.
- **Uses from project**: `zeta`, `cyclotomicDescent_dvd`
- **Used by**: `cyclotomicDescent_polynomialLaurentSeries`
- **Visibility**: public
- **Lines**: 697–702, proof 2 lines
- **Notes**: none.

### `theorem Cox.cyclotomicDescent_polynomialLaurentSeries`
- **Type**: `(p) [Fact (Nat.Prime p)] (A : Polynomial (LaurentSeries (Polynomial ℤ))) (B : Polynomial (LaurentSeries ℤ)) (h : A.map (laurentSeriesMapRingHom (eval₂RingHom (Int.castRingHom ℂ) (zeta p))) = B.map (laurentSeriesMapRingHom (Int.castRingHom ℂ))) : A.map (laurentSeriesMapRingHom (eval₂RingHom (Int.castRingHom (ZMod p)) 1)) = B.map (laurentSeriesMapRingHom (Int.castRingHom (ZMod p)))`
- **What**: Exercise 11.13 applied coefficientwise (in both polynomial and Laurent index) to a polynomial identity over ℂ: agreement at `ζ_p` over ℂ implies agreement at `1` over `ZMod p`.
- **How**: `Polynomial.ext` + `HahnSeries.ext`; extract the `(n,k)` coefficient of `h`; rewrite `1 = castRingHom 1` and `Polynomial.eval₂_at_apply` (Eval/Defs.lean:256) so that `cyclotomicDescent_zmod` applies.
- **Hypotheses**: `p` prime.
- **Uses from project**: `laurentSeriesMapRingHom`, `laurentSeriesMapRingHom_coeff`, `zeta`, `cyclotomicDescent_zmod`
- **Used by**: `specializeJMod_modularPolynomial_eq_formal`
- **Visibility**: public
- **Lines**: 705–733, proof ≈ 14 lines
- **Notes**: none.

### `theorem Cox.specializeJMod_modularPolynomial_eq_formal`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : specializeJMod p (BivariatePolynomial.map (Int.castRingHom (ZMod p)) (modularPolynomial p)) = formalCoxPolynomial p (1 : ZMod p)`
- **What**: After reduction mod `p`, `Φ_p` specialised at the width-`p` `j`-series is the phase-one formal Cox product.
- **How**: over ℂ, `cyclotomicCoxPolynomial p` and `specializeJIntegral p (modularPolynomial p)` agree (`cyclotomicCoxPolynomial_map_complex`, `specializeJIntegral_modularPolynomial_map_complex`); descend by `cyclotomicDescent_polynomialLaurentSeries`; identify the two sides via `specializeJIntegral_map_zmod` and `cyclotomicCoxPolynomial_map_mod`.
- **Hypotheses**: `p` prime.
- **Uses from project**: `specializeJMod`, `BivariatePolynomial.map`, `modularPolynomial`, `formalCoxPolynomial`, `cyclotomicCoxPolynomial`, `specializeJIntegral`, `laurentSeriesMapRingHom`, `zeta`, `phaseEvalComplex`, `cyclotomicCoxPolynomial_map_complex`, `specializeJIntegral_modularPolynomial_map_complex`, `cyclotomicDescent_polynomialLaurentSeries`, `specializeJIntegral_map_zmod`, `cyclotomicCoxPolynomial_map_mod`
- **Used by**: unused in file (KroneckerFrobenius.lean:216)
- **Visibility**: public
- **Lines**: 737–769, proof ≈ 27 lines
- **Notes**: `let A/B` + `change` at 749–752 only to unfold `phaseEvalComplex`; a `@[simp] phaseEvalComplex_eq` or stating the descent lemma in terms of `phaseEvalComplex`/`phaseEvalMod` would remove it.

## File Summary
- Total declarations: 63 (16 defs, 47 theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `jLaurentSeriesMod` (12), `jUnitLaurentSeriesMod` (7), `jIntegralLaurentSeriesWidth` (7), `primeFinToCoxMatrix` (7), `jUnitLaurentSeriesModPrimeNormalForm` (6), `primeLowerCoxMatrix` (6), `phasePolynomial` (6), `laurentSeriesMapRingHom` (9, imported), `jLaurentSeriesMod_coeff` (5), `specializeJMod` (5), `specializeJIntegral` (4), `cyclotomicTransformedJSeries` (4), `jIntCoeff_eq_zero_of_lt` (3), `jIntegralLaurentSeriesWidth_coeff` (3), `jUnitLaurentSeriesMod_coeff` (3), `cyclotomicCoxPolynomial` (3), `phaseEvalComplex` (3)
- Unused declarations (not used by anything in this file): `primeCoxMatrixEquiv_symm_apply_of_lt`, `primeCoxMatrixEquiv_symm_apply_last`, `jIntegralLaurentSeries_coeff` (unused project-wide), `jIntegralLaurentSeries_map_complex` (unused project-wide), `jUnitLaurentSeriesMod_pow_prime`, `specializeJMod_varX`, `specializeJMod_varY` (simp-set only), `specializeJMod_injective`, `specializeJMod_modularPolynomial_eq_formal` (all others used by KroneckerFrobenius/LevelThree)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: `specializeJMod_modularPolynomial_eq_formal` ≈ 27, `primeFinToCoxMatrix_surjective` ≈ 23, `cyclotomicDescent_dvd` ≈ 22)

## Observations

### Mathlib API candidates
- **Four anonymous `HahnSeries` constructions** — `jIntegralLaurentSeries` (160–169), `jIntegralLaurentSeriesWidth` (184–195), `jLaurentSeriesMod` (300–311), `cyclotomicTransformedJSeries` (572–587) — plus the parallel `transformedJSeries` (CoxMatrices/LaurentExpansion.lean:50–63): mathlib `HahnSeries.ofSuppBddBelow (f : Γ → R) (hf : BddBelow (Function.support f)) : R⟦Γ⟧` (`Mathlib/RingTheory/HahnSeries/Basic.lean:574`, `@[simps]`), with `coeff_ofSuppBddBelow` (rfl, :589) and `ofSuppBddBelow_eq_zero` (:585). CURRENT STATE: unchanged since July; each carries the identical 6–8-line `Set.IsWF.isPWO; BddBelow.isWF; refine ⟨-N, ?_⟩; simp only [mem_support]; split_ifs/by_contra` block (162–169, 187–195, 303–311, 579–587).
- **Deeper**: `jIntegralLaurentSeriesWidth m` is `HahnSeries.embDomain` of `jIntegralLaurentSeries` along `k ↦ m·k`, `jLaurentSeriesMod p` is `embDomain` of `jUnitLaurentSeriesMod p`, and `transformedJSeries ζ σ`/`cyclotomicTransformedJSeries` are `embDomain` (by `a²`) of a phase-twisted unit series. Mathlib: `HahnSeries.embDomain (f : Γ ↪o Γ')` (Basic.lean:441), `embDomain_coeff` (:449), `embDomain_notin_range` (:477), `embDomain_add` (Addition.lean:294), `embDomain_mul` (Multiplication.lean:857), `orderTop_embDomain` (Basic.lean:505), and the bundled `HahnSeries.embDomainRingHom (f : Γ →+ Γ') (hfi) (hf : ∀ g g', f g ≤ f g' ↔ g ≤ g') : R⟦Γ⟧ →+* R⟦Γ'⟧` (Multiplication.lean:899) — the very construction mathlib uses for `ofPowerSeries` (HahnSeries/PowerSeries.lean:89). With `f = AddMonoidHom.mulLeft (m : ℤ)`, `jIntegralLaurentSeriesWidth_coeff_mul_map_complex` (204–226), `jUnitPrimeNormalForm_coeff_mul` (426–442), `_of_not_dvd` (444–458), `jIntegralLaurentSeriesWidth_map_zmod` (320–328) and `jLaurentSeriesMod_order` (339–359, via `orderTop_embDomain`) become one-liners from `embDomain_coeff`/`embDomain_notin_range`.
- `powerSeries_pow_prime_eq_expand` (282–297): `MvPowerSeries.map_frobenius_expand` (`Mathlib/RingTheory/MvPowerSeries/Expand.lean:232`, `[ExpChar R p]`) is used through the `PowerSeries = MvPowerSeries Unit` defeq (`@… Unit` + `change`, 286–289). There is NO `PowerSeries.map_frobenius_expand` (grep `frobenius` in `PowerSeries/Expand.lean`: none; the polynomial version is `Polynomial.map_frobenius_expand`/`expand_char`, Algebra/Polynomial/Expand.lean:262/270). `hmap` (290–295) = `ZMod.frobenius_zmod` (`Mathlib/FieldTheory/Finite/Basic.lean:593`, `@[simp]`) + `PowerSeries.map_id` (PowerSeries/Basic.lean:448). PR candidates: `PowerSeries.map_frobenius_expand`, `PowerSeries.map_iterateFrobenius_expand`.
- `HahnSeries.leadingCoeff_pow`: not in mathlib (grep `leadingCoeff_pow` in `Mathlib/RingTheory/HahnSeries/`: none); not needed in this file (only `_order`/`_leadingCoeff` of specific series).
- Order computations (263–280, 339–359): `HahnSeries.orderTop_eq_of_le` (Basic.lean:275), `order_eq_orderTop_of_ne_zero` (:370) used correctly; `HahnSeries.le_order_iff_forall (h : x ≠ 0) : i ≤ x.order ↔ ∀ j < i, x.coeff j = 0` (Basic.lean:552) + `order_le_of_coeff_ne_zero` (:383) gives `order = g` in one `le_antisymm`.
- `cyclotomicDescent_dvd` (669–694): all cited lemmas verified (`cyclotomic_eq_minpoly_rat` Cyclotomic/Roots.lean:178, `map_dvd_map` Algebra/Polynomial/Div.lean:415, `eval_one_cyclotomic_prime` Cyclotomic/Eval.lean:32, `eval_dvd` Eval/Defs.lean:691); ℤ-native alternative via `cyclotomic_eq_minpoly` (Roots.lean:171) + `minpoly.isIntegrallyClosed_dvd` (Minpoly/IsIntegrallyClosed.lean:71). No mathlib lemma states "`aeval ζ_p F ∈ ℤ ⇒ p ∣ F(1) − value`" directly (searched Cyclotomic/*.lean for `eval_one`, `sub_one_dvd`).
- `primeFinToCoxMatrix_*` (41–126): project-specific classification; `Fin.lastCases`, `Fin.eq_castSucc_or_eq_last` (Data/Fin/SuccPred.lean:195), `Equiv.ofBijective` used correctly; `card_coxMatrix` (CoxMatrices/Cardinality.lean:270) gives `Fintype.card (CoxMatrix p) = p + 1` but not the explicit enumeration.
- `specializeJMod_injective` (538–545): `Polynomial.map_injective` (Eval/Coeff.lean:103) — correct.
- `phasePolynomial_eval_zeta` (551–564): `zpow_eq_zpow_emod'` (Algebra/Group/Basic.lean:858), `Units.val_zpow_eq_zpow_val` (Algebra/Group/Units/Hom.lean:127) — correct.

### Missing API / repeated patterns
- **`by_cases -1 ≤ q` block** (217–226 ≡ 433–442): both derive `coeff (m*q)` of a width-`m` series; missing simp lemmas `jIntegralLaurentSeriesWidth_coeff_mul (m q) : coeff (m*q) = jIntCoeff q` and `jIntegralLaurentSeriesWidth_coeff_of_not_dvd`, and the `ZMod` twins for `jLaurentSeriesMod` (which are `embDomain_coeff`/`embDomain_notin_range` under the `embDomain` definition).
- **`order = g` skeleton** (263–280, 339–359; also DiagonalLaurent.lean:257–266, 65–77): helper `HahnSeries.order_eq_of_coeff_ne_zero_of_forall_lt (h : x.coeff g ≠ 0) (h' : ∀ i < g, x.coeff i = 0) : x.order = g := le_antisymm (order_le_of_coeff_ne_zero h) ((le_order_iff_forall (ne_zero_of_coeff_ne_zero h)).2 h')`.
- **`coeff (single (-N) 1 * ↑(F.expand N _)) k`** (389–458 here; KroneckerFrobenius.lean:104–139; LevelThree.lean:577–600, 609–635): one lemma `LaurentSeries.coeff_single_neg_mul_coe_expand` (statement in the KroneckerFrobenius inventory) replaces ≥ 5 blocks.
- **`F^(p^n) = expand (p^n) F` over `ZMod p`**: `n = 1` here (282–297), `n = 2` in KroneckerFrobenius.lean:141–155; state once with `n`.
- **`_map_complex`/`_map_mod` twins**: `cyclotomicTransformedJSeries_map_complex`/`_map_mod` (607–643) and `cyclotomicCoxPolynomial_map_complex`/`_map_mod` (651–666) are literally the same proofs with `(phaseEvalComplex, zeta p, phasePolynomial_eval_zeta)` vs `(phaseEvalMod, 1, phasePolynomial_eval_one)`; one `cyclotomicTransformedJSeries_map (φ : ℤ[X] →+* K) (ζ : K) (hφ : ∀ e, φ (phasePolynomial p e) = ζ ^ e) : laurentSeriesMapRingHom φ (cyclotomicTransformedJSeries p σ) = transformedJSeries ζ σ` and `cyclotomicCoxPolynomial_map` give all four. Likewise `specializeJIntegral_map_zmod`/`_map_complex` (496–526) are the same `simpa using bivariateSpecializeLaurent_map_apply` twice.
- Missing `@[simp]` on `jLaurentSeriesMod_coeff` (313) and `cyclotomicTransformedJSeries_coeff` (589) while `jIntegralLaurentSeries_coeff`, `jIntegralLaurentSeriesWidth_coeff`, `jUnitLaurentSeriesMod_coeff` are `@[simp]` (July flag; unchanged).
- `jLaurentSeriesMod p = transformedJSeries (1 : ZMod p) (sigmaZero p)` is never stated but is a direct `ext` from the two `_coeff` formulas (`a = p`, `b = 0`); with it, KroneckerFrobenius.lean:66–187 (the `unitJPowerSeries` route to `transformedJSeries 1 σ₀ = jLaurentSeriesMod^p`) could reuse `jUnitLaurentSeriesMod_pow_prime` directly.

### Junk candidates
- `jIntegralLaurentSeries_coeff` (172–174) and `jIntegralLaurentSeries_map_complex` (176–181): unused anywhere in the project (`grep -rnw`).
- `jIntegralLaurentSeries` (160–169) is the `m = 1` instance of `jIntegralLaurentSeriesWidth` (coefficients agree by `jIntCoeff_eq_zero_of_lt`); `jUnitLaurentSeriesMod p` could then be `(jIntegralLaurentSeriesWidth 1).map _`.
- `import XYin.PhD.Cox.LaurentPolynomialEvaluation` (line 9) is redundant (already imported by `DiagonalLaurent`, line 8 → DiagonalLaurent.lean:11).
- `primeCoxMatrixEquiv` (130–133) is only ever used through `.symm` (here 136–146; KroneckerFrobenius.lean:51–62); the double `symm` is avoidable by exposing `primeFinEquivCoxMatrix`.
- `[Fact (Nat.Prime p)]` unused in `jUnitPrimeNormalForm_coeff_of_not_dvd` (444–458).

### Moral duplicates within this batch
- `jUnitLaurentSeriesMod_order` (263–280) ≡ `jLaurentSeriesMod_order` (339–359) (same skeleton; hypotheses `Fact Prime` vs `1 < p`).
- `jIntegralLaurentSeriesWidth` (184–195) ≡ `jLaurentSeriesMod` (300–311) up to the coefficient ring (ℤ vs `ZMod p`); `jIntegralLaurentSeriesWidth_map_zmod` (320–328) is the witness.
- `jUnitLaurentSeriesMod_pow_prime_normalForm` (373–387) ≡ KroneckerFrobenius.lean `jUnitLaurentSeriesMod_eq_unitJPowerSeries` (77–96) + `unitJPowerSeries_pow_prime_sq_eq_expand` (141–155) (mathlib-native vs hand-rolled `powerSeriesPart`).
- `jUnitPrimeNormalForm_coeff_mul/_of_not_dvd` (426–458) ≡ KroneckerFrobenius.lean `transformedJSeries_one_sigmaZero_eq_expand` (104–139) with `N = p` vs `N = p²`.
- `cyclotomicTransformedJSeries` (572–587) ≡ `transformedJSeries` (CoxMatrices/LaurentExpansion.lean:50–63) with `ζ^e` replaced by `phasePolynomial p e`.

### Generalization notes
- **One parametric width-`m` series**: `jLaurentSeriesWidth (R : Type*) [Ring R] (m : ℕ+) : LaurentSeries R` with coefficient `(jIntCoeff (k/m) : R)` on `m ∣ k ≥ -m` gives `jIntegralLaurentSeries = jLaurentSeriesWidth ℤ 1`, `jIntegralLaurentSeriesWidth m = jLaurentSeriesWidth ℤ m`, `jUnitLaurentSeriesMod p = jLaurentSeriesWidth (ZMod p) 1`, `jLaurentSeriesMod p = jLaurentSeriesWidth (ZMod p) p`, with a single `map` lemma `(jLaurentSeriesWidth R m).map f = jLaurentSeriesWidth S m` replacing `jUnitLaurentSeriesMod`'s definition and `jIntegralLaurentSeriesWidth_map_zmod`, and `_coeff_neg`/`_order`/`_leadingCoeff` proved once for `[Nontrivial R]` (replacing 252–280 and 330–364). KroneckerFrobenius's `unitJPowerSeries K` is then `(jLaurentSeriesWidth K 1).powerSeriesPart`.
- **Phase-generalised `transformedJSeries`**: `transformedJSeries` needs `Field K` only for `ζ ^ (e : ℤ)`; taking the phase as a hom `φ : Multiplicative ℤ →* K` (or `ℤ → K` with `φ (e₁ + e₂) = φ e₁ * φ e₂`) makes `cyclotomicTransformedJSeries p σ` the instance `φ e := phasePolynomial p e` over `ℤ[X]`, and `_map_complex`/`_map_mod` become one `transformedJSeries_map` lemma (which `FormalCoxProduct.lean:31` already has as private `transformedJSeries_map` for field-to-field maps).
- `jUnitLaurentSeriesMod_order` (263), `jUnitPrimeNormalForm_coeff_mul_of_lower` (389), `_coeff_mul` (426): `[Fact (Nat.Prime p)]` is used only for `Nontrivial (ZMod p)`; `(hp : 1 < p)` as in `jLaurentSeriesMod_order` suffices. `powerSeries_pow_prime_eq_expand` and `jUnitLaurentSeriesMod_pow_prime` genuinely need primality (`ExpChar`, `ZMod.pow_card`).
- `cyclotomicDescent_dvd/_zmod` (669–702) hold for any `Polynomial ℤ` and any primitive `p`-th root in any field of characteristic zero; `zeta p : ℂ` is incidental.
