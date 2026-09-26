# Inventory: XYin/PhD/Cox/KroneckerFrobenius.lean  (233 lines)

Completes Cox Theorem 11.18(v) (Kronecker's congruence `Φ_p(X,Y) ≡ (X^p − Y)(X − Y^p) mod p`). At prime level with the cyclotomic phase set to `1`, the `p` lower Cox roots all equal the unit-step reduction of `j`, the distinguished root `σ₀` is their `p²`-th power (via `PowerSeries.expand` and Frobenius over `ZMod p`), and `(X − F)^p = X^p − F^p` in characteristic `p` gives the factorisation; injectivity of `specializeJMod` (Kronecker.lean) lifts it back to `ZMod p[X][Y]`.

## Declarations

### `theorem Cox.transformedJSeries_one_primeLower_eq_jUnit`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (i : Fin (p : ℕ)) : transformedJSeries (1 : ZMod p) (primeLowerCoxMatrix p i) = jUnitLaurentSeriesMod p`
- **What**: With phase `1`, the root series of every lower representative `(1,i;0,p)` is the reduction mod `p` of the integral `j`-series (all `p` lower roots coincide).
- **How**: coefficientwise: `a = 1` kills the divisibility and phase conditions in `transformedJSeries_coeff`; for `k < -1` both sides vanish by `jIntCoeff_eq_zero_of_lt`.
- **Hypotheses**: `p` prime (NOT used: the computation is valid for every `p : ℕ+`).
- **Uses from project**: `transformedJSeries`, `transformedJSeries_coeff`, `primeLowerCoxMatrix`, `jUnitLaurentSeriesMod`, `jUnitLaurentSeriesMod_coeff`, `jIntCoeff_eq_zero_of_lt`
- **Used by**: `formalCoxPolynomial_prime_one_factorization`, `transformedJSeries_one_sigmaZero_eq_primeLower_pow`
- **Visibility**: public
- **Lines**: 26–37, proof ≈ 8 lines
- **Notes**: `[Fact (Nat.Prime p)]` is superfluous.

### `theorem Cox.formalCoxPolynomial_prime_one_factorization`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : formalCoxPolynomial p (1 : ZMod p) = (X − C (jUnitLaurentSeriesMod p)) ^ (p : ℕ) * (X − C (transformedJSeries 1 (sigmaZero p)))`
- **What**: At prime level and phase one the formal Cox product is a `p`-fold repeated factor times the `σ₀` factor.
- **How**: reindex the product over `CoxMatrix p` along `primeCoxMatrixEquiv` (`Equiv.prod_comp`), split off the last index with `Fin.prod_univ_castSucc` (Algebra/BigOperators/Fin.lean:84), identify the first `p` factors by `primeCoxMatrixEquiv_symm_apply_of_lt` + `transformedJSeries_one_primeLower_eq_jUnit` and collapse them with `Fin.prod_const`.
- **Hypotheses**: `p` prime (needed for `primeCoxMatrixEquiv`).
- **Uses from project**: `formalCoxPolynomial`, `jUnitLaurentSeriesMod`, `transformedJSeries`, `sigmaZero`, `CoxMatrix`, `primeCoxMatrixEquiv`, `primeCoxMatrixEquiv_symm_apply_of_lt`, `primeCoxMatrixEquiv_symm_apply_last`, `primeLowerCoxMatrix`, `transformedJSeries_one_primeLower_eq_jUnit`
- **Used by**: `formalCoxPolynomial_prime_one_frobenius`
- **Visibility**: public
- **Lines**: 41–64, proof ≈ 20 lines
- **Notes**: none.

### `def Cox.unitJPowerSeries` (private)
- **Type**: `(K : Type*) [Ring K] : PowerSeries K`
- **What**: The power series `∑ jIntCoeff(n−1) q^n`, i.e. `q · j(q)` with coefficients cast to `K`.
- **How**: `PowerSeries.mk fun n ↦ (jIntCoeff (n − 1) : K)`.
- **Hypotheses**: none.
- **Uses from project**: `jIntCoeff`
- **Used by**: `unitJPowerSeries_coeff`, `jUnitLaurentSeriesMod_eq_unitJPowerSeries`, `transformedJSeries_one_sigmaZero_eq_expand`, `unitJPowerSeries_pow_prime_sq_eq_expand`, `transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq`
- **Visibility**: private
- **Lines**: 66–68
- **Notes**: identical to LevelThree.lean:132–133 `qjIntegralPowerSeriesThree : PowerSeries ℤ := PowerSeries.mk fun n ↦ jIntCoeff (n − 1)` (the `K = ℤ` case). It equals `(jUnitLaurentSeriesMod p).powerSeriesPart` (mathlib `LaurentSeries.powerSeriesPart_coeff`, LaurentSeries.lean:215, plus `jUnitLaurentSeriesMod_order = -1`).

### `theorem Cox.unitJPowerSeries_coeff` (private)
- **Type**: `{K} [Ring K] (n : ℕ) : PowerSeries.coeff n (unitJPowerSeries K) = (jIntCoeff ((n : ℤ) − 1) : K)`
- **What**: Coefficient formula.
- **How**: `simp [unitJPowerSeries]` (`PowerSeries.coeff_mk`).
- **Hypotheses**: none.
- **Uses from project**: `unitJPowerSeries`, `jIntCoeff`
- **Used by**: `jUnitLaurentSeriesMod_eq_unitJPowerSeries`, `transformedJSeries_one_sigmaZero_eq_expand`
- **Visibility**: private
- **Lines**: 71–75, proof 1 line
- **Notes**: `@[simp]`.

### `theorem Cox.jUnitLaurentSeriesMod_eq_unitJPowerSeries` (private)
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : jUnitLaurentSeriesMod p = HahnSeries.single (-1 : ℤ) 1 * (unitJPowerSeries (ZMod p) : LaurentSeries (ZMod p))`
- **What**: The unit-step reduced `j`-series is `q^{-1}` times the power series `unitJPowerSeries`.
- **How**: `ext k`; `HahnSeries.coeff_single_mul` (Multiplication.lean:471) shifts by `1`; `PowerSeries.coeff_coe` (LaurentSeries.lean:335) splits on the sign of `k + 1`; for `k ≥ -1` `unitJPowerSeries_coeff` + `Int.natAbs_of_nonneg`; for `k < -1` both sides vanish (`jIntCoeff_eq_zero_of_lt`).
- **Hypotheses**: `p` prime (NOT used).
- **Uses from project**: `jUnitLaurentSeriesMod`, `unitJPowerSeries`, `jUnitLaurentSeriesMod_coeff`, `unitJPowerSeries_coeff`, `jIntCoeff_eq_zero_of_lt`
- **Used by**: `transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq`
- **Visibility**: private
- **Lines**: 77–96, proof ≈ 16 lines
- **Notes**: re-proves mathlib's `LaurentSeries.single_order_mul_powerSeriesPart` (LaurentSeries.lean:237) for this series; Kronecker.lean:377–378 already invokes that mathlib lemma for the SAME series (`hdecomp`).

### `theorem Cox.prime_sq_dvd_iff_dvd_shift_natAbs` (private)
- **Type**: `(p : ℕ+) (k : ℤ) : ((p : ℤ) ^ 2 ∣ k) ↔ (p : ℕ) ^ 2 ∣ (k − -((p : ℤ) ^ 2)).natAbs`
- **What**: `p² ∣ k` iff `p² ∣ |k + p²|`.
- **How**: `Int.natCast_dvd`, `Int.natCast_pow`, `dvd_add_self_right`.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: `transformedJSeries_one_sigmaZero_eq_expand`
- **Visibility**: private
- **Lines**: 98–102, proof 1 line
- **Notes**: same statement as LevelThree.lean:569 `three_dvd_iff_dvd_shift_natAbs` and :573 `nine_dvd_iff_dvd_shift_natAbs` with `N = 3, 9`; one general `(N : ℤ) ∣ k ↔ N ∣ (k + N).natAbs` serves all three.

### `theorem Cox.transformedJSeries_one_sigmaZero_eq_expand` (private)
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : transformedJSeries (1 : ZMod p) (sigmaZero p) = HahnSeries.single (-((p : ℤ) ^ 2)) 1 * ((unitJPowerSeries (ZMod p)).expand (p ^ 2) _ : LaurentSeries (ZMod p))`
- **What**: The phase-one `σ₀` root series is `q^{-p²}` times the `p²`-fold expansion of `unitJPowerSeries` (Cox (11.13) with `a = p`, `b = 0`).
- **How**: `ext k`; `HahnSeries.coeff_single_mul`, `PowerSeries.coeff_coe`, `PowerSeries.coeff_expand` (PowerSeries/Expand.lean:110); case split on `-p² ≤ k` and on `p² ∣ k` (`prime_sq_dvd_iff_dvd_shift_natAbs`), with `Int.mul_ediv_cancel_left` to match `jIntCoeff (k / p²)` against `jIntCoeff ((k + p²)/p² − 1)`.
- **Hypotheses**: `p` prime (NOT used).
- **Uses from project**: `transformedJSeries`, `transformedJSeries_coeff`, `sigmaZero`, `unitJPowerSeries`, `unitJPowerSeries_coeff`, `prime_sq_dvd_iff_dvd_shift_natAbs`
- **Used by**: `transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq`
- **Visibility**: private
- **Lines**: 104–139, proof ≈ 31 lines
- **Notes**: proof >30 lines. Same skeleton as Kronecker.lean:389–458 (`jUnitPrimeNormalForm_coeff_mul_of_lower/_of_lt/_of_not_dvd`, `N = p`) and LevelThree.lean:577–600, 609–635 (`N = 3, 9`).

### `theorem Cox.unitJPowerSeries_pow_prime_sq_eq_expand` (private)
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : unitJPowerSeries (ZMod p) ^ ((p : ℕ) ^ 2) = (unitJPowerSeries (ZMod p)).expand (p ^ 2) _`
- **What**: Over `ZMod p`, raising to the `p²` is the `p²`-fold expansion (Frobenius is the identity on coefficients).
- **How**: `MvPowerSeries.map_iterateFrobenius_expand` (MvPowerSeries/Expand.lean:247) with `n = 2`, after showing `iterateFrobenius (ZMod p) p 2 = RingHom.id` by `ZMod.pow_card_pow` (FieldTheory/Finite/Basic.lean:587) and `MvPowerSeries.map_id` (MvPowerSeries/Basic.lean:525).
- **Hypotheses**: `p` prime.
- **Uses from project**: `unitJPowerSeries`
- **Used by**: `transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq`
- **Visibility**: private
- **Lines**: 141–155, proof ≈ 12 lines
- **Notes**: the `n = 2` instance of Kronecker.lean:282–297 `powerSeries_pow_prime_eq_expand` (`n = 1`); the two use different mathlib entry points (`map_frobenius_expand` vs `map_iterateFrobenius_expand`). Relies on the defeq `PowerSeries R = MvPowerSeries Unit R`.

### `theorem Cox.transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq` (private)
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : transformedJSeries (1 : ZMod p) (sigmaZero p) = jUnitLaurentSeriesMod p ^ ((p : ℕ) ^ 2)`
- **What**: The `σ₀` root is the `p²`-th power of the unit-step reduced `j`-series.
- **How**: combine the two expansion identities; `mul_pow`, `HahnSeries.single_pow` (Multiplication.lean:795), `PowerSeries.coe_pow`.
- **Hypotheses**: `p` prime.
- **Uses from project**: `transformedJSeries`, `sigmaZero`, `jUnitLaurentSeriesMod`, `transformedJSeries_one_sigmaZero_eq_expand`, `jUnitLaurentSeriesMod_eq_unitJPowerSeries`, `unitJPowerSeries_pow_prime_sq_eq_expand`
- **Used by**: `transformedJSeries_one_sigmaZero_eq_primeLower_pow`, `transformedJSeries_one_sigmaZero_eq_jLaurent_pow`
- **Visibility**: private
- **Lines**: 157–165, proof ≈ 6 lines
- **Notes**: none.

### `theorem Cox.transformedJSeries_one_sigmaZero_eq_primeLower_pow`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] (i : Fin p) : transformedJSeries 1 (sigmaZero p) = transformedJSeries 1 (primeLowerCoxMatrix p i) ^ ((p : ℕ) ^ 2)`
- **What**: The distinguished root is the `p²`-th power of each lower root.
- **How**: `transformedJSeries_one_primeLower_eq_jUnit` + `_eq_jUnit_pow_sq`.
- **Hypotheses**: `p` prime.
- **Uses from project**: `transformedJSeries`, `sigmaZero`, `primeLowerCoxMatrix`, `transformedJSeries_one_primeLower_eq_jUnit`, `transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq`
- **Used by**: unused in file (no other file uses it either)
- **Visibility**: public
- **Lines**: 168–174, proof 2 lines
- **Notes**: unused anywhere in the project; documentary restatement.

### `theorem Cox.transformedJSeries_one_sigmaZero_eq_jLaurent_pow`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : transformedJSeries 1 (sigmaZero p) = jLaurentSeriesMod p ^ (p : ℕ)`
- **What**: The distinguished root is the `p`-th power of the width-`p` reduced `j`-series.
- **How**: `p² = p·p`, `pow_mul`, then `jUnitLaurentSeriesMod_pow_prime` (`(jUnit)^p = jLaurentSeriesMod`).
- **Hypotheses**: `p` prime.
- **Uses from project**: `transformedJSeries`, `sigmaZero`, `jLaurentSeriesMod`, `jUnitLaurentSeriesMod`, `transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq`, `jUnitLaurentSeriesMod_pow_prime`
- **Used by**: `formalCoxPolynomial_prime_one_frobenius`
- **Visibility**: public
- **Lines**: 177–187, proof ≈ 8 lines
- **Notes**: none.

### `theorem Cox.formalCoxPolynomial_prime_one_frobenius`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : formalCoxPolynomial p (1 : ZMod p) = (X ^ (p : ℕ) − C (jLaurentSeriesMod p)) * (X − C (jLaurentSeriesMod p ^ (p : ℕ)))`
- **What**: Kronecker's factorisation of the formal Cox product in characteristic `p`.
- **How**: install `CharP (LaurentSeries (ZMod p)) p` via `charP_of_injective_ringHom` (CharP/Algebra.lean:56) with `HahnSeries.C_injective` (Multiplication.lean:828); rewrite by the factorisation lemma and `_eq_jLaurent_pow`; `sub_pow_char` (CharP/Lemmas.lean:262) turns `(X − C F)^p` into `X^p − C (F^p)` and `jUnitLaurentSeriesMod_pow_prime` identifies `F^p`.
- **Hypotheses**: `p` prime.
- **Uses from project**: `formalCoxPolynomial`, `jLaurentSeriesMod`, `formalCoxPolynomial_prime_one_factorization`, `transformedJSeries_one_sigmaZero_eq_jLaurent_pow`, `jUnitLaurentSeriesMod_pow_prime`
- **Used by**: `kronecker_after_specializeJ`
- **Visibility**: public
- **Lines**: 190–200, proof ≈ 6 lines
- **Notes**: `letI` for the `CharP` instance; mathlib has no `CharP` instance on `HahnSeries`/`LaurentSeries` (grep `CharP`, `ExpChar` in `Mathlib/RingTheory/HahnSeries/`, `LaurentSeries.lean`: none) — small upstream candidate.

### `theorem Cox.kronecker_after_specializeJ`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : specializeJMod p (map (Int.castRingHom (ZMod p)) (modularPolynomial p)) = specializeJMod p (varX ^ p − varY) * specializeJMod p (varX − varY ^ p)`
- **What**: After substituting the width-`p` series of `j` for `Y`, the reduced modular polynomial factors as Kronecker predicts.
- **How**: `specializeJMod_modularPolynomial_eq_formal` + `formalCoxPolynomial_prime_one_frobenius`, then `simp` (using the `@[simp]` lemmas `specializeJMod_varX/_varY` and `map_sub/map_pow`).
- **Hypotheses**: `p` prime.
- **Uses from project**: `specializeJMod`, `BivariatePolynomial.map`, `modularPolynomial`, `BivariatePolynomial.varX`, `BivariatePolynomial.varY`, `specializeJMod_modularPolynomial_eq_formal`, `formalCoxPolynomial_prime_one_frobenius`, (implicitly via simp) `specializeJMod_varX`, `specializeJMod_varY`
- **Used by**: `theorem_11_18_v`
- **Visibility**: public
- **Lines**: 204–218, proof ≈ 3 lines
- **Notes**: none.

### `theorem Cox.theorem_11_18_v`
- **Type**: `(p : ℕ+) [Fact (Nat.Prime p)] : BivariatePolynomial.map (Int.castRingHom (ZMod p)) (modularPolynomial p) = (varX ^ p − varY) * (varX − varY ^ p)`
- **What**: Cox Theorem 11.18(v), Kronecker's congruence `Φ_p(X,Y) ≡ (X^p − Y)(X − Y^p) (mod p)`.
- **How**: `specializeJMod_injective` (Hasse principle) applied to `kronecker_after_specializeJ` after `map_mul`.
- **Hypotheses**: `p` prime.
- **Uses from project**: `BivariatePolynomial.map`, `modularPolynomial`, `BivariatePolynomial.varX`, `BivariatePolynomial.varY`, `specializeJMod_injective`, `kronecker_after_specializeJ`
- **Used by**: unused in file (headline result; no consumer)
- **Visibility**: public
- **Lines**: 221–231, proof 2 lines
- **Notes**: none.

## File Summary
- Total declarations: 14 (1 def, 13 theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `unitJPowerSeries` (5), `transformedJSeries_one_sigmaZero_eq_jUnit_pow_sq` (2), `transformedJSeries_one_primeLower_eq_jUnit` (2)
- Unused declarations (not used by anything in this file): `transformedJSeries_one_sigmaZero_eq_primeLower_pow` (unused project-wide), `theorem_11_18_v` (headline)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `transformedJSeries_one_sigmaZero_eq_expand` (≈ 31)

## Observations

### Mathlib API candidates
- `jUnitLaurentSeriesMod_eq_unitJPowerSeries` (77–96) + `unitJPowerSeries` (66–68): mathlib `LaurentSeries.powerSeriesPart` (LaurentSeries.lean:210), `powerSeriesPart_coeff` (:215), `single_order_mul_powerSeriesPart` (:237) give `jUnitLaurentSeriesMod p = single (-1) 1 * ↑(powerSeriesPart _)` directly once `order = -1` is known (Kronecker.lean `jUnitLaurentSeriesMod_order`); Kronecker.lean:377 already does exactly this. Replace `unitJPowerSeries (ZMod p)` by `(jUnitLaurentSeriesMod p).powerSeriesPart`.
- `unitJPowerSeries_pow_prime_sq_eq_expand` (141–155): `MvPowerSeries.map_iterateFrobenius_expand` (MvPowerSeries/Expand.lean:247, `[ExpChar R p]`) is the right tool; mathlib has NO single-variable `PowerSeries.map_frobenius_expand`/`map_iterateFrobenius_expand` (grep `frobenius` in `Mathlib/RingTheory/PowerSeries/Expand.lean`: none), only the `MvPowerSeries` and `Polynomial` (`Polynomial.map_frobenius_expand`/alias `expand_char`, Algebra/Polynomial/Expand.lean:262/270; `map_expand_pow_char` :283) versions. `ZMod.frobenius_zmod` (FieldTheory/Finite/Basic.lean:593, `@[simp]`: `frobenius (ZMod p) p = RingHom.id _`) would replace the `hiter` block once an `iterateFrobenius` analogue is available; `ZMod.pow_card_pow` (:587) as used is fine.
- `formalCoxPolynomial_prime_one_frobenius` (195–197): `charP_of_injective_ringHom` + `HahnSeries.C_injective` — correct; a `CharP R p → CharP R⟦Γ⟧ p` instance is absent from mathlib (verified) and would remove the `letI`.
- `formalCoxPolynomial_prime_one_factorization` (41–64): `Equiv.prod_comp`, `Fin.prod_univ_castSucc` (BigOperators/Fin.lean:84), `Fin.prod_const` — correct.
- `prime_sq_dvd_iff_dvd_shift_natAbs` (98–102): `Int.natCast_dvd` + `dvd_add_self_right`; no mathlib lemma in this exact shape (searched `natCast_dvd_natAbs`, `dvd_natAbs_add`): none.

### Missing API / repeated patterns
- **`coeff (single (-N) 1 * ↑(F.expand N _)) k` computation** appears with the same 20–30-line skeleton (`ext`; `coeff_single_mul`; `PowerSeries.coeff_coe`; split `-N ≤ k`; `PowerSeries.coeff_expand`; split `N ∣ k`; `Int.mul_ediv_cancel_left`; else `embDomain_notin_range`/`coeff_coe` `if_pos`) in: this file 104–139 (`N = p²`), Kronecker.lean 389–458 (`N = p`, three lemmas), LevelThree.lean 577–600 (`N = 3`) and 609–635 (`N = 9`). One lemma `LaurentSeries.coeff_single_neg_mul_coe_expand (N : ℕ) (hN : N ≠ 0) (F : R⟦X⟧) (k : ℤ) : (single (-(N:ℤ)) 1 * ↑(F.expand N hN)).coeff k = if (N:ℤ) ∣ k ∧ -(N:ℤ) ≤ k then PowerSeries.coeff (k / N + 1).toNat F else 0` collapses all five sites to `rw`+`split_ifs`.
- **`F ^ (p^n) = F.expand (p^n)` over `ZMod p`**: `n = 1` at Kronecker.lean:282–297, `n = 2` here at 141–155, proved separately with different mathlib lemmas. One `PowerSeries.pow_prime_pow_eq_expand (F : PowerSeries (ZMod p)) (n : ℕ) : F ^ p ^ n = F.expand (p ^ n) _` (from `map_iterateFrobenius_expand` + `ZMod.pow_card_pow`) gives both. CURRENT STATE: still two proofs (July flagged).
- **`N ∣ k ↔ N ∣ (k + N).natAbs`**: three private copies (here 98–102; LevelThree.lean:569, 573).

### Junk candidates
- `transformedJSeries_one_sigmaZero_eq_primeLower_pow` (168–174): unused project-wide (`grep -rnw`: only its own definition).
- `unitJPowerSeries` + `unitJPowerSeries_coeff` + `jUnitLaurentSeriesMod_eq_unitJPowerSeries` (66–96): replaceable by mathlib `powerSeriesPart` machinery already used in Kronecker.lean:373–387.
- Import `Mathlib.Algebra.BigOperators.Fin` (line 6) is likely already transitive via `Mathlib.RingTheory.LaurentSeries`; harmless.

### Moral duplicates within this batch
- `unitJPowerSeries` (66–68) ≡ LevelThree.lean:132–133 `qjIntegralPowerSeriesThree` (over ℤ) ≡ `(jIntegralLaurentSeries).powerSeriesPart` ≡ `(jUnitLaurentSeriesMod p).powerSeriesPart`.
- `jUnitLaurentSeriesMod_eq_unitJPowerSeries` (77–96) ≡ Kronecker.lean:377–378 (`single_order_mul_powerSeriesPart` + `jUnitLaurentSeriesMod_order`), same series.
- `transformedJSeries_one_sigmaZero_eq_expand` (104–139) ≡ Kronecker.lean `jUnitLaurentSeriesModPrimeNormalForm` (366–371) + `jUnitPrimeNormalForm_coeff_mul/_of_not_dvd` (426–458): both say "the `a²`-expanded unit series is `single (-a²) 1 * ↑(expand a² F)`" for `a = p` resp. the general `transformedJSeries` at `a = p`; indeed `jLaurentSeriesMod p = transformedJSeries 1 (sigmaZero p)` is never stated but follows by `ext` from `jLaurentSeriesMod_coeff` and `transformedJSeries_coeff`, which would let `transformedJSeries_one_sigmaZero_eq_jLaurent_pow` reuse `jUnitLaurentSeriesMod_pow_prime` after one more `pow` — bypassing 66–165 entirely.
- `unitJPowerSeries_pow_prime_sq_eq_expand` (141–155) ≡ Kronecker.lean `powerSeries_pow_prime_eq_expand` (282–297) at `n = 2`.

### Generalization notes
- `[Fact (Nat.Prime p)]` is unused in `transformedJSeries_one_primeLower_eq_jUnit` (26–37), `jUnitLaurentSeriesMod_eq_unitJPowerSeries` (77–96) and `transformedJSeries_one_sigmaZero_eq_expand` (104–139): all three are pure coefficient identities valid for every `p : ℕ+` (compare Kronecker.lean `jLaurentSeriesMod_order` which correctly takes only `1 < p`).
- `unitJPowerSeries (K) [Ring K]` is fine; `Semiring K` would do (`Int.cast` needs `IntCast`, i.e. `Ring`, so keep).
- `formalCoxPolynomial_prime_one_frobenius` uses characteristic `p` only through `sub_pow_char`; it holds verbatim for the formal product over any `CharP K p` field once `(jUnit)^p = jLaurentSeriesMod` is available (which is `ZMod p`-specific).
