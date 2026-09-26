# Inventory: XYin/PhD/Cox/DiagonalLaurent.lean  (293 lines)

Cox equation (11.19): in the width-`m` local parameter the analytic `j` has order `-m` with leading coefficient one, each transformed root series has order `-σ.a²` with leading coefficient a phase `ζ^(-ab)`, so for nonsquare `m` every diagonal factor `j − j∘σ` has a `2m`-th root of unity as leading coefficient, hence so does the diagonal `Φ_m(X,X)`. Along the way it identifies the formal Cox polynomial with `Φ_m` specialised at the width-`m` Laurent series of `j`.

## Declarations

### `theorem Cox.j_widthM_cuspMeromorphicAt` (private)
- **Type**: `(m : ℕ+) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) j) 0`
- **What**: The width-`m` cusp function of `j` is meromorphic at `0`.
- **How**: third component of `j_cuspData m` specialised at `1`.
- **Hypotheses**: none.
- **Uses from project**: `cuspFunction`, `j`, `j_cuspData`
- **Used by**: `laurentqExpansion_j_order_widthM`, `laurentqExpansion_j_pow_widthM`
- **Visibility**: private
- **Lines**: 28–30, proof 1 line
- **Notes**: none.

### `theorem Cox.laurentqExpansion_j_order_widthM`
- **Type**: `(m : ℕ+) : (laurentqExpansion ((m : ℕ) : ℝ) j).order = -(m : ℤ)`
- **What**: In the parameter `q^(1/m)`, `j` has a pole of order exactly `m`.
- **How**: `poleOrder_nat_mul` scales `j_poleOrder = 1` to `m`; `laurentqExpansion.poleOrder_to_order` converts pole order to Hahn-series order; `omega` fixes signs.
- **Hypotheses**: none.
- **Uses from project**: `laurentqExpansion`, `j`, `poleOrder`, `j_poleOrder`, `poleOrder_nat_mul`, `j_cuspFunction_meromorphicAt`, `ModularFunction.j_periodic`, `laurentqExpansion.poleOrder_to_order`, `j_widthM_cuspMeromorphicAt`
- **Used by**: `laurentqExpansion_j_leadingCoeff_widthM`, `cox_diagonal_factor_leadingCoeff`, `laurentqExpansion_j_pow_order_widthM`, `eval₂_laurentqExpansion_j_coeff_widthM`
- **Visibility**: public
- **Lines**: 33–41, proof ≈ 7 lines
- **Notes**: width-1 twin `laurentqExpansion_j_order_aux` at IntegralDescent.lean:54–59; width-3 wrapper `laurentqExpansion_j_order_three` at LevelThree.lean:715–719.

### `theorem Cox.laurentqExpansion_j_leadingCoeff_widthM`
- **Type**: `(m : ℕ+) : (laurentqExpansion ((m : ℕ) : ℝ) j).leadingCoeff = 1`
- **What**: The leading coefficient of `j` at width `m` is one.
- **How**: `HahnSeries.leadingCoeff_eq` + the order lemma reduce to the coefficient at `-m`; `laurentqExpansion_nat_mul_coeff` identifies it with the width-1 coefficient at `-1`, which is `jIntCoeff (-1) = 1` (`jIntCoeff_spec`, `jIntCoeff_neg_one`).
- **Hypotheses**: none.
- **Uses from project**: `laurentqExpansion_j_order_widthM`, `laurentqExpansion_nat_mul_coeff`, `j_cuspFunction_meromorphicAt`, `ModularFunction.j_periodic`, `jIntCoeff_spec`, `jIntCoeff_neg_one`
- **Used by**: `cox_diagonal_factor_leadingCoeff`, `eval₂_laurentqExpansion_j_coeff_widthM`
- **Visibility**: public
- **Lines**: 44–54, proof ≈ 9 lines
- **Notes**: width-1 twin `laurentqExpansion_j_leadingCoeff_aux` IntegralDescent.lean:61–64; width-3 wrapper LevelThree.lean:721–725.

### `theorem Cox.transformedJSeries_coeff_order` (private)
- **Type**: `{K} [Field K] {m : ℕ+} (ζ : K) (σ : CoxMatrix m) : (transformedJSeries ζ σ).coeff (-((σ.a : ℤ) ^ 2)) = ζ ^ (-((σ.a : ℤ) * (σ.b : ℤ)))`
- **What**: The coefficient at exponent `-a²` of the transformed root series is the phase `ζ^(-ab)`.
- **How**: unfold `transformedJSeries_coeff`; the `if` is satisfied since `a² ∣ -a²`, then `jIntCoeff_neg_one` and `simp`.
- **Hypotheses**: none (uses `σ.a_pos` for `a² ≠ 0`).
- **Uses from project**: `transformedJSeries`, `transformedJSeries_coeff`, `CoxMatrix`, `jIntCoeff_neg_one`
- **Used by**: `transformedJSeries_order`, `transformedJSeries_leadingCoeff`
- **Visibility**: private
- **Lines**: 56–62, proof ≈ 3 lines
- **Notes**: none.

### `theorem Cox.transformedJSeries_order`
- **Type**: `{K} [Field K] {m : ℕ+} (ζ : K) (hζ : ζ ≠ 0) (σ : CoxMatrix m) : (transformedJSeries ζ σ).order = -((σ.a : ℤ) ^ 2)`
- **What**: For a nonzero phase the transformed root series has order exactly `-a²`.
- **How**: `≤` by `HahnSeries.order_le_of_coeff_ne_zero` (coefficient is `ζ^(-ab) ≠ 0` via `zpow_ne_zero`); `≥` since the coefficient at the order is nonzero (`HahnSeries.coeff_order_eq_zero`) and the `if` in `transformedJSeries_coeff` forces `-a² ≤ order`.
- **Hypotheses**: `ζ ≠ 0`.
- **Uses from project**: `transformedJSeries_coeff_order`, `transformedJSeries_coeff`
- **Used by**: `transformedJSeries_leadingCoeff`, `cox_diagonal_factor_leadingCoeff`
- **Visibility**: public
- **Lines**: 65–77, proof ≈ 11 lines
- **Notes**: shorter than July (19 → 11 lines). Also used by LevelThree.lean.

### `theorem Cox.transformedJSeries_leadingCoeff`
- **Type**: `(ζ : K) (hζ : ζ ≠ 0) (σ : CoxMatrix m) : (transformedJSeries ζ σ).leadingCoeff = ζ ^ (-((σ.a : ℤ) * (σ.b : ℤ)))`
- **What**: The leading coefficient of the transformed root series is its Cox (11.13) phase.
- **How**: `HahnSeries.leadingCoeff_eq` + `transformedJSeries_order` + `transformedJSeries_coeff_order`.
- **Hypotheses**: `ζ ≠ 0`.
- **Uses from project**: `transformedJSeries_order`, `transformedJSeries_coeff_order`
- **Used by**: `cox_diagonal_factor_leadingCoeff`
- **Visibility**: public
- **Lines**: 80–85, proof 2 lines
- **Notes**: none.

### `theorem Cox.cox_diagonal_factor_leadingCoeff`
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) (σ : CoxMatrix m) : (laurentqExpansion m j − transformedJSeries (zeta m) σ).leadingCoeff = if σ.a ^ 2 < m then 1 else -(zeta m ^ (-((σ.a : ℤ) * (σ.b : ℤ))))`
- **What**: Cox (11.19): the leading coefficient of a diagonal factor is `1` when `j` dominates (`a² < m`) and `-ζ^(-ab)` when the root dominates (`a² > m`); `a² = m` is excluded by nonsquareness.
- **How**: both series are nonzero (`leadingCoeff_ne_zero`), their `orderTop`s are `-m`, `-a²` (`order_eq_orderTop_of_ne_zero`); `a² ≠ m` from `isSquare_iff_exists_sq`; then `HahnSeries.leadingCoeff_sub` (needs strict `orderTop` comparison, checked by `norm_cast; omega`) in the `a² < m` case, and in the other case rewrite `J − T = -(T − J)` and use `HahnSeries.leadingCoeff_neg` + `leadingCoeff_sub`.
- **Hypotheses**: `m` not a perfect square.
- **Uses from project**: `laurentqExpansion`, `j`, `transformedJSeries`, `zeta`, `zeta_isPrimitiveRoot`, `laurentqExpansion_j_leadingCoeff_widthM`, `laurentqExpansion_j_order_widthM`, `transformedJSeries_leadingCoeff`, `transformedJSeries_order`, `CoxMatrix`
- **Used by**: `cox_diagonal_factor_leadingCoeff_pow`
- **Visibility**: public
- **Lines**: 89–135, proof ≈ 41 lines
- **Notes**: proof >30 lines. Lines 105–112 exist only to translate `order` into `orderTop` for mathlib's `leadingCoeff_sub`.

### `theorem Cox.cox_diagonal_factor_leadingCoeff_pow`
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) (σ : CoxMatrix m) : (laurentqExpansion m j − transformedJSeries (zeta m) σ).leadingCoeff ^ (2 * (m : ℕ)) = 1`
- **What**: Every diagonal factor's leading coefficient is a `2m`-th root of unity.
- **How**: split on the previous lemma; `1^k = 1`; otherwise `(zeta m ^ e)^m = 1` by `(zeta_isPrimitiveRoot m).zpow_eq_one` and `zpow_mul`, and the sign dies under the even exponent `2m` (`Even.neg_pow`).
- **Hypotheses**: `m` nonsquare.
- **Uses from project**: `cox_diagonal_factor_leadingCoeff`, `zeta`, `zeta_isPrimitiveRoot`
- **Used by**: `diagonal_cox_product_leadingCoeff_pow`
- **Visibility**: public
- **Lines**: 138–150, proof ≈ 9 lines
- **Notes**: none.

### `theorem Cox.laurentqExpansion_j_pow_widthM` (private)
- **Type**: `(m : ℕ+) (n : ℕ) : laurentqExpansion m (fun τ ↦ j τ ^ n) = (laurentqExpansion m j) ^ n`
- **What**: The width-`m` expansion of `j^n` is the `n`-th power of the expansion of `j`.
- **How**: `laurentqExpansion_finset_prod` over `Finset.range n` with constant family `j`.
- **Hypotheses**: none.
- **Uses from project**: `laurentqExpansion_finset_prod`, `j`, `j_widthM_cuspMeromorphicAt`
- **Used by**: `laurentqExpansion_polynomialIn_j_widthM`
- **Visibility**: private
- **Lines**: 152–157, proof ≈ 4 lines
- **Notes**: verbatim width-`m` copy of IntegralDescent.lean:25–29 `laurentqExpansion_j_pow_aux` (width 1).

### `theorem Cox.polynomialIn_widthM_cuspMeromorphicAt` (private)
- **Type**: `(m : ℕ+) (P : Polynomial ℂ) : MeromorphicAt (cuspFunction m (polynomialIn P j)) 0`
- **What**: `P(j)` has a meromorphic width-`m` cusp function.
- **How**: `(j_cuspData m).polynomialIn P` third component.
- **Hypotheses**: none.
- **Uses from project**: `cuspFunction`, `polynomialIn`, `j`, `j_cuspData`, `CuspData.polynomialIn`
- **Used by**: `laurentqExpansion_polynomialIn_j_widthM`
- **Visibility**: private
- **Lines**: 159–161, proof 1 line
- **Notes**: verbatim copy of IntegralDescent.lean:31–33 `polynomialIn_cuspMeromorphicAt_aux` (width 1).

### `theorem Cox.laurentqExpansion_polynomialIn_j_widthM`
- **Type**: `(m : ℕ+) (P : Polynomial ℂ) : laurentqExpansion m (polynomialIn P j) = P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion m j)`
- **What**: Taking the width-`m` Laurent expansion is a ring hom on polynomials in `j`: the expansion of `P(j)` is `P` evaluated at the expansion of `j`.
- **How**: `Polynomial.induction_on'`: the `add` case by `laurentqExpansion_add` (both summands meromorphic by `polynomialIn_widthM_cuspMeromorphicAt`); the `monomial` case by `laurentqExpansion_mul` of a constant (`meromorphicAt_cuspFunction_const`, `laurentqExpansion_const`) with `j^n` (`laurentqExpansion_j_pow_widthM`).
- **Hypotheses**: none.
- **Uses from project**: `laurentqExpansion`, `polynomialIn`, `j`, `laurentqExpansion_add`, `polynomialIn_widthM_cuspMeromorphicAt`, `j_cuspData`, `CuspData.polynomialIn`, `cuspFunction`, `laurentqExpansion_const`, `laurentqExpansion_j_pow_widthM`, `laurentqExpansion_mul`, `meromorphicAt_cuspFunction_const`
- **Used by**: `formalCoxPolynomial_eq_modularPolynomialC_map_j`
- **Visibility**: public
- **Lines**: 164–185, proof ≈ 18 lines
- **Notes**: verbatim width-`m` copy of IntegralDescent.lean:35–52 `laurentqExpansion_polynomialIn_j_aux` (same `induction_on'` skeleton, same `simpa` chains). CURRENT STATE: still duplicated (flagged in July).

### `theorem Cox.formalCoxPolynomial_eq_modularPolynomialC_map_j`
- **Type**: `(m : ℕ+) : formalCoxPolynomial m (zeta m) = Polynomial.map (Polynomial.eval₂RingHom HahnSeries.C (laurentqExpansion m j)) (modularPolynomialC m)`
- **What**: The formal Cox product `∏_σ (X − j∘σ)` over Laurent series equals `Φ_m` with `Y ↦ laurentqExpansion m j`.
- **How**: coefficientwise: `Polynomial.coeff_map`, then `coxPhiFunction_coeff_laurentqExpansion_widthM` (coefficient functions of the analytic Cox product), `modularPolynomialC_coeff_polynomialIn` (they are polynomials in `j`), and `laurentqExpansion_polynomialIn_j_widthM`.
- **Hypotheses**: none.
- **Uses from project**: `formalCoxPolynomial`, `zeta`, `modularPolynomialC`, `laurentqExpansion`, `j`, `coxPhiFunction_coeff_laurentqExpansion_widthM`, `modularPolynomialC_coeff_polynomialIn`, `laurentqExpansion_polynomialIn_j_widthM`
- **Used by**: `modularPolynomialC_diagonal_series`
- **Visibility**: public
- **Lines**: 189–199, proof ≈ 6 lines
- **Notes**: also used by Kronecker.lean:535 and LevelThree.lean.

### `theorem Cox.modularPolynomialC_diagonal_series`
- **Type**: `(m : ℕ+) : (BivariatePolynomial.diagonal (modularPolynomialC m)).eval₂ HahnSeries.C (laurentqExpansion m j) = ∏ σ : CoxMatrix m, (laurentqExpansion m j − transformedJSeries (zeta m) σ)`
- **What**: Specialising `Φ_m(X,X)` at the width-`m` series of `j` gives the product of the diagonal Cox factors.
- **How**: `BivariatePolynomial.diagonal_eval₂` + `Polynomial.eval_map` + the previous identity, then `Polynomial.eval_prod`.
- **Hypotheses**: none.
- **Uses from project**: `BivariatePolynomial.diagonal`, `BivariatePolynomial.diagonal_eval₂`, `modularPolynomialC`, `laurentqExpansion`, `j`, `transformedJSeries`, `zeta`, `CoxMatrix`, `formalCoxPolynomial_eq_modularPolynomialC_map_j`, `formalCoxPolynomial`
- **Used by**: `modularPolynomialC_diagonal_leadingCoeff_pow`
- **Visibility**: public
- **Lines**: 203–212, proof ≈ 3 lines
- **Notes**: none.

### `theorem Cox.laurentqExpansion_j_pow_order_widthM` (private)
- **Type**: `(m : ℕ+) (n : ℕ) : ((laurentqExpansion m j) ^ n).order = -((m : ℤ) * (n : ℤ))`
- **What**: `j^n` has order `-mn` at width `m`.
- **How**: instance of `laurentSeries_pow_order_of_order_neg`.
- **Hypotheses**: none.
- **Uses from project**: `laurentSeries_pow_order_of_order_neg`, `laurentqExpansion_j_order_widthM`, `laurentqExpansion`, `j`
- **Used by**: `eval₂_laurentqExpansion_j_coeff_eq_zero_of_lt_widthM`
- **Visibility**: private
- **Lines**: 214–217, proof 1 line
- **Notes**: one-line wrapper.

### `theorem Cox.eval₂_laurentqExpansion_j_coeff_widthM` (private)
- **Type**: `(m : ℕ+) (P : Polynomial ℂ) : (P.eval₂ HahnSeries.C (laurentqExpansion m j)).coeff (-((m : ℤ) * (P.natDegree : ℤ))) = P.leadingCoeff`
- **What**: The coefficient of `q^(-m·deg P)` in `P(j)` at width `m` is `leadingCoeff P`.
- **How**: instance of `polynomial_eval₂_laurentSeries_coeff` with `w = m`.
- **Hypotheses**: none.
- **Uses from project**: `polynomial_eval₂_laurentSeries_coeff`, `laurentqExpansion_j_order_widthM`, `laurentqExpansion_j_leadingCoeff_widthM`
- **Used by**: `eval₂_laurentqExpansion_j_leadingCoeff_widthM`
- **Visibility**: private
- **Lines**: 219–224, proof 2 lines
- **Notes**: CURRENT STATE: July's 36-line re-proof (then at 258–294) is gone; this now delegates to LaurentPolynomialEvaluation. Width-1 twin `eval₂_laurentqExpansion_j_coeff_neg_natDegree_aux` IntegralDescent.lean:66–70.

### `theorem Cox.eval₂_laurentqExpansion_j_coeff_eq_zero_of_lt_widthM` (private)
- **Type**: `(m : ℕ+) (P : Polynomial ℂ) (k : ℤ) (hk : k < -((m : ℤ) * (P.natDegree : ℤ))) : (P.eval₂ HahnSeries.C (laurentqExpansion m j)).coeff k = 0`
- **What**: Below `-m·deg P` all coefficients of `P(j)` vanish.
- **How**: expand `Polynomial.eval₂_eq_sum_range`, `HahnSeries.coeff_sum`, `Finset.sum_eq_zero`; each term `C (coeff n) * j^n` has order `-mn ≥ -m·deg P > k` (`laurentqExpansion_j_pow_order_widthM`, `Int.mul_le_mul_of_nonneg_left`) so `HahnSeries.coeff_eq_zero_of_lt_order`.
- **Hypotheses**: `k < -m·deg P`.
- **Uses from project**: `laurentqExpansion_j_pow_order_widthM`, `laurentqExpansion`, `j`
- **Used by**: `eval₂_laurentqExpansion_j_leadingCoeff_widthM`
- **Visibility**: private
- **Lines**: 226–242, proof ≈ 12 lines
- **Notes**: generic in `J` (only `J.order = -m` used); belongs in LaurentPolynomialEvaluation as `polynomial_eval₂_laurentSeries_coeff_eq_zero_of_lt`. Same argument as LaurentPolynomialEvaluation.lean:128–135.

### `theorem Cox.eval₂_laurentqExpansion_j_leadingCoeff_widthM` (private)
- **Type**: `(m : ℕ+) (P : Polynomial ℂ) : (P.eval₂ HahnSeries.C (laurentqExpansion m j)).leadingCoeff = P.leadingCoeff`
- **What**: Substituting the width-`m` series of `j` preserves the leading coefficient.
- **How**: for `P ≠ 0` the coefficient at `k = -m·deg P` is `leadingCoeff P ≠ 0` and everything below vanishes, so `HahnSeries.orderTop_eq_of_le` (with a `by_contra`) gives `orderTop = k`; unfold `HahnSeries.leadingCoeff`.
- **Hypotheses**: none.
- **Uses from project**: `eval₂_laurentqExpansion_j_coeff_widthM`, `eval₂_laurentqExpansion_j_coeff_eq_zero_of_lt_widthM`, `laurentqExpansion`, `j`
- **Used by**: `modularPolynomialC_diagonal_leadingCoeff_pow`
- **Visibility**: private
- **Lines**: 244–266, proof ≈ 19 lines
- **Notes**: generic in `J`; belongs in LaurentPolynomialEvaluation as `polynomial_eval₂_laurentSeries_leadingCoeff`. The `htop` block (257–262) is the `orderTop_eq_of_le`+`by_contra` idiom also at Kronecker.lean:272–276, 347–355; `HahnSeries.le_order_iff_forall` (Basic.lean:552) makes it a one-liner.

### `theorem Cox.diagonal_cox_product_leadingCoeff_pow` (private)
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) : (∏ σ : CoxMatrix m, (laurentqExpansion m j − transformedJSeries (zeta m) σ)).leadingCoeff ^ (2 * (m : ℕ)) = 1`
- **What**: The product of the diagonal factors has leading coefficient a `2m`-th root of unity.
- **How**: `Finset.prod_induction` with predicate `F.leadingCoeff ^ (2m) = 1`, closed under `*` by `HahnSeries.leadingCoeff_mul` + `mul_pow`, base `leadingCoeff_one`, factors by `cox_diagonal_factor_leadingCoeff_pow`.
- **Hypotheses**: `m` nonsquare.
- **Uses from project**: `cox_diagonal_factor_leadingCoeff_pow`, `laurentqExpansion`, `j`, `transformedJSeries`, `zeta`, `CoxMatrix`
- **Used by**: `modularPolynomialC_diagonal_leadingCoeff_pow`
- **Visibility**: private
- **Lines**: 268–280, proof ≈ 8 lines
- **Notes**: `classical` is used. A `HahnSeries.leadingCoeff_prod` (absent from mathlib) would reduce this to `Finset.prod_pow` + `Finset.prod_eq_one`.

### `theorem Cox.modularPolynomialC_diagonal_leadingCoeff_pow`
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) : (BivariatePolynomial.diagonal (modularPolynomialC m)).leadingCoeff ^ (2 * (m : ℕ)) = 1`
- **What**: Cox (11.19): for nonsquare `m` the leading coefficient of `Φ_m(X,X)` is a `2m`-th root of unity (later sharpened to `±1` in Arithmetic.lean).
- **How**: rewrite the leading coefficient as that of the specialised series (`eval₂_laurentqExpansion_j_leadingCoeff_widthM`), identify the series with the Cox product (`modularPolynomialC_diagonal_series`), and apply `diagonal_cox_product_leadingCoeff_pow`.
- **Hypotheses**: `m` nonsquare.
- **Uses from project**: `eval₂_laurentqExpansion_j_leadingCoeff_widthM`, `modularPolynomialC_diagonal_series`, `diagonal_cox_product_leadingCoeff_pow`, `BivariatePolynomial.diagonal`, `modularPolynomialC`
- **Used by**: unused in file (Arithmetic.lean)
- **Visibility**: public
- **Lines**: 284–291, proof ≈ 4 lines
- **Notes**: none.

## File Summary
- Total declarations: 19 (0 defs, 19 theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `laurentqExpansion_j_order_widthM` (4), `laurentqExpansion_j_leadingCoeff_widthM` (2 + cross-file)
- Unused declarations (not used by anything in this file): `modularPolynomialC_diagonal_leadingCoeff_pow` (used by Arithmetic.lean)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `cox_diagonal_factor_leadingCoeff` (≈ 41)

## Observations

### Mathlib API candidates
- Order/leadingCoeff bookkeeping (65–77, 105–112, 257–266) rides on `HahnSeries.order_le_of_coeff_ne_zero` (Basic.lean:383), `coeff_order_eq_zero` (:374), `orderTop_eq_of_le` (:275), `order_eq_orderTop_of_ne_zero` (:370), `leadingCoeff_sub` (Addition.lean:418), `leadingCoeff_neg` (:399) — all verified. Not yet used but available: `HahnSeries.le_order_iff_forall (h : x ≠ 0) : i ≤ x.order ↔ ∀ j < i, x.coeff j = 0` (Basic.lean:552) which replaces the `orderTop_eq_of_le` + `by_contra` idiom at 257–262 by `le_antisymm (order_le_of_coeff_ne_zero hcoeff0) ((le_order_iff_forall hne).2 …)`.
- `cox_diagonal_factor_leadingCoeff_pow` (145–149): `(zeta_isPrimitiveRoot m).zpow_eq_one` is `IsPrimitiveRoot.zpow_eq_one` (RootsOfUnity/PrimitiveRoots.lean:338) — correct use.
- `diagonal_cox_product_leadingCoeff_pow` (268–280): no `HahnSeries.leadingCoeff_prod` in mathlib (grep `leadingCoeff_prod` in `Mathlib/RingTheory/HahnSeries/`: none); PR candidate alongside `leadingCoeff_pow`.
- `laurentqExpansion_polynomialIn_j_widthM` (164–185): no mathlib analogue (the project's `laurentqExpansion` is project-defined); the shape is "`laurentqExpansion h` is a ring hom on the subring of functions with meromorphic cusp function", which the project only has piecemeal (`laurentqExpansion_add/mul/const/finset_prod`).

### Missing API / repeated patterns
- **Width-1 / width-m duplication with IntegralDescent.lean** (CURRENT, unchanged since July): `laurentqExpansion_j_pow_widthM` (152–157) = IntegralDescent `laurentqExpansion_j_pow_aux` (25–29); `polynomialIn_widthM_cuspMeromorphicAt` (159–161) = `polynomialIn_cuspMeromorphicAt_aux` (31–33); `laurentqExpansion_polynomialIn_j_widthM` (164–185) = `laurentqExpansion_polynomialIn_j_aux` (35–52); `laurentqExpansion_j_order_widthM`/`_leadingCoeff_widthM` (33–54) ≈ `laurentqExpansion_j_order_aux`/`_leadingCoeff_aux` (54–64); `eval₂_laurentqExpansion_j_coeff_widthM` (219–224) = `eval₂_laurentqExpansion_j_coeff_neg_natDegree_aux` (66–70). Fix: keep only the width-`m` versions (IntegralDescent takes `m = 1` via `PNat.one_coe`/`Nat.cast_one`), or better add a general `laurentqExpansion_polynomialIn {N} (hf : CuspData N f) (h : ℝ) (hh : 0 < h) (P) : laurentqExpansion h (polynomialIn P f) = P.eval₂ C (laurentqExpansion h f)` to LaurentQExpansion/Algebra.lean (the proof uses only `laurentqExpansion_add/mul/const/finset_prod` and meromorphy of powers).
- **Generic lowest-coefficient siblings** (226–266) proved at `K = ℂ`: `polynomial_eval₂_laurentSeries_coeff_eq_zero_of_lt`, `polynomial_eval₂_laurentSeries_order`, `polynomial_eval₂_laurentSeries_leadingCoeff` should live in LaurentPolynomialEvaluation.lean next to `polynomial_eval₂_laurentSeries_coeff`; then 214–266 collapse to three one-line instantiations. CURRENT STATE vs July: the coefficient lemma itself was fixed (219–224 now delegates), the two siblings were not.
- **`order` vs `orderTop` friction** (98–112): `HahnSeries.leadingCoeff_sub` is stated with `orderTop`; a project (or mathlib) lemma `leadingCoeff_sub_of_order_lt (hx : x ≠ 0) (hy : y ≠ 0) (h : x.order < y.order) : (x - y).leadingCoeff = x.leadingCoeff` (from `order_eq_orderTop_of_ne_zero` + `leadingCoeff_sub`) would cut ~15 lines from `cox_diagonal_factor_leadingCoeff` and applies again in Arithmetic.lean-style arguments.
- `laurentqExpansion_j_order_three`/`_leadingCoeff_three` (LevelThree.lean:715–725) are `norm_num` cast-shims of the two public lemmas here; a statement with `(m : ℕ) : ℝ` replaced by a real `h` with `h = m` hypothesis, or `@[simp]` lemmas for `((3 : ℕ+) : ℕ) : ℝ) = 3`, would remove them.

### Junk candidates
- Lines 1–10: the copyright header is duplicated verbatim (two identical 5-line blocks).
- `laurentqExpansion_j_pow_order_widthM` (214–217): one-line wrapper used once (238); inline.
- `transformedJSeries_coeff_order` (56–62) is fine as a private helper (used twice).

### Moral duplicates within this batch
- `transformedJSeries_order` (65–77), Kronecker `jUnitLaurentSeriesMod_order` (263–280), Kronecker `jLaurentSeriesMod_order` (339–359), and the `htop` block of `eval₂_laurentqExpansion_j_leadingCoeff_widthM` (257–262) all prove "order = g from coeff g ≠ 0 and vanishing below g" by hand with two different routes (`coeff_order_eq_zero` vs `orderTop_eq_of_le`+`by_contra`+`order_eq_orderTop_of_ne_zero`+`exact_mod_cast`). One helper `HahnSeries.order_eq_of_coeff_ne_zero_of_forall_lt` (composable from mathlib's `order_le_of_coeff_ne_zero`, `le_order_iff_forall`, `ne_zero_of_coeff_ne_zero`) serves all four.
- `laurentqExpansion_j_pow_widthM` ↔ `laurentqExpansion_finset_prod` with constant family: the project lacks a `laurentqExpansion_pow` lemma; both this file and IntegralDescent derive it ad hoc.

### Generalization notes
- `transformedJSeries_order`/`_leadingCoeff` (65–85): stated for `Field K`; the proof uses only `zpow_ne_zero` (any `GroupWithZero`/`DivisionRing`) and Hahn-series order lemmas; `Field` is forced by the definition of `transformedJSeries`.
- `eval₂_laurentqExpansion_j_coeff_eq_zero_of_lt_widthM` and `_leadingCoeff_widthM` (226–266): nothing about ℂ, `j` or `m` is used beyond `order = -m`, `leadingCoeff = 1`; generalise to `{K} [CommRing K] [IsDomain K] (J : LaurentSeries K) (w : ℕ) (hw : 0 < w) (horder) (hleading)` exactly as `polynomial_eval₂_laurentSeries_coeff`.
- `cox_diagonal_factor_leadingCoeff` needs `¬ IsSquare m` only to exclude `σ.a ^ 2 = m`; the statement could instead take `(hne : σ.a ^ 2 ≠ m)` per `σ`, making the square case usable factor-by-factor.
