# Inventory: XYin/PhD/Cox/SymmetricCubicLaurent.lean  (391 lines)

Finite Laurent detection for symmetric bivariate polynomials of bidegree ≤ 3: if `T`, `J` are Laurent series of orders `-9`, `-3` with leading coefficient one, then a symmetric `P ∈ K[X][Y]` of bidegree ≤ 3 is zero as soon as the ten "triangular" coefficients of `P(T, J)` at exponents `0, -9, -12, …, -36` vanish. Everything except the final theorem is private; the only consumer is LevelThree.lean (`modularPolynomialThreeDifference_eq_zero`, line 824), used to certify the explicit `Φ_3`.

## Declarations

### `theorem Cox.coeff_comm_of_swap_eq` (private)
- **Type**: `{K} [CommRing K] (P : BivariatePolynomial K) (hsymm : Polynomial.Bivariate.swap P = P) (i j : ℕ) : (P.coeff i).coeff j = (P.coeff j).coeff i`
- **What**: A swap-symmetric bivariate polynomial has symmetric coefficient matrix.
- **How**: apply `(·.coeff i).coeff j` to `hsymm` and rewrite with the project's `BivariatePolynomial.coeff_coeff_swap`.
- **Hypotheses**: `P` is symmetric.
- **Uses from project**: `BivariatePolynomial`, `BivariatePolynomial.coeff_coeff_swap`
- **Used by**: `symmetricCubicExpansion_coeff_aux`
- **Visibility**: private
- **Lines**: 21–27, proof ≈ 4 lines
- **Notes**: same trick inlined at LevelThree.lean:785; belongs next to `coeff_coeff_swap` in ModularPolynomial/Construction.lean.

### `def Cox.symmetricCubicExpansion` (private)
- **Type**: `{K} [CommRing K] (P : BivariatePolynomial K) : BivariatePolynomial K`
- **What**: The explicit ten-term rewrite of a symmetric cubic: for `j ≤ i ≤ 3` the monomials `c_{ij}(X^i Y^j + X^j Y^i)` (once when `i = j`) with `c_{ij}` read off from `P`.
- **How**: a literal sum of `Polynomial.monomial i (Polynomial.monomial j …)` terms (10 unordered pairs, 16 monomials).
- **Hypotheses**: none.
- **Uses from project**: `BivariatePolynomial`
- **Used by**: `symmetricCubicExpansion_coeff_aux`, `eq_symmetricCubicExpansion`, `symmetricCubicExpansion_eq_fin`
- **Visibility**: private
- **Lines**: 29–42
- **Notes**: hard-codes bidegree 3; re-expressed as a `Fin 10` sum by `symmetricCubicPolynomialExpansionFin` (249–251), making this def a stepping stone only.

### `theorem Cox.symmetricCubicExpansion_coeff_aux` (private)
- **Type**: `(P) (i : ℕ) (hi : i ≤ 3) (hinner : (P.coeff i).natDegree ≤ 3) (hsymm : swap P = P) : (symmetricCubicExpansion P).coeff i = P.coeff i`
- **What**: For `i ≤ 3` the `i`-th coefficient polynomial of the expansion agrees with that of `P`.
- **How**: `Polynomial.ext`; for `j ≤ 3` `interval_cases i <;> interval_cases j <;> simp [Polynomial.coeff_monomial, coeff_comm_of_swap_eq]`; for `j > 3` both sides vanish (`Polynomial.coeff_eq_zero_of_natDegree_lt` on the right, `simp` with `j ≠ 0,1,2,3` on the left).
- **Hypotheses**: `i ≤ 3`, inner degree ≤ 3, symmetry.
- **Uses from project**: `symmetricCubicExpansion`, `coeff_comm_of_swap_eq`
- **Used by**: `symmetricCubicExpansion_coeff_zero/_one/_two/_three`
- **Visibility**: private
- **Lines**: 44–62, proof ≈ 14 lines
- **Notes**: new since July (the July report asked for exactly this uniform lemma).

### `theorem Cox.symmetricCubicExpansion_coeff_zero` (private)
- **Type**: `(P) (hinner : (P.coeff 0).natDegree ≤ 3) (hsymm) : (symmetricCubicExpansion P).coeff 0 = P.coeff 0`
- **What**: Instance `i = 0` of the previous lemma.
- **How**: `symmetricCubicExpansion_coeff_aux P 0 (by decide)`.
- **Hypotheses**: as above.
- **Uses from project**: `symmetricCubicExpansion_coeff_aux`, `symmetricCubicExpansion`
- **Used by**: `eq_symmetricCubicExpansion`
- **Visibility**: private
- **Lines**: 64–68, proof 1 line
- **Notes**: vestigial one-line wrapper.

### `theorem Cox.symmetricCubicExpansion_coeff_one` (private)
- **Type**: as `_coeff_zero` with `1`.
- **What**: Instance `i = 1`.
- **How**: `symmetricCubicExpansion_coeff_aux P 1 (by decide)`.
- **Hypotheses**: as above.
- **Uses from project**: `symmetricCubicExpansion_coeff_aux`, `symmetricCubicExpansion`
- **Used by**: `eq_symmetricCubicExpansion`
- **Visibility**: private
- **Lines**: 70–74, proof 1 line
- **Notes**: vestigial.

### `theorem Cox.symmetricCubicExpansion_coeff_two` (private)
- **Type**: as `_coeff_zero` with `2`.
- **What**: Instance `i = 2`.
- **How**: `symmetricCubicExpansion_coeff_aux P 2 (by decide)`.
- **Hypotheses**: as above.
- **Uses from project**: `symmetricCubicExpansion_coeff_aux`, `symmetricCubicExpansion`
- **Used by**: `eq_symmetricCubicExpansion`
- **Visibility**: private
- **Lines**: 76–80, proof 1 line
- **Notes**: vestigial.

### `theorem Cox.symmetricCubicExpansion_coeff_three` (private)
- **Type**: as `_coeff_zero` with `3`.
- **What**: Instance `i = 3`.
- **How**: `symmetricCubicExpansion_coeff_aux P 3 (by decide)`.
- **Hypotheses**: as above.
- **Uses from project**: `symmetricCubicExpansion_coeff_aux`, `symmetricCubicExpansion`
- **Used by**: `eq_symmetricCubicExpansion`
- **Visibility**: private
- **Lines**: 82–86, proof 1 line
- **Notes**: vestigial.

### `theorem Cox.eq_symmetricCubicExpansion` (private)
- **Type**: `(P) (houter : P.natDegree ≤ 3) (hinner : ∀ i, (P.coeff i).natDegree ≤ 3) (hsymm) : P = symmetricCubicExpansion P`
- **What**: A symmetric polynomial of bidegree ≤ 3 equals its ten-term expansion.
- **How**: `Polynomial.ext`; `i ≤ 3` by `interval_cases` and the four wrappers; `i > 3` both sides vanish (`Polynomial.coeff_eq_zero_of_natDegree_lt`, `simp` with `i ≠ 0,1,2,3` via `lia`).
- **Hypotheses**: bidegree ≤ 3, symmetry.
- **Uses from project**: `symmetricCubicExpansion`, `symmetricCubicExpansion_coeff_zero/_one/_two/_three`
- **Used by**: `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`, `eq_zero_of_cubicCoeff_eq_zero`
- **Visibility**: private
- **Lines**: 88–109, proof ≈ 17 lines
- **Notes**: the `i > 3` branch (101–109) repeats the `j > 3` branch of `_coeff_aux` (55–62) one level up.

### `def Cox.bivariateLaurentEvalHom` (private)
- **Type**: `{K} [Field K] (T J : LaurentSeries K) : BivariatePolynomial K →+* LaurentSeries K`
- **What**: Evaluate a bivariate polynomial at `(outer ↦ T, inner ↦ J)` in Laurent series.
- **How**: `Polynomial.eval₂RingHom (Polynomial.eval₂RingHom HahnSeries.C J) T`.
- **Hypotheses**: none.
- **Uses from project**: `BivariatePolynomial`
- **Used by**: `bivariateLaurentEval`, `bivariateLaurentEval_add`, `bivariateLaurentEval_monomial`, `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff` (unfolded by `norm_num`)
- **Visibility**: private
- **Lines**: 111–114
- **Notes**: CURRENT STATE: still `eval₂RingHom (eval₂RingHom C J) T`, not `evalEval`-based (unchanged since July). Mathlib: `Polynomial.eval₂RingHom_eval₂RingHom` (Algebra/Polynomial/Bivariate.lean:189) rewrites it as `(evalEvalRingHom J T).comp (mapRingHom (mapRingHom HahnSeries.C))`, and with `HahnSeries.C_eq_algebraMap` (Multiplication.lean:928) it is `Polynomial.aevalAeval J T` (Bivariate.lean:231; `coe_aevalAeval_eq_evalEval` :237). Same hom is rebuilt inline at LevelThree.lean:643–649 and 656–659.

### `def Cox.bivariateLaurentEval` (private)
- **Type**: `(T J : LaurentSeries K) (P : BivariatePolynomial K) : LaurentSeries K`
- **What**: The underlying function of `bivariateLaurentEvalHom`.
- **How**: `bivariateLaurentEvalHom T J P`.
- **Hypotheses**: none.
- **Uses from project**: `bivariateLaurentEvalHom`
- **Used by**: `bivariateLaurentEval_add`, `bivariateLaurentEval_monomial`, `bivariateLaurentEval_symmetricBivariateMonomial`, `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`, `cubicCoeff_eq_zero_of_laurent_coeff`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff`
- **Visibility**: private
- **Lines**: 116–118
- **Notes**: pure coercion wrapper (`⇑(bivariateLaurentEvalHom T J)`); junk candidate.

### `theorem Cox.bivariateLaurentEval_add` (private)
- **Type**: `(T J) (P Q) : bivariateLaurentEval T J (P + Q) = bivariateLaurentEval T J P + bivariateLaurentEval T J Q`
- **What**: Additivity of evaluation.
- **How**: `map_add` of the ring hom.
- **Hypotheses**: none.
- **Uses from project**: `bivariateLaurentEval`, `bivariateLaurentEvalHom`
- **Used by**: `bivariateLaurentEval_symmetricBivariateMonomial`
- **Visibility**: private
- **Lines**: 121–125, proof 1 line
- **Notes**: `@[simp]`; would be `map_add` for free if the hom were used directly.

### `theorem Cox.bivariateLaurentEval_monomial` (private)
- **Type**: `(T J) (i j : ℕ) (a : K) : bivariateLaurentEval T J (monomial i (monomial j a)) = HahnSeries.C a * T ^ i * J ^ j`
- **What**: Evaluation of a monomial `a X^i Y^j`.
- **How**: `Polynomial.eval₂_monomial` twice then `ring`.
- **Hypotheses**: none.
- **Uses from project**: `bivariateLaurentEval`, `bivariateLaurentEvalHom`
- **Used by**: `bivariateLaurentEval_symmetricBivariateMonomial`
- **Visibility**: private
- **Lines**: 128–134, proof ≈ 3 lines
- **Notes**: `@[simp]`.

### `def Cox.symmetricBivariateMonomial` (private)
- **Type**: `{K} [Field K] (i j : ℕ) (a : K) : BivariatePolynomial K`
- **What**: The symmetrised monomial `a(X^i Y^j + X^j Y^i)`, or `a X^i Y^i` when `i = j`.
- **How**: `if i = j then … else … + …`.
- **Hypotheses**: none.
- **Uses from project**: `BivariatePolynomial`
- **Used by**: `bivariateLaurentEval_symmetricBivariateMonomial`, `symmetricCubicPolynomialExpansionFin`, `symmetricCubicExpansion_eq_fin`, `eq_zero_of_cubicCoeff_eq_zero`
- **Visibility**: private
- **Lines**: 136–140
- **Notes**: `Field K` unnecessary (`Semiring`).

### `def Cox.cubicWeight` (private)
- **Type**: `(i j : ℕ) : ℤ`
- **What**: The pole order `9i + 3j` of `T^i J^j`.
- **How**: `9 * i + 3 * j`.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: `laurentMonomial_order`, `laurentMonomial_coeff_self`, `laurentMonomial_coeff_zero_of_weight_lt`, `symmetricLaurentMonomial_coeff_self`, `symmetricLaurentMonomial_coeff_zero_of_weight_lt`, `cubicWeight_strictMono`, `cubicBasis_coeff_self`, `cubicBasis_coeff_zero_of_lt`, `symmetricCubicLaurentExpansionFin_coeff_eq`, `cubicCoeff_eq_zero_of_laurent_coeff`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff`
- **Visibility**: private
- **Lines**: 142
- **Notes**: hard-codes the orders `-9`, `-3`.

### `theorem Cox.laurentMonomial_order` (private)
- **Type**: `(T J) (hT : T.order = -9) (hJ : J.order = -3) (i j : ℕ) : (T ^ i * J ^ j).order = -(cubicWeight i j)`
- **What**: `T^i J^j` has order `-(9i + 3j)`.
- **How**: `T, J ≠ 0` from their orders (`subst; simp`), then `HahnSeries.order_mul` (Multiplication.lean:1022) and `HahnSeries.order_pow` (:1034); `simp [cubicWeight]; ring`.
- **Hypotheses**: orders `-9`, `-3`.
- **Uses from project**: `cubicWeight`
- **Used by**: `laurentMonomial_coeff_self`, `laurentMonomial_coeff_zero_of_weight_lt`
- **Visibility**: private
- **Lines**: 144–158, proof ≈ 12 lines
- **Notes**: needs only `[Semiring K] [NoZeroDivisors K]`.

### `theorem Cox.laurentMonomial_leadingCoeff` (private)
- **Type**: `(T J) (hT : T.leadingCoeff = 1) (hJ : J.leadingCoeff = 1) (i j) : (T ^ i * J ^ j).leadingCoeff = 1`
- **What**: Monomials in monic series are monic.
- **How**: `HahnSeries.leadingCoeff_mul` + `laurentSeries_pow_leadingCoeff_of_eq_one` twice.
- **Hypotheses**: leading coefficients one.
- **Uses from project**: `laurentSeries_pow_leadingCoeff_of_eq_one`
- **Used by**: `laurentMonomial_coeff_self`
- **Visibility**: private
- **Lines**: 160–165, proof ≈ 3 lines
- **Notes**: none.

### `theorem Cox.laurentMonomial_coeff_self` (private)
- **Type**: `(T J) (hTorder) (hJorder) (hTlead) (hJlead) (i j) : (T ^ i * J ^ j).coeff (-(cubicWeight i j)) = 1`
- **What**: The coefficient of `T^i J^j` at its own pole order is one.
- **How**: rewrite the exponent as the order (`laurentMonomial_order`), `HahnSeries.leadingCoeff_eq`, `laurentMonomial_leadingCoeff`.
- **Hypotheses**: orders and leading coefficients as above.
- **Uses from project**: `laurentMonomial_order`, `laurentMonomial_leadingCoeff`, `cubicWeight`
- **Used by**: `symmetricLaurentMonomial_coeff_self`
- **Visibility**: private
- **Lines**: 167–174, proof ≈ 3 lines
- **Notes**: none.

### `theorem Cox.laurentMonomial_coeff_zero_of_weight_lt` (private)
- **Type**: `(T J) (hT) (hJ) (i j r s : ℕ) (hweight : cubicWeight i j < cubicWeight r s) : (T ^ i * J ^ j).coeff (-(cubicWeight r s)) = 0`
- **What**: A monomial of smaller weight has no coefficient at a deeper pole exponent.
- **How**: `HahnSeries.coeff_eq_zero_of_lt_order` with `laurentMonomial_order`.
- **Hypotheses**: weight comparison.
- **Uses from project**: `laurentMonomial_order`, `cubicWeight`
- **Used by**: `symmetricLaurentMonomial_coeff_self`, `symmetricLaurentMonomial_coeff_zero_of_weight_lt`
- **Visibility**: private
- **Lines**: 176–182, proof ≈ 3 lines
- **Notes**: none.

### `def Cox.symmetricLaurentMonomial` (private)
- **Type**: `(T J : LaurentSeries K) (i j : ℕ) : LaurentSeries K`
- **What**: `T^i J^j + T^j J^i` (or `T^i J^i` when `i = j`): the Laurent image of `symmetricBivariateMonomial`.
- **How**: `if i = j then … else … + …`.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: `bivariateLaurentEval_symmetricBivariateMonomial`, `symmetricLaurentMonomial_coeff_self`, `symmetricLaurentMonomial_coeff_zero_of_weight_lt`, `cubicBasis`
- **Visibility**: private
- **Lines**: 184–186
- **Notes**: none.

### `theorem Cox.bivariateLaurentEval_symmetricBivariateMonomial` (private)
- **Type**: `(T J) (i j) (a : K) : bivariateLaurentEval T J (symmetricBivariateMonomial i j a) = HahnSeries.C a * symmetricLaurentMonomial T J i j`
- **What**: Evaluation sends the symmetrised monomial to `a` times the symmetrised Laurent monomial.
- **How**: case `i = j`: `subst`, `simp` with `bivariateLaurentEval_monomial`, `HahnSeries.C_mul_eq_smul`, `ring`; otherwise `bivariateLaurentEval_add` + `_monomial` + `ring`.
- **Hypotheses**: none.
- **Uses from project**: `bivariateLaurentEval`, `symmetricBivariateMonomial`, `symmetricLaurentMonomial`, `bivariateLaurentEval_monomial`, `bivariateLaurentEval_add`
- **Used by**: `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`
- **Visibility**: private
- **Lines**: 188–200, proof ≈ 9 lines
- **Notes**: none.

### `theorem Cox.symmetricLaurentMonomial_coeff_self` (private)
- **Type**: `(T J) (hTorder) (hJorder) (hTlead) (hJlead) (i j) (hji : j ≤ i) : (symmetricLaurentMonomial T J i j).coeff (-(cubicWeight i j)) = 1`
- **What**: At its dominant exponent `-(9i+3j)` (with `j ≤ i`) the symmetrised monomial has coefficient one: the `T^i J^j` term contributes one and the mirror term `T^j J^i` has strictly smaller weight.
- **How**: `laurentMonomial_coeff_self` for the leading term, `laurentMonomial_coeff_zero_of_weight_lt` for the mirror (weight inequality by `lia` on `cubicWeight`).
- **Hypotheses**: `j ≤ i`, orders, leading coefficients.
- **Uses from project**: `symmetricLaurentMonomial`, `laurentMonomial_coeff_self`, `laurentMonomial_coeff_zero_of_weight_lt`, `cubicWeight`
- **Used by**: `cubicBasis_coeff_self`
- **Visibility**: private
- **Lines**: 202–216, proof ≈ 10 lines
- **Notes**: the mirror-term inequality `9j+3i < 9i+3j` for `j < i` is where the weights `(9,3)` matter.

### `theorem Cox.symmetricLaurentMonomial_coeff_zero_of_weight_lt` (private)
- **Type**: `(T J) (hT) (hJ) (i j r s) (hji : j ≤ i) (hweight : cubicWeight i j < cubicWeight r s) : (symmetricLaurentMonomial T J i j).coeff (-(cubicWeight r s)) = 0`
- **What**: A symmetrised monomial of smaller dominant weight vanishes at a deeper exponent.
- **How**: `split_ifs`; both terms by `laurentMonomial_coeff_zero_of_weight_lt` (mirror term's weight ≤ dominant weight, `lia`).
- **Hypotheses**: `j ≤ i`, weight comparison.
- **Uses from project**: `symmetricLaurentMonomial`, `laurentMonomial_coeff_zero_of_weight_lt`, `cubicWeight`
- **Used by**: `cubicBasis_coeff_zero_of_lt`
- **Visibility**: private
- **Lines**: 218–231, proof ≈ 9 lines
- **Notes**: none.

### `def Cox.cubicI` (private)
- **Type**: `Fin 10 → ℕ`
- **What**: Outer exponents of the ten triangular pairs `(i,j)`, `j ≤ i ≤ 3`, in weight order.
- **How**: `![0, 1, 1, 2, 2, 2, 3, 3, 3, 3]`.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: `cubicCoeff`, `cubicBasis`, `symmetricCubicPolynomialExpansionFin`, `symmetricCubicExpansion_eq_fin`, `cubicJ_le_cubicI`, `cubicWeight_strictMono`, `cubicBasis_coeff_self`, `cubicBasis_coeff_zero_of_lt`, `symmetricCubicLaurentExpansionFin_coeff_eq`, `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`, `cubicCoeff_eq_zero_of_laurent_coeff`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff`
- **Visibility**: private
- **Lines**: 233
- **Notes**: literal enumeration; blocks generalisation in `n`.

### `def Cox.cubicJ` (private)
- **Type**: `Fin 10 → ℕ`
- **What**: Inner exponents of the ten pairs.
- **How**: `![0, 0, 1, 0, 1, 2, 0, 1, 2, 3]`.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: same set as `cubicI`
- **Visibility**: private
- **Lines**: 235
- **Notes**: as `cubicI`.

### `def Cox.cubicCoeff` (private)
- **Type**: `(P : BivariatePolynomial K) (k : Fin 10) : K`
- **What**: The `k`-th triangular coefficient `(P.coeff (cubicI k)).coeff (cubicJ k)`.
- **How**: direct.
- **Hypotheses**: none.
- **Uses from project**: `cubicI`, `cubicJ`, `BivariatePolynomial`
- **Used by**: `symmetricCubicLaurentExpansionFin`, `symmetricCubicPolynomialExpansionFin`, `symmetricCubicExpansion_eq_fin`, `symmetricCubicLaurentExpansionFin_coeff_eq`, `bivariateLaurentEval_eq_…Fin`, `cubicCoeff_eq_zero_of_laurent_coeff`, `eq_zero_of_cubicCoeff_eq_zero`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`
- **Visibility**: private
- **Lines**: 237–239
- **Notes**: none.

### `def Cox.cubicBasis` (private)
- **Type**: `(T J : LaurentSeries K) (k : Fin 10) : LaurentSeries K`
- **What**: The `k`-th symmetrised Laurent monomial `symmetricLaurentMonomial T J (cubicI k) (cubicJ k)`.
- **How**: direct.
- **Hypotheses**: none.
- **Uses from project**: `symmetricLaurentMonomial`, `cubicI`, `cubicJ`
- **Used by**: `symmetricCubicLaurentExpansionFin`, `cubicBasis_coeff_self`, `cubicBasis_coeff_zero_of_lt`, `symmetricCubicLaurentExpansionFin_coeff_eq`
- **Visibility**: private
- **Lines**: 241–243
- **Notes**: none.

### `def Cox.symmetricCubicLaurentExpansionFin` (private)
- **Type**: `(T J) (P : BivariatePolynomial K) : LaurentSeries K`
- **What**: `∑_{k : Fin 10} C (cubicCoeff P k) * cubicBasis T J k`, the expected Laurent value of a symmetric cubic.
- **How**: `Finset.sum` over `Fin 10`.
- **Hypotheses**: none.
- **Uses from project**: `cubicCoeff`, `cubicBasis`
- **Used by**: `symmetricCubicLaurentExpansionFin_coeff_eq`, `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`
- **Visibility**: private
- **Lines**: 245–247
- **Notes**: none.

### `def Cox.symmetricCubicPolynomialExpansionFin` (private)
- **Type**: `(P : BivariatePolynomial K) : BivariatePolynomial K`
- **What**: `∑_{k} symmetricBivariateMonomial (cubicI k) (cubicJ k) (cubicCoeff P k)`, the `Fin 10`-indexed form of `symmetricCubicExpansion`.
- **How**: `Finset.sum` over `Fin 10`.
- **Hypotheses**: none.
- **Uses from project**: `symmetricBivariateMonomial`, `cubicI`, `cubicJ`, `cubicCoeff`
- **Used by**: `symmetricCubicExpansion_eq_fin`, `bivariateLaurentEval_eq_…Fin`, `eq_zero_of_cubicCoeff_eq_zero`
- **Visibility**: private
- **Lines**: 249–251
- **Notes**: makes `symmetricCubicExpansion` (29–42) redundant except as an unfolding target.

### `theorem Cox.symmetricCubicExpansion_eq_fin` (private)
- **Type**: `(P) : symmetricCubicExpansion P = symmetricCubicPolynomialExpansionFin P`
- **What**: The literal 10-term expansion equals the indexed sum.
- **How**: `simp [Fin.sum_univ_succ, …]; abel`.
- **Hypotheses**: none.
- **Uses from project**: `symmetricCubicExpansion`, `symmetricCubicPolynomialExpansionFin`, `symmetricBivariateMonomial`, `cubicCoeff`, `cubicI`, `cubicJ`
- **Used by**: `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`, `eq_zero_of_cubicCoeff_eq_zero`
- **Visibility**: private
- **Lines**: 253–258, proof ≈ 3 lines
- **Notes**: exists only to bridge the two encodings.

### `theorem Cox.cubicJ_le_cubicI` (private)
- **Type**: `(k : Fin 10) : cubicJ k ≤ cubicI k`
- **What**: Every enumerated pair is triangular.
- **How**: `fin_cases k <;> norm_num`.
- **Hypotheses**: none.
- **Uses from project**: `cubicI`, `cubicJ`
- **Used by**: `cubicBasis_coeff_self`, `cubicBasis_coeff_zero_of_lt`
- **Visibility**: private
- **Lines**: 260–261, proof 1 line
- **Notes**: none.

### `theorem Cox.cubicWeight_strictMono` (private)
- **Type**: `StrictMono (fun k : Fin 10 ↦ cubicWeight (cubicI k) (cubicJ k))`
- **What**: The weights `0, 9, 12, 18, 21, 24, 27, 30, 33, 36` are strictly increasing along the enumeration.
- **How**: `Fin.strictMono_iff_lt_succ` (Order/Fin/Basic.lean:149) then `fin_cases`.
- **Hypotheses**: none.
- **Uses from project**: `cubicWeight`, `cubicI`, `cubicJ`
- **Used by**: `cubicBasis_coeff_zero_of_lt`
- **Visibility**: private
- **Lines**: 263–267, proof ≈ 3 lines
- **Notes**: this is the only place the choice `(9,3)` with `j ≤ i ≤ 3` is verified to give distinct orders.

### `theorem Cox.cubicBasis_coeff_self` (private)
- **Type**: `(T J) (hTorder) (hJorder) (hTlead) (hJlead) (k) : (cubicBasis T J k).coeff (-(cubicWeight (cubicI k) (cubicJ k))) = 1`
- **What**: Diagonal entries of the triangular system are one.
- **How**: `symmetricLaurentMonomial_coeff_self` with `cubicJ_le_cubicI`.
- **Hypotheses**: orders/leading coefficients.
- **Uses from project**: `cubicBasis`, `symmetricLaurentMonomial_coeff_self`, `cubicI`, `cubicJ`, `cubicWeight`, `cubicJ_le_cubicI`
- **Used by**: `symmetricCubicLaurentExpansionFin_coeff_eq`
- **Visibility**: private
- **Lines**: 269–275, proof 2 lines
- **Notes**: none.

### `theorem Cox.cubicBasis_coeff_zero_of_lt` (private)
- **Type**: `(T J) (hT) (hJ) {k l : Fin 10} (hkl : k < l) : (cubicBasis T J k).coeff (-(cubicWeight (cubicI l) (cubicJ l))) = 0`
- **What**: Strictly-below-diagonal entries vanish (the system is triangular).
- **How**: `symmetricLaurentMonomial_coeff_zero_of_weight_lt` with `cubicWeight_strictMono hkl`.
- **Hypotheses**: `k < l`, orders.
- **Uses from project**: `cubicBasis`, `symmetricLaurentMonomial_coeff_zero_of_weight_lt`, `cubicJ_le_cubicI`, `cubicWeight_strictMono`, `cubicI`, `cubicJ`, `cubicWeight`
- **Used by**: `symmetricCubicLaurentExpansionFin_coeff_eq`
- **Visibility**: private
- **Lines**: 277–283, proof 3 lines
- **Notes**: none.

### `theorem Cox.symmetricCubicLaurentExpansionFin_coeff_eq` (private)
- **Type**: `(T J) (P) (hTorder) (hJorder) (hTlead) (hJlead) (k : Fin 10) (hzero : ∀ l, k < l → cubicCoeff P l = 0) : (symmetricCubicLaurentExpansionFin T J P).coeff (-(cubicWeight (cubicI k) (cubicJ k))) = cubicCoeff P k`
- **What**: Back-substitution step: once all higher triangular coefficients vanish, the Laurent coefficient at the `k`-th exponent equals the `k`-th coefficient of `P`.
- **How**: `HahnSeries.coeff_sum` + `Fintype.sum_eq_single k`: the `k` term by `cubicBasis_coeff_self`, `l < k` terms by `cubicBasis_coeff_zero_of_lt`, `l > k` terms by `hzero`.
- **Hypotheses**: as stated.
- **Uses from project**: `symmetricCubicLaurentExpansionFin`, `cubicBasis_coeff_self`, `cubicBasis_coeff_zero_of_lt`, `cubicCoeff`, `cubicWeight`, `cubicI`, `cubicJ`
- **Used by**: `cubicCoeff_eq_zero_of_laurent_coeff`
- **Visibility**: private
- **Lines**: 285–304, proof ≈ 12 lines
- **Notes**: `classical`. Generic in the index type given a strictly monotone weight.

### `theorem Cox.bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin` (private)
- **Type**: `(T J) (P) (houter) (hinner) (hsymm) : bivariateLaurentEval T J P = symmetricCubicLaurentExpansionFin T J P`
- **What**: For a symmetric cubic, evaluation equals the indexed Laurent expansion.
- **How**: rewrite `P` by `eq_symmetricCubicExpansion` + `symmetricCubicExpansion_eq_fin`, push the ring hom through the sum (`map_sum`), and use `bivariateLaurentEval_symmetricBivariateMonomial` termwise.
- **Hypotheses**: bidegree ≤ 3, symmetry.
- **Uses from project**: `bivariateLaurentEval`, `symmetricCubicLaurentExpansionFin`, `eq_symmetricCubicExpansion`, `symmetricCubicExpansion_eq_fin`, `symmetricCubicPolynomialExpansionFin`, `bivariateLaurentEvalHom`, `symmetricBivariateMonomial`, `cubicI`, `cubicJ`, `cubicCoeff`, `bivariateLaurentEval_symmetricBivariateMonomial`
- **Used by**: `cubicCoeff_eq_zero_of_laurent_coeff`
- **Visibility**: private
- **Lines**: 306–321, proof ≈ 11 lines
- **Notes**: none.

### `theorem Cox.cubicCoeff_eq_zero_of_laurent_coeff` (private)
- **Type**: `(T J) (hTorder) (hJorder) (hTlead) (hJlead) (P) (houter) (hinner) (hsymm) (hcoeff : ∀ k : Fin 10, (bivariateLaurentEval T J P).coeff (-(cubicWeight (cubicI k) (cubicJ k))) = 0) : ∀ k, cubicCoeff P k = 0`
- **What**: If the ten triangular Laurent coefficients vanish, all ten polynomial coefficients vanish.
- **How**: well-founded induction downward on `Fin 10` (`wellFounded_gt.induction`) using `symmetricCubicLaurentExpansionFin_coeff_eq` for the step.
- **Hypotheses**: as stated.
- **Uses from project**: `bivariateLaurentEval`, `cubicWeight`, `cubicI`, `cubicJ`, `cubicCoeff`, `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`, `symmetricCubicLaurentExpansionFin_coeff_eq`
- **Used by**: `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`
- **Visibility**: private
- **Lines**: 323–342, proof ≈ 9 lines
- **Notes**: the "unit upper-triangular system is invertible" kernel.

### `theorem Cox.eq_zero_of_cubicCoeff_eq_zero` (private)
- **Type**: `(P) (houter) (hinner) (hsymm) (hall : ∀ k, cubicCoeff P k = 0) : P = 0`
- **What**: A symmetric cubic with all ten triangular coefficients zero is zero.
- **How**: rewrite by the expansion and `simp` with `hall`.
- **Hypotheses**: bidegree ≤ 3, symmetry.
- **Uses from project**: `eq_symmetricCubicExpansion`, `symmetricCubicExpansion_eq_fin`, `symmetricCubicPolynomialExpansionFin`, `symmetricBivariateMonomial`, `cubicCoeff`
- **Used by**: `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`
- **Visibility**: private
- **Lines**: 344–350, proof ≈ 2 lines
- **Notes**: none.

### `theorem Cox.symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux` (private)
- **Type**: as the public theorem but with `hcoeff : ∀ k : Fin 10, (bivariateLaurentEval T J P).coeff (-(cubicWeight (cubicI k) (cubicJ k))) = 0`.
- **What**: Indexed form of the detection theorem.
- **How**: chain `eq_zero_of_cubicCoeff_eq_zero` after `cubicCoeff_eq_zero_of_laurent_coeff`.
- **Hypotheses**: as stated.
- **Uses from project**: `eq_zero_of_cubicCoeff_eq_zero`, `cubicCoeff_eq_zero_of_laurent_coeff`, `bivariateLaurentEval`, `cubicWeight`, `cubicI`, `cubicJ`
- **Used by**: `symmetric_bidegree_three_eq_zero_of_laurent_coeff`
- **Visibility**: private
- **Lines**: 352–365, proof ≈ 3 lines
- **Notes**: this is the better public interface (see Observations).

### `theorem Cox.symmetric_bidegree_three_eq_zero_of_laurent_coeff`
- **Type**: `{K} [Field K] (T J : LaurentSeries K) (hTorder : T.order = -9) (hJorder : J.order = -3) (hTlead : T.leadingCoeff = 1) (hJlead : J.leadingCoeff = 1) (P : BivariatePolynomial K) (houter : P.natDegree ≤ 3) (hinner : ∀ i, (P.coeff i).natDegree ≤ 3) (hsymm : Polynomial.Bivariate.swap P = P) (hcoeff : let E := P.eval₂ (eval₂RingHom HahnSeries.C J) T; E.coeff 0 = 0 ∧ E.coeff (-9) = 0 ∧ … ∧ E.coeff (-36) = 0) : P = 0`
- **What**: A symmetric bivariate polynomial of bidegree ≤ 3 is detected by the ten Laurent coefficients of `P(T, J)` at exponents `0, -9, -12, -18, -21, -24, -27, -30, -33, -36`.
- **How**: destructure the tenfold conjunction, apply `_aux`, and match each `k : Fin 10` to its exponent by `fin_cases k <;> norm_num [cubicWeight, cubicI, cubicJ] <;> assumption`.
- **Hypotheses**: as listed.
- **Uses from project**: `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`, `bivariateLaurentEval`, `bivariateLaurentEvalHom`, `cubicWeight`, `cubicI`, `cubicJ`, `BivariatePolynomial`
- **Used by**: unused in file (LevelThree.lean:824 `modularPolynomialThreeDifference_eq_zero`)
- **Visibility**: public
- **Lines**: 368–389, proof ≈ 7 lines
- **Notes**: `hcoeff` uses a `let` inside a hypothesis with a 10-fold `∧`; the consumer (LevelThree.lean:815–832) has to build exactly that conjunction.

## File Summary
- Total declarations: 39 (12 defs, 27 theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `cubicWeight` (12), `cubicI`/`cubicJ` (13 each), `cubicCoeff` (8), `bivariateLaurentEval` (7), `symmetricBivariateMonomial` (4), `symmetricLaurentMonomial` (4), `laurentMonomial_coeff_zero_of_weight_lt` (2), `eq_symmetricCubicExpansion` (2), `symmetricCubicExpansion_eq_fin` (2)
- Unused declarations (not used by anything in this file): `symmetric_bidegree_three_eq_zero_of_laurent_coeff` (used by LevelThree.lean)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations

### Mathlib API candidates
- `bivariateLaurentEvalHom` (111–114) = `Polynomial.eval₂RingHom (Polynomial.eval₂RingHom HahnSeries.C J) T`. Mathlib (`Mathlib/Algebra/Polynomial/Bivariate.lean`, verified): `eval₂RingHom_eval₂RingHom (f) (x y) : eval₂RingHom (eval₂RingHom f x) y = (evalEvalRingHom x y).comp (mapRingHom (mapRingHom f))` (line 189), `eval₂_eval₂RingHom_apply` (194), `evalEvalRingHom` (151, `@[simps!]`), `aevalAeval : R[X][Y] →ₐ[R] A` (231) with `coe_aevalAeval_eq_evalEval` (237), `aevalAeval_C/X/Y` (241–245), plus the `evalEval_add/mul/pow/prod/finsetSum` family. With `HahnSeries.C_eq_algebraMap` (Multiplication.lean:928) the hom IS `aevalAeval J T` (inner variable ↦ `J`, `Y` ↦ `T`). CURRENT STATE: unchanged since July; `bivariateLaurentEval` (116–118), `_add` (121–125, = `map_add`), `_monomial` (128–134, = `eval₂_monomial` twice) would all disappear.
- `laurentMonomial_order` (144–158): `HahnSeries.order_mul` (Multiplication.lean:1022) + `order_pow` (:1034) — correct; the `T ≠ 0` derivation from `T.order = -9` uses `HahnSeries.order_zero` (Basic.lean:363) through `subst; simp`.
- `laurentMonomial_leadingCoeff` (160–165): `HahnSeries.leadingCoeff_mul` (Multiplication.lean:573) + project pow lemma; a mathlib `leadingCoeff_pow` (absent, see LaurentPolynomialEvaluation inventory) would make it `simp`.
- `cubicWeight_strictMono` (263–267): `Fin.strictMono_iff_lt_succ` (Order/Fin/Basic.lean:149) — correct.
- The triangular-system kernel (285–342): no mathlib analogue found for "Hahn series with pairwise distinct orders are linearly independent / a unit-triangular coefficient system forces zero" (searched `LinearIndependent`, `order` in `Mathlib/RingTheory/HahnSeries/`, `Finset.sum_eq_single` usages; nothing specific). It is composable from `HahnSeries.coeff_sum` (Addition.lean:321) and `Fintype.sum_eq_single`, as done.
- `coeff_comm_of_swap_eq` (21–27): mathlib has `Polynomial.Bivariate.swap` (Bivariate.lean:248) and `swap_monomial_monomial` (:281) but no coefficient-level `coeff (coeff (swap p) i) j = coeff (coeff p j) i`; the project supplies it as `BivariatePolynomial.coeff_coeff_swap` (Construction.lean:97). Upstream candidate.

### Missing API / repeated patterns
- **Vestigial quadruplet** `symmetricCubicExpansion_coeff_zero/_one/_two/_three` (64–86): each is a one-line instance of `_coeff_aux` (44–62) and each is used once (97–100). CURRENT STATE: the uniform `_aux` lemma requested in July now exists, but the four wrappers were kept; `eq_symmetricCubicExpansion` can do `interval_cases i <;> exact (symmetricCubicExpansion_coeff_aux P _ (by decide) (hinner _) hsymm).symm`.
- **`j > 3` / `i > 3` vanishing branches** (55–62 and 101–109) are the same 8-line `hj0…hj3`/`hi0…hi3` + `simp [coeff_monomial, coeff_C, eq_comm]` block at two levels.
- **Two encodings of the expansion** (`symmetricCubicExpansion` 29–42 vs `symmetricCubicPolynomialExpansionFin` 249–251, bridged by `symmetricCubicExpansion_eq_fin` 253–258): define only the `Fin 10` form and prove `_coeff_aux` against it, deleting 29–42 and 253–258.
- **Public statement shape** (368–389): the 10-fold `∧` with a `let` forces LevelThree.lean:800–832 to assemble the same conjunction; exposing the `Fin 10`-indexed `_aux` (or a `∀ k ∈ ({0,-9,…,-36} : Finset ℤ), E.coeff k = 0` form) would be cleaner and generalisable.
- **Same hom in LevelThree**: `P.eval₂ (Polynomial.eval₂RingHom HahnSeries.C J) T` is rebuilt at LevelThree.lean:643–649 (`bivariateLaurentEval_map`) and 656–659; a single public `bivariateLaurentEvalHom` (or direct `aevalAeval`) plus one `map` lemma serves both files.

### Junk candidates
- `bivariateLaurentEval` (116–118): coercion wrapper.
- `symmetricCubicExpansion_coeff_zero/_one/_two/_three` (64–86): one-line wrappers used once each.
- `symmetricCubicExpansion` (29–42) + `symmetricCubicExpansion_eq_fin` (253–258): redundant encoding (see above).

### Moral duplicates within this batch
- `laurentMonomial_coeff_zero_of_weight_lt` (176–182) is the same `coeff_eq_zero_of_lt_order`-after-`order_pow` step as LaurentPolynomialEvaluation.lean:131–135 and DiagonalLaurent.lean:238–242.
- `laurentMonomial_leadingCoeff` (160–165) and LaurentPolynomialEvaluation `laurentSeries_pow_leadingCoeff_of_eq_one` (103–110) are both instances of the missing `HahnSeries.leadingCoeff_pow`.

### Generalization notes
- **Bidegree parameter**: the file is NOT written so that "bidegree ≤ n" is a parameter change. Hard-coded in: `symmetricCubicExpansion` (29–42, literal 16 monomials), `_coeff_aux`/`eq_symmetricCubicExpansion` (`interval_cases` to 3 and explicit `≠ 0,1,2,3` facts, 52–62, 96–109), `cubicWeight = 9i + 3j` (142, encodes orders `-9`, `-3`), `cubicI`/`cubicJ` (233–235, literal `Fin 10` vectors), `cubicWeight_strictMono` (263–267, `fin_cases`), and the final theorem's ten explicit exponents (378–381, `fin_cases` 387). What IS generic: the kernel 285–342 (`symmetricCubicLaurentExpansionFin_coeff_eq`, `cubicCoeff_eq_zero_of_laurent_coeff`) works for any `Fintype ι` with `LinearOrder ι`, any `basis : ι → LaurentSeries K` and `weight : ι → ℤ` with `StrictMono weight`, `(basis k).coeff (-(weight k)) = 1`, and `(basis k).coeff (-(weight l)) = 0` for `k < l`. A general version would take `n`, index set `{(i,j) | j ≤ i ≤ n}`, weights `a·i + b·j` with `T.order = -a`, `J.order = -b`, and the strict-monotonicity hypothesis `b·n < a` (here `3·3 = 9`, which is why the weights are only just distinct: the mirror inequality at 215–216 is `9j + 3i < 9i + 3j`); the enumeration lemmas would then be `Finset`-based instead of `fin_cases`.
- All Laurent lemmas (144–231, 269–342) are stated for `Field K` but use only `order_mul`/`order_pow`/`leadingCoeff_mul` (`[NoZeroDivisors K]`) and `HahnSeries.C`: `[CommRing K] [IsDomain K]` suffices; `symmetricBivariateMonomial`, `cubicCoeff`, `symmetricCubicPolynomialExpansionFin` need only `Semiring K`.
