# XYin/PhD/Cox/SymmetricCubicLaurent.lean

**Source**: `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/SymmetricCubicLaurent.lean`
**Project-internal imports**: `XYin.PhD.Cox.LaurentPolynomialEvaluation`, `XYin.PhD.Cox.ModularPolynomial`

File purpose: proves that a symmetric bivariate polynomial of bidegree ≤ 3 over a field is zero as soon as ten specific Laurent coefficients of its evaluation at a pair of Laurent series (of orders −9 and −3, monic leading coefficients) vanish. The ten test exponents 0, −9, −12, −18, −21, −24, −27, −30, −33, −36 are the leading exponents −(9i+3j) of the triangular monomial family T^i J^j, j ≤ i ≤ 3, which is upper-triangular with unit diagonal against the coefficient family — a finite-detection / leading-term-elimination argument. All declarations live in namespace `Cox`.

### `theorem coeff_comm_of_swap_eq`
- **Type**: `{K : Type*} [CommRing K] (P : BivariatePolynomial K) (hsymm : Polynomial.Bivariate.swap P = P) (i j : ℕ) : (P.coeff i).coeff j = (P.coeff j).coeff i`
- **What**: For a symmetric bivariate polynomial (fixed by the variable swap), the coefficient array is symmetric: the (i,j) coefficient equals the (j,i) coefficient.
- **How**: Applies the (i,j)-coefficient extraction to the equation `swap P = P` and rewrites with the project lemma `BivariatePolynomial.coeff_coeff_swap`, which says the swapped polynomial's (i,j) coefficient is the original (j,i) coefficient.
- **Hypotheses**: `P` is fixed by the swap of its two variables; `K` a commutative ring.
- **Uses from project**: [`BivariatePolynomial`, `BivariatePolynomial.coeff_coeff_swap`]
- **Used by**: `symmetricCubicExpansion_coeff_zero`, `symmetricCubicExpansion_coeff_one`, `symmetricCubicExpansion_coeff_two`, `symmetricCubicExpansion_coeff_three`
- **Visibility**: private
- **Lines**: 21–27, proof 4 lines
- **Notes**: none

### `def symmetricCubicExpansion`
- **Type**: `{K : Type*} [CommRing K] (P : BivariatePolynomial K) : BivariatePolynomial K`
- **What**: The explicit ten-term expansion of a symmetric bidegree-≤3 bivariate polynomial: the sum of monomials `c i j = X^i Y^j · (P.coeff i).coeff j` over the triangle 0 ≤ j ≤ i ≤ 3, where each off-diagonal term appears symmetrized as `c i j + c j i` (with the mirror term using the same (i,j) coefficient of P).
- **How**: Direct definition as a sum of `Polynomial.monomial i (Polynomial.monomial j _)` terms; the diagonal terms (0,0), (1,1), (2,2), (3,3) appear once, the six off-diagonal pairs appear with both orientations sharing the coefficient `(P.coeff i).coeff j`.
- **Hypotheses**: none (definition; correctness for symmetric cubics is proved separately).
- **Uses from project**: [`BivariatePolynomial`]
- **Used by**: `symmetricCubicExpansion_coeff_zero`, `symmetricCubicExpansion_coeff_one`, `symmetricCubicExpansion_coeff_two`, `symmetricCubicExpansion_coeff_three`, `eq_symmetricCubicExpansion`, `symmetricCubicExpansion_eq_fin`, `eq_zero_of_cubicCoeff_eq_zero`
- **Visibility**: private
- **Lines**: 29–42
- **Notes**: none

### `theorem symmetricCubicExpansion_coeff_zero`
- **Type**: `{K : Type*} [CommRing K] (P : BivariatePolynomial K) (hinner : (P.coeff 0).natDegree ≤ 3) (hsymm : Polynomial.Bivariate.swap P = P) : (symmetricCubicExpansion P).coeff 0 = P.coeff 0`
- **What**: The outer coefficient at X-degree 0 of the ten-term expansion agrees with that of P itself.
- **How**: Coefficientwise check: for inner index j ≤ 3, `interval_cases` plus `Polynomial.coeff_monomial` and the symmetry `coeff_comm_of_swap_eq` (needed because the expansion stores the mirror coefficient at (j,0) as the (j,0)-entry of P); for j > 3 both sides vanish by `Polynomial.coeff_eq_zero_of_natDegree_lt`.
- **Hypotheses**: inner degree of `P.coeff 0` at most 3; P symmetric under swap.
- **Uses from project**: [`BivariatePolynomial`, `symmetricCubicExpansion`, `coeff_comm_of_swap_eq`]
- **Used by**: `eq_symmetricCubicExpansion`
- **Visibility**: private
- **Lines**: 44–61, proof 15 lines
- **Notes**: near-identical quadruplet with `_coeff_one`, `_coeff_two`, `_coeff_three` — a consolidation candidate

### `theorem symmetricCubicExpansion_coeff_one`
- **Type**: `{K : Type*} [CommRing K] (P : BivariatePolynomial K) (hinner : (P.coeff 1).natDegree ≤ 3) (hsymm : Polynomial.Bivariate.swap P = P) : (symmetricCubicExpansion P).coeff 1 = P.coeff 1`
- **What**: The outer coefficient at X-degree 1 of the ten-term expansion agrees with that of P.
- **How**: Same argument as `symmetricCubicExpansion_coeff_zero`: `interval_cases` on j ≤ 3 with `Polynomial.coeff_monomial` and `coeff_comm_of_swap_eq`; `Polynomial.coeff_eq_zero_of_natDegree_lt` kills j > 3.
- **Hypotheses**: inner degree of `P.coeff 1` at most 3; P symmetric under swap.
- **Uses from project**: [`BivariatePolynomial`, `symmetricCubicExpansion`, `coeff_comm_of_swap_eq`]
- **Used by**: `eq_symmetricCubicExpansion`
- **Visibility**: private
- **Lines**: 63–80, proof 15 lines
- **Notes**: copy of the `_coeff_zero` proof

### `theorem symmetricCubicExpansion_coeff_two`
- **Type**: `{K : Type*} [CommRing K] (P : BivariatePolynomial K) (hinner : (P.coeff 2).natDegree ≤ 3) (hsymm : Polynomial.Bivariate.swap P = P) : (symmetricCubicExpansion P).coeff 2 = P.coeff 2`
- **What**: The outer coefficient at X-degree 2 of the ten-term expansion agrees with that of P.
- **How**: Same argument as `symmetricCubicExpansion_coeff_zero` (`interval_cases`, `Polynomial.coeff_monomial`, `coeff_comm_of_swap_eq`, `Polynomial.coeff_eq_zero_of_natDegree_lt`).
- **Hypotheses**: inner degree of `P.coeff 2` at most 3; P symmetric under swap.
- **Uses from project**: [`BivariatePolynomial`, `symmetricCubicExpansion`, `coeff_comm_of_swap_eq`]
- **Used by**: `eq_symmetricCubicExpansion`
- **Visibility**: private
- **Lines**: 82–99, proof 15 lines
- **Notes**: copy of the `_coeff_zero` proof

### `theorem symmetricCubicExpansion_coeff_three`
- **Type**: `{K : Type*} [CommRing K] (P : BivariatePolynomial K) (hinner : (P.coeff 3).natDegree ≤ 3) (hsymm : Polynomial.Bivariate.swap P = P) : (symmetricCubicExpansion P).coeff 3 = P.coeff 3`
- **What**: The outer coefficient at X-degree 3 of the ten-term expansion agrees with that of P.
- **How**: Same argument as `symmetricCubicExpansion_coeff_zero` (`interval_cases`, `Polynomial.coeff_monomial`, `coeff_comm_of_swap_eq`, `Polynomial.coeff_eq_zero_of_natDegree_lt`).
- **Hypotheses**: inner degree of `P.coeff 3` at most 3; P symmetric under swap.
- **Uses from project**: [`BivariatePolynomial`, `symmetricCubicExpansion`, `coeff_comm_of_swap_eq`]
- **Used by**: `eq_symmetricCubicExpansion`
- **Visibility**: private
- **Lines**: 101–118, proof 15 lines
- **Notes**: copy of the `_coeff_zero` proof

### `theorem eq_symmetricCubicExpansion`
- **Type**: `{K : Type*} [CommRing K] (P : BivariatePolynomial K) (houter : P.natDegree ≤ 3) (hinner : ∀ i, (P.coeff i).natDegree ≤ 3) (hsymm : Polynomial.Bivariate.swap P = P) : P = symmetricCubicExpansion P`
- **What**: A symmetric bivariate polynomial of bidegree ≤ 3 equals its explicit ten-term symmetrized expansion; i.e. the ten triangular coefficients determine P.
- **How**: Outer-coefficientwise: `interval_cases` for i ≤ 3 dispatches to the four `symmetricCubicExpansion_coeff_*` lemmas; for i > 3, `Polynomial.coeff_eq_zero_of_natDegree_lt` shows both sides vanish.
- **Hypotheses**: outer degree ≤ 3, all inner degrees ≤ 3, P symmetric under swap.
- **Uses from project**: [`BivariatePolynomial`, `symmetricCubicExpansion`, `symmetricCubicExpansion_coeff_zero`, `symmetricCubicExpansion_coeff_one`, `symmetricCubicExpansion_coeff_two`, `symmetricCubicExpansion_coeff_three`]
- **Used by**: `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`, `eq_zero_of_cubicCoeff_eq_zero`
- **Visibility**: private
- **Lines**: 120–141, proof 18 lines
- **Notes**: none

### `def bivariateLaurentEvalHom`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) : BivariatePolynomial K →+* LaurentSeries K`
- **What**: The ring homomorphism evaluating a bivariate polynomial at the pair of Laurent series (T, J): outer variable ↦ T, inner variable ↦ J.
- **How**: Composition of two `Polynomial.eval₂RingHom`s over the constant embedding `HahnSeries.C : K →+* LaurentSeries K`.
- **Hypotheses**: K a field.
- **Uses from project**: [`BivariatePolynomial`]
- **Used by**: `bivariateLaurentEval`, `bivariateLaurentEval_add`, `bivariateLaurentEval_monomial`, `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff`
- **Visibility**: private
- **Lines**: 143–146
- **Notes**: none

### `def bivariateLaurentEval`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (P : BivariatePolynomial K) : LaurentSeries K`
- **What**: The value of the bivariate polynomial P at the Laurent-series pair (T, J), as a plain function (unbundled form of `bivariateLaurentEvalHom`).
- **How**: Applies `bivariateLaurentEvalHom T J` to P.
- **Hypotheses**: K a field.
- **Uses from project**: [`BivariatePolynomial`, `bivariateLaurentEvalHom`]
- **Used by**: `bivariateLaurentEval_add`, `bivariateLaurentEval_monomial`, `bivariateLaurentEval_symmetricBivariateMonomial`, `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`, `cubicCoeff_eq_zero_of_laurent_coeff`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff`
- **Visibility**: private
- **Lines**: 148–150
- **Notes**: none

### `theorem bivariateLaurentEval_add`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (P Q : BivariatePolynomial K) : bivariateLaurentEval T J (P + Q) = bivariateLaurentEval T J P + bivariateLaurentEval T J Q`
- **What**: Bivariate Laurent evaluation is additive.
- **How**: Immediate from `map_add` applied to the ring hom `bivariateLaurentEvalHom`.
- **Hypotheses**: K a field.
- **Uses from project**: [`BivariatePolynomial`, `bivariateLaurentEval`, `bivariateLaurentEvalHom`]
- **Used by**: `bivariateLaurentEval_symmetricBivariateMonomial`
- **Visibility**: private
- **Lines**: 152–157, proof 1 line
- **Notes**: @[simp]

### `theorem bivariateLaurentEval_monomial`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (i j : ℕ) (a : K) : bivariateLaurentEval T J (Polynomial.monomial i (Polynomial.monomial j a)) = HahnSeries.C a * T ^ i * J ^ j`
- **What**: Evaluating the monomial a·X^i Y^j at (T, J) gives a·T^i·J^j (constant embedded via `HahnSeries.C`).
- **How**: Unfolds the evaluation hom and uses `Polynomial.eval₂_monomial` twice, closing with `ring`.
- **Hypotheses**: K a field.
- **Uses from project**: [`bivariateLaurentEval`, `bivariateLaurentEvalHom`]
- **Used by**: `bivariateLaurentEval_symmetricBivariateMonomial`
- **Visibility**: private
- **Lines**: 159–166, proof 3 lines
- **Notes**: @[simp]

### `def symmetricBivariateMonomial`
- **Type**: `{K : Type*} [Field K] (i j : ℕ) (a : K) : BivariatePolynomial K`
- **What**: The symmetrized bivariate monomial with coefficient a: a·X^i Y^j when i = j, and a·(X^i Y^j + X^j Y^i) otherwise.
- **How**: `if i = j then` single `Polynomial.monomial` term `else` sum of the term and its mirror.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial`]
- **Used by**: `bivariateLaurentEval_symmetricBivariateMonomial`, `symmetricCubicPolynomialExpansionFin`, `symmetricCubicExpansion_eq_fin`, `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`
- **Visibility**: private
- **Lines**: 168–172
- **Notes**: none

### `def cubicWeight`
- **Type**: `(i j : ℕ) : ℤ`
- **What**: The weight 9i + 3j of the monomial T^i J^j — the negative of the order of T^i J^j when ord T = −9 and ord J = −3. The ten distinct weights of the triangle j ≤ i ≤ 3 give the ten detection exponents.
- **How**: Direct arithmetic definition `9 * i + 3 * j` over ℤ.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `laurentMonomial_order`, `laurentMonomial_coeff_self`, `laurentMonomial_coeff_zero_of_weight_lt`, `symmetricLaurentMonomial_coeff_self`, `symmetricLaurentMonomial_coeff_zero_of_weight_lt`, `cubicWeight_strictMono`, `cubicBasis_coeff_self`, `cubicBasis_coeff_zero_of_lt`, `symmetricCubicLaurentExpansionFin_coeff_eq`, `cubicCoeff_eq_zero_of_laurent_coeff`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff`
- **Visibility**: private
- **Lines**: 174
- **Notes**: none

### `theorem laurentMonomial_order`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (hT : T.order = -9) (hJ : J.order = -3) (i j : ℕ) : (T ^ i * J ^ j).order = -(cubicWeight i j)`
- **What**: With ord T = −9 and ord J = −3, the Laurent series T^i J^j has order −(9i + 3j).
- **How**: Orders are additive on products of nonzero Hahn series: `HahnSeries.order_mul` and `HahnSeries.order_pow` (nonvanishing of T, J follows since a zero series has order 0 ≠ −9, −3), then integer arithmetic.
- **Hypotheses**: T has order −9, J has order −3.
- **Uses from project**: [`cubicWeight`]
- **Used by**: `laurentMonomial_coeff_self`, `laurentMonomial_coeff_zero_of_weight_lt`
- **Visibility**: private
- **Lines**: 176–190, proof 12 lines
- **Notes**: none

### `theorem laurentMonomial_leadingCoeff`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (hT : T.leadingCoeff = 1) (hJ : J.leadingCoeff = 1) (i j : ℕ) : (T ^ i * J ^ j).leadingCoeff = 1`
- **What**: A product of powers of two monic (leading coefficient 1) Laurent series is monic.
- **How**: `HahnSeries.leadingCoeff_mul` (leading coefficients multiply over an integral domain of coefficients) combined with the project lemma `laurentSeries_pow_leadingCoeff_of_eq_one` for each power.
- **Hypotheses**: T and J both have leading coefficient 1.
- **Uses from project**: [`laurentSeries_pow_leadingCoeff_of_eq_one`]
- **Used by**: `laurentMonomial_coeff_self`
- **Visibility**: private
- **Lines**: 192–197, proof 3 lines
- **Notes**: none

### `theorem laurentMonomial_coeff_self`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (hTorder : T.order = -9) (hJorder : J.order = -3) (hTlead : T.leadingCoeff = 1) (hJlead : J.leadingCoeff = 1) (i j : ℕ) : (T ^ i * J ^ j).coeff (-(cubicWeight i j)) = 1`
- **What**: The coefficient of T^i J^j at its own leading exponent −(9i+3j) is 1: these monomials are "unit diagonal" against the weight grading.
- **How**: The coefficient at the order is the leading coefficient (`HahnSeries.leadingCoeff_eq`), so this reduces to `laurentMonomial_order` plus `laurentMonomial_leadingCoeff`.
- **Hypotheses**: ord T = −9, ord J = −3, both leading coefficients 1.
- **Uses from project**: [`cubicWeight`, `laurentMonomial_order`, `laurentMonomial_leadingCoeff`]
- **Used by**: `symmetricLaurentMonomial_coeff_self`
- **Visibility**: private
- **Lines**: 199–206, proof 3 lines
- **Notes**: none

### `theorem laurentMonomial_coeff_zero_of_weight_lt`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (hT : T.order = -9) (hJ : J.order = -3) (i j r s : ℕ) (hweight : cubicWeight i j < cubicWeight r s) : (T ^ i * J ^ j).coeff (-(cubicWeight r s)) = 0`
- **What**: A monomial T^i J^j of strictly smaller weight has zero coefficient at the (more negative) leading exponent of a heavier monomial T^r J^s — the triangularity that drives the detection.
- **How**: `HahnSeries.coeff_eq_zero_of_lt_order`: the exponent −weight(r,s) lies strictly below the order −weight(i,j) of the series (by `laurentMonomial_order` and negation of the weight inequality).
- **Hypotheses**: ord T = −9, ord J = −3, weight(i,j) < weight(r,s).
- **Uses from project**: [`cubicWeight`, `laurentMonomial_order`]
- **Used by**: `symmetricLaurentMonomial_coeff_self`, `symmetricLaurentMonomial_coeff_zero_of_weight_lt`
- **Visibility**: private
- **Lines**: 208–214, proof 4 lines
- **Notes**: none

### `def symmetricLaurentMonomial`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (i j : ℕ) : LaurentSeries K`
- **What**: The Laurent-series counterpart of the symmetrized monomial: T^i J^j when i = j, else T^i J^j + T^j J^i.
- **How**: Direct `if i = j then … else …` definition mirroring `symmetricBivariateMonomial`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `bivariateLaurentEval_symmetricBivariateMonomial`, `symmetricLaurentMonomial_coeff_self`, `symmetricLaurentMonomial_coeff_zero_of_weight_lt`, `cubicBasis`
- **Visibility**: private
- **Lines**: 216–218
- **Notes**: none

### `theorem bivariateLaurentEval_symmetricBivariateMonomial`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (i j : ℕ) (a : K) : bivariateLaurentEval T J (symmetricBivariateMonomial i j a) = HahnSeries.C a * symmetricLaurentMonomial T J i j`
- **What**: Evaluating the symmetrized polynomial monomial at (T, J) gives the constant a times the symmetrized Laurent monomial.
- **How**: Case split on i = j; each branch reduces via `bivariateLaurentEval_monomial` (and additivity `bivariateLaurentEval_add` in the off-diagonal case) followed by ring manipulation, using `HahnSeries.C_mul_eq_smul` to normalise the constant multiple.
- **Hypotheses**: K a field.
- **Uses from project**: [`bivariateLaurentEval`, `symmetricBivariateMonomial`, `symmetricLaurentMonomial`, `bivariateLaurentEval_monomial`, `bivariateLaurentEval_add`]
- **Used by**: `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`
- **Visibility**: private
- **Lines**: 220–232, proof 9 lines
- **Notes**: none

### `theorem symmetricLaurentMonomial_coeff_self`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (hTorder : T.order = -9) (hJorder : J.order = -3) (hTlead : T.leadingCoeff = 1) (hJlead : J.leadingCoeff = 1) (i j : ℕ) (hji : j ≤ i) : (symmetricLaurentMonomial T J i j).coeff (-(cubicWeight i j)) = 1`
- **What**: The symmetrized Laurent monomial for a triangle index (j ≤ i) has coefficient 1 at its leading exponent −(9i+3j): the dominant orientation contributes 1 and the mirror term contributes 0.
- **How**: Diagonal case is `laurentMonomial_coeff_self` directly; off-diagonal case adds `laurentMonomial_coeff_self` for the (i,j) term and kills the mirror (j,i) term with `laurentMonomial_coeff_zero_of_weight_lt`, since weight(j,i) < weight(i,j) exactly when j < i (9j+3i < 9i+3j).
- **Hypotheses**: ord T = −9, ord J = −3, unit leading coefficients, j ≤ i.
- **Uses from project**: [`symmetricLaurentMonomial`, `cubicWeight`, `laurentMonomial_coeff_self`, `laurentMonomial_coeff_zero_of_weight_lt`]
- **Used by**: `cubicBasis_coeff_self`
- **Visibility**: private
- **Lines**: 234–248, proof 10 lines
- **Notes**: none

### `theorem symmetricLaurentMonomial_coeff_zero_of_weight_lt`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (hT : T.order = -9) (hJ : J.order = -3) (i j r s : ℕ) (hji : j ≤ i) (hweight : cubicWeight i j < cubicWeight r s) : (symmetricLaurentMonomial T J i j).coeff (-(cubicWeight r s)) = 0`
- **What**: A lighter symmetrized monomial (triangle-indexed, weight below weight(r,s)) has zero coefficient at the leading exponent of the heavier one — strict upper-triangularity of the ten-element system.
- **How**: Both orientations are handled by `laurentMonomial_coeff_zero_of_weight_lt`: for the mirror term one checks weight(j,i) ≤ weight(i,j) < weight(r,s) via linear arithmetic on 9i+3j using j ≤ i.
- **Hypotheses**: ord T = −9, ord J = −3, j ≤ i, weight(i,j) < weight(r,s).
- **Uses from project**: [`symmetricLaurentMonomial`, `cubicWeight`, `laurentMonomial_coeff_zero_of_weight_lt`]
- **Used by**: `cubicBasis_coeff_zero_of_lt`
- **Visibility**: private
- **Lines**: 250–263, proof 9 lines
- **Notes**: none

### `def cubicI`
- **Type**: `Fin 10 → ℕ`
- **What**: The outer-exponent component of the enumeration of the ten triangle indices (i,j), 0 ≤ j ≤ i ≤ 3, listed in increasing weight order: `![0, 1, 1, 2, 2, 2, 3, 3, 3, 3]`.
- **How**: `Matrix.of`-style vector literal `![…]`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `cubicCoeff`, `cubicBasis`, `symmetricCubicLaurentExpansionFin` (via those), `symmetricCubicPolynomialExpansionFin`, `symmetricCubicExpansion_eq_fin`, `cubicJ_le_cubicI`, `cubicWeight_strictMono`, `cubicBasis_coeff_self`, `cubicBasis_coeff_zero_of_lt`, `symmetricCubicLaurentExpansionFin_coeff_eq`, `cubicCoeff_eq_zero_of_laurent_coeff`, `eq_zero_of_cubicCoeff_eq_zero`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff`
- **Visibility**: private
- **Lines**: 265
- **Notes**: none

### `def cubicJ`
- **Type**: `Fin 10 → ℕ`
- **What**: The inner-exponent component of the same enumeration: `![0, 0, 1, 0, 1, 2, 0, 1, 2, 3]`, paired with `cubicI` so that k ↦ (cubicI k, cubicJ k) runs through the triangle in strictly increasing weight 9i+3j: 0, 9, 12, 18, 21, 24, 27, 30, 33, 36.
- **How**: Vector literal `![…]`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: same list as `cubicI`
- **Visibility**: private
- **Lines**: 267
- **Notes**: none

### `def cubicCoeff`
- **Type**: `{K : Type*} [Field K] (P : BivariatePolynomial K) (k : Fin 10) : K`
- **What**: The k-th triangular coefficient of P: `(P.coeff (cubicI k)).coeff (cubicJ k)` — the ten unknowns of the symmetric cubic.
- **How**: Direct coefficient extraction through the enumeration.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial`, `cubicI`, `cubicJ`]
- **Used by**: `symmetricCubicLaurentExpansionFin`, `symmetricCubicPolynomialExpansionFin`, `symmetricCubicExpansion_eq_fin`, `symmetricCubicLaurentExpansionFin_coeff_eq`, `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`, `cubicCoeff_eq_zero_of_laurent_coeff`, `eq_zero_of_cubicCoeff_eq_zero`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`
- **Visibility**: private
- **Lines**: 269–271
- **Notes**: none

### `def cubicBasis`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (k : Fin 10) : LaurentSeries K`
- **What**: The k-th member of the ten-element Laurent "basis": the symmetrized Laurent monomial at the k-th triangle index.
- **How**: `symmetricLaurentMonomial T J (cubicI k) (cubicJ k)`.
- **Hypotheses**: none.
- **Uses from project**: [`symmetricLaurentMonomial`, `cubicI`, `cubicJ`]
- **Used by**: `symmetricCubicLaurentExpansionFin`, `cubicBasis_coeff_self`, `cubicBasis_coeff_zero_of_lt`
- **Visibility**: private
- **Lines**: 273–275
- **Notes**: none

### `def symmetricCubicLaurentExpansionFin`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (P : BivariatePolynomial K) : LaurentSeries K`
- **What**: The Laurent series ∑ₖ cubicCoeff P k · cubicBasis T J k — the value of the symmetric cubic P at (T, J) written as a Fin-10 linear combination of the basis monomials.
- **How**: `∑ k : Fin 10, HahnSeries.C (cubicCoeff P k) * cubicBasis T J k`.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial`, `cubicCoeff`, `cubicBasis`]
- **Used by**: `symmetricCubicLaurentExpansionFin_coeff_eq`, `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`
- **Visibility**: private
- **Lines**: 277–279
- **Notes**: none

### `def symmetricCubicPolynomialExpansionFin`
- **Type**: `{K : Type*} [Field K] (P : BivariatePolynomial K) : BivariatePolynomial K`
- **What**: The polynomial-side Fin-10 form of the expansion: ∑ₖ symmetrized monomial at index k with coefficient cubicCoeff P k.
- **How**: `∑ k : Fin 10, symmetricBivariateMonomial (cubicI k) (cubicJ k) (cubicCoeff P k)`.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial`, `symmetricBivariateMonomial`, `cubicI`, `cubicJ`, `cubicCoeff`]
- **Used by**: `symmetricCubicExpansion_eq_fin`, `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`
- **Visibility**: private
- **Lines**: 281–283
- **Notes**: none

### `theorem symmetricCubicExpansion_eq_fin`
- **Type**: `{K : Type*} [Field K] (P : BivariatePolynomial K) : symmetricCubicExpansion P = symmetricCubicPolynomialExpansionFin P`
- **What**: The hand-written ten-term expansion coincides with the Fin-10 indexed sum of symmetrized monomials — bridging the two presentations.
- **How**: Expands the Fin sum with `Fin.sum_univ_succ`, unfolds `symmetricBivariateMonomial`/`cubicCoeff`/`cubicI`/`cubicJ` by `simp`, and matches term-by-term with `abel`.
- **Hypotheses**: K a field.
- **Uses from project**: [`symmetricCubicExpansion`, `symmetricCubicPolynomialExpansionFin`, `symmetricBivariateMonomial`, `cubicCoeff`, `cubicI`, `cubicJ`]
- **Used by**: `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`
- **Visibility**: private
- **Lines**: 285–290, proof 4 lines
- **Notes**: none

### `theorem cubicJ_le_cubicI`
- **Type**: `(k : Fin 10) : cubicJ k ≤ cubicI k`
- **What**: The enumeration really stays inside the triangle j ≤ i.
- **How**: `fin_cases k` and numeric evaluation of the two vector literals.
- **Hypotheses**: none.
- **Uses from project**: [`cubicI`, `cubicJ`]
- **Used by**: `cubicBasis_coeff_self`, `cubicBasis_coeff_zero_of_lt`
- **Visibility**: private
- **Lines**: 292–293, proof 1 line
- **Notes**: none

### `theorem cubicWeight_strictMono`
- **Type**: `StrictMono (fun k : Fin 10 ↦ cubicWeight (cubicI k) (cubicJ k))`
- **What**: The ten weights 0 < 9 < 12 < 18 < 21 < 24 < 27 < 30 < 33 < 36 are strictly increasing along the enumeration — the key ordering making the coefficient system triangular.
- **How**: `Fin.strictMono_iff_lt_succ` reduces to adjacent comparisons, each verified numerically by `fin_cases`.
- **Hypotheses**: none.
- **Uses from project**: [`cubicWeight`, `cubicI`, `cubicJ`]
- **Used by**: `cubicBasis_coeff_zero_of_lt`
- **Visibility**: private
- **Lines**: 295–299, proof 3 lines
- **Notes**: none

### `theorem cubicBasis_coeff_self`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (hTorder : T.order = -9) (hJorder : J.order = -3) (hTlead : T.leadingCoeff = 1) (hJlead : J.leadingCoeff = 1) (k : Fin 10) : (cubicBasis T J k).coeff (-(cubicWeight (cubicI k) (cubicJ k))) = 1`
- **What**: The k-th basis element has coefficient 1 at its own detection exponent (unit diagonal of the 10×10 system).
- **How**: Instance of `symmetricLaurentMonomial_coeff_self`, feeding in `cubicJ_le_cubicI`.
- **Hypotheses**: ord T = −9, ord J = −3, unit leading coefficients.
- **Uses from project**: [`cubicBasis`, `cubicWeight`, `cubicI`, `cubicJ`, `symmetricLaurentMonomial_coeff_self`, `cubicJ_le_cubicI`]
- **Used by**: `symmetricCubicLaurentExpansionFin_coeff_eq`
- **Visibility**: private
- **Lines**: 301–307, proof 2 lines
- **Notes**: none

### `theorem cubicBasis_coeff_zero_of_lt`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (hT : T.order = -9) (hJ : J.order = -3) {k l : Fin 10} (hkl : k < l) : (cubicBasis T J k).coeff (-(cubicWeight (cubicI l) (cubicJ l))) = 0`
- **What**: An earlier (lighter) basis element vanishes at the detection exponent of any later one (strict upper triangularity in the enumeration order).
- **How**: Instance of `symmetricLaurentMonomial_coeff_zero_of_weight_lt`, with the weight inequality supplied by `cubicWeight_strictMono` and the triangle condition by `cubicJ_le_cubicI`.
- **Hypotheses**: ord T = −9, ord J = −3, k < l in Fin 10.
- **Uses from project**: [`cubicBasis`, `cubicWeight`, `cubicI`, `cubicJ`, `symmetricLaurentMonomial_coeff_zero_of_weight_lt`, `cubicJ_le_cubicI`, `cubicWeight_strictMono`]
- **Used by**: `symmetricCubicLaurentExpansionFin_coeff_eq`
- **Visibility**: private
- **Lines**: 309–315, proof 3 lines
- **Notes**: none

### `theorem symmetricCubicLaurentExpansionFin_coeff_eq`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (P : BivariatePolynomial K) (hTorder : T.order = -9) (hJorder : J.order = -3) (hTlead : T.leadingCoeff = 1) (hJlead : J.leadingCoeff = 1) (k : Fin 10) (hzero : ∀ l, k < l → cubicCoeff P l = 0) : (symmetricCubicLaurentExpansionFin T J P).coeff (-(cubicWeight (cubicI k) (cubicJ k))) = cubicCoeff P k`
- **What**: Back-substitution step: if all coefficients after index k already vanish, then the Laurent coefficient of the expansion at the k-th detection exponent reads off exactly the k-th unknown coefficient.
- **How**: Expands `HahnSeries.coeff_sum` and isolates the k-th summand with `Fintype.sum_eq_single`; the diagonal term contributes `cubicCoeff P k` by `cubicBasis_coeff_self`, earlier terms vanish by `cubicBasis_coeff_zero_of_lt`, later terms vanish by the hypothesis hzero.
- **Hypotheses**: order/leading-coefficient normalisations of T and J; all later triangular coefficients of P vanish.
- **Uses from project**: [`symmetricCubicLaurentExpansionFin`, `cubicCoeff`, `cubicWeight`, `cubicI`, `cubicJ`, `cubicBasis_coeff_self`, `cubicBasis_coeff_zero_of_lt`]
- **Used by**: `cubicCoeff_eq_zero_of_laurent_coeff`
- **Visibility**: private
- **Lines**: 317–336, proof 13 lines
- **Notes**: none

### `theorem bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (P : BivariatePolynomial K) (houter : P.natDegree ≤ 3) (hinner : ∀ i, (P.coeff i).natDegree ≤ 3) (hsymm : Polynomial.Bivariate.swap P = P) : bivariateLaurentEval T J P = symmetricCubicLaurentExpansionFin T J P`
- **What**: The evaluation of a symmetric bidegree-≤3 polynomial at (T, J) equals the ten-term linear combination of basis Laurent monomials with the triangular coefficients of P.
- **How**: Rewrites P by `eq_symmetricCubicExpansion` and `symmetricCubicExpansion_eq_fin`, pushes the ring hom through the sum with `map_sum`, and evaluates each summand with `bivariateLaurentEval_symmetricBivariateMonomial`.
- **Hypotheses**: bidegree ≤ 3 in both variables, P symmetric under swap.
- **Uses from project**: [`bivariateLaurentEval`, `bivariateLaurentEvalHom`, `symmetricCubicLaurentExpansionFin`, `symmetricCubicPolynomialExpansionFin`, `symmetricBivariateMonomial`, `eq_symmetricCubicExpansion`, `symmetricCubicExpansion_eq_fin`, `bivariateLaurentEval_symmetricBivariateMonomial`, `cubicI`, `cubicJ`, `cubicCoeff`]
- **Used by**: `cubicCoeff_eq_zero_of_laurent_coeff`
- **Visibility**: private
- **Lines**: 338–353, proof 11 lines
- **Notes**: none

### `theorem cubicCoeff_eq_zero_of_laurent_coeff`
- **Type**: `{K} [Field K] (T J : LaurentSeries K) (hTorder hJorder hTlead hJlead) (P) (houter : P.natDegree ≤ 3) (hinner : ∀ i, (P.coeff i).natDegree ≤ 3) (hsymm : swap P = P) (hcoeff : ∀ k : Fin 10, (bivariateLaurentEval T J P).coeff (-(cubicWeight (cubicI k) (cubicJ k))) = 0) : ∀ k, cubicCoeff P k = 0`
- **What**: The heart of the detection: if all ten Laurent coefficients of the evaluation vanish, then all ten triangular coefficients of P vanish. This is back-substitution through the strictly triangular unit-diagonal system, from the heaviest index downward.
- **How**: Downward induction over Fin 10 via `Fin.reverseInduction`: at each index k, once all later coefficients vanish, `symmetricCubicLaurentExpansionFin_coeff_eq` (after rewriting the evaluation with `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`) identifies the k-th Laurent coefficient with cubicCoeff P k, which is zero by hypothesis. An auxiliary claim `hfrom : ∀ k l, k ≤ l → cubicCoeff P l = 0` organises the induction.
- **Hypotheses**: order/leading normalisations of T, J; bidegree ≤ 3; symmetry; the ten Laurent coefficients vanish.
- **Uses from project**: [`bivariateLaurentEval`, `cubicWeight`, `cubicI`, `cubicJ`, `cubicCoeff`, `bivariateLaurentEval_eq_symmetricCubicLaurentExpansionFin`, `symmetricCubicLaurentExpansionFin_coeff_eq`]
- **Used by**: `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`
- **Visibility**: private
- **Lines**: 355–392, proof 27 lines
- **Notes**: longest proof in the file (just under 30 lines); the `Fin.reverseInduction` bookkeeping with `Fin.castSucc_lt_iff_succ_le` is the delicate part

### `theorem eq_zero_of_cubicCoeff_eq_zero`
- **Type**: `{K : Type*} [Field K] (P : BivariatePolynomial K) (houter : P.natDegree ≤ 3) (hinner : ∀ i, (P.coeff i).natDegree ≤ 3) (hsymm : Polynomial.Bivariate.swap P = P) (hall : ∀ k, cubicCoeff P k = 0) : P = 0`
- **What**: A symmetric bidegree-≤3 polynomial all of whose ten triangular coefficients vanish is the zero polynomial.
- **How**: Rewrites P as its ten-term expansion via `eq_symmetricCubicExpansion`, then substitutes the ten vanishing coefficients (extracted from `hall` at each of the ten indices) so every monomial of `symmetricCubicExpansion` collapses to 0.
- **Hypotheses**: bidegree ≤ 3, symmetry, all ten triangular coefficients zero.
- **Uses from project**: [`BivariatePolynomial`, `cubicCoeff`, `cubicI`, `cubicJ`, `eq_symmetricCubicExpansion`, `symmetricCubicExpansion`]
- **Used by**: `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`
- **Visibility**: private
- **Lines**: 394–411, proof 14 lines
- **Notes**: none

### `theorem symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`
- **Type**: `{K} [Field K] (T J : LaurentSeries K) (hTorder hJorder hTlead hJlead) (P) (houter) (hinner) (hsymm) (hcoeff : ∀ k : Fin 10, (bivariateLaurentEval T J P).coeff (-(cubicWeight (cubicI k) (cubicJ k))) = 0) : P = 0`
- **What**: Combination step: ten vanishing Laurent coefficients (indexed abstractly through the enumeration) force P = 0.
- **How**: Chains `cubicCoeff_eq_zero_of_laurent_coeff` (Laurent coefficients ⇒ triangular coefficients vanish) into `eq_zero_of_cubicCoeff_eq_zero` (triangular coefficients ⇒ P = 0).
- **Hypotheses**: same normalisations and degree/symmetry hypotheses as above.
- **Uses from project**: [`bivariateLaurentEval`, `cubicWeight`, `cubicI`, `cubicJ`, `eq_zero_of_cubicCoeff_eq_zero`, `cubicCoeff_eq_zero_of_laurent_coeff`]
- **Used by**: `symmetric_bidegree_three_eq_zero_of_laurent_coeff`
- **Visibility**: private
- **Lines**: 413–426, proof 3 lines
- **Notes**: none

### `theorem symmetric_bidegree_three_eq_zero_of_laurent_coeff`
- **Type**: `{K : Type*} [Field K] (T J : LaurentSeries K) (hTorder : T.order = -9) (hJorder : J.order = -3) (hTlead : T.leadingCoeff = 1) (hJlead : J.leadingCoeff = 1) (P : BivariatePolynomial K) (houter : P.natDegree ≤ 3) (hinner : ∀ i, (P.coeff i).natDegree ≤ 3) (hsymm : Polynomial.Bivariate.swap P = P) (hcoeff : let E := P.eval₂ (Polynomial.eval₂RingHom HahnSeries.C J) T; E.coeff 0 = 0 ∧ E.coeff (-9) = 0 ∧ … ∧ E.coeff (-36) = 0) : P = 0`
- **What**: The public API of the file: a symmetric bivariate cubic over a field is zero iff the ten explicit Laurent coefficients (at exponents 0, −9, −12, −18, −21, −24, −27, −30, −33, −36) of its evaluation at (T, J) vanish, when T, J are monic Laurent series of orders −9, −3. Downstream this detects identities among modular functions from finitely many q-expansion coefficients (T a Hauptmodul-type series, J the j-function).
- **How**: Destructures the ten concrete coefficient hypotheses and feeds them into `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`, using `fin_cases` + `norm_num` to match each concrete exponent with `-(cubicWeight (cubicI k) (cubicJ k))` and to unfold `bivariateLaurentEval` back to the `eval₂` form of the statement.
- **Hypotheses**: ord T = −9, ord J = −3, leading coefficients 1; P of bidegree ≤ 3 in each variable; P symmetric; the ten Laurent coefficients vanish.
- **Uses from project**: [`BivariatePolynomial`, `bivariateLaurentEval`, `bivariateLaurentEvalHom`, `cubicWeight`, `cubicI`, `cubicJ`, `symmetric_bidegree_three_eq_zero_of_laurent_coeff_aux`]
- **Used by**: unused in file (public API; consumed by downstream Cox files, e.g. LevelThree)
- **Visibility**: public
- **Lines**: 429–450, proof 7 lines
- **Notes**: only public declaration in the file; has docstring

### File Summary
- Total declarations: 38 (12 defs, 26 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): `symmetricCubicExpansion` (7), `coeff_comm_of_swap_eq` (4), `bivariateLaurentEvalHom` (5), `bivariateLaurentEval` (7), `symmetricBivariateMonomial` (4), `cubicWeight` (12), `symmetricLaurentMonomial` (4), `cubicI`/`cubicJ` (~13 each), `cubicCoeff` (8), `cubicBasis` (3)
- Unused declarations (not used by anything in this file): `symmetric_bidegree_three_eq_zero_of_laurent_coeff` (the public entry point; everything else feeds into it)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [] (longest is `cubicCoeff_eq_zero_of_laurent_coeff` at ~27 proof lines, lines 355–392)
