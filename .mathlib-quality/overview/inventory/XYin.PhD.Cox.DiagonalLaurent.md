# XYin/PhD/Cox/DiagonalLaurent.lean

**Source**: `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/DiagonalLaurent.lean`
**Project-internal imports**: `XYin.PhD.Cox.ModularPolynomial`
**Module doc**: The Laurent leading term of the diagonal modular polynomial — Cox equation (11.19). At the width-`m` cusp, `j` has order `−m` while the root indexed by a Cox matrix `σ` has order `−σ.a²`; for nonsquare `m` these never coincide, so every diagonal factor's leading coefficient is `1` or a signed power of `ζ_m`. All in `noncomputable section`, `namespace Cox`, `open UpperHalfPlane`.
**File-level note**: the copyright header block is duplicated (lines 1–10).

### `theorem j_widthM_cuspMeromorphicAt` (private)
- **Type**: `(m : ℕ+) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) j) 0`
- **What**: The cusp function of `j` in the width-`m` local parameter `q^(1/m)` is meromorphic at 0.
- **How**: Extracts the cusp-meromorphy component (`.2.2 1`) of `j_isGamma0ModularFunction m` (the proof that `j` is a Γ₀(m)-modular function) at the identity coset.
- **Hypotheses**: `m` a positive natural.
- **Uses from project**: [`cuspFunction`, `j`, `j_isGamma0ModularFunction`]
- **Used by**: `laurentqExpansion_j_order_widthM`, `laurentqExpansion_j_pow_widthM`
- **Visibility**: private
- **Lines**: 27–29, proof 1 line
- **Notes**: none

### `theorem laurentqExpansion_j_order_widthM`
- **Type**: `(m : ℕ+) : (laurentqExpansion ((m : ℕ) : ℝ) j).order = -(m : ℤ)`
- **What**: In the width-`m` local parameter `q^(1/m)`, the Laurent expansion of the `j`-function has order exactly `−m` (its simple pole at width 1 becomes an order-`m` pole after reparametrization).
- **How**: `j_poleOrder` (`poleOrder 1 j = 1`) rescales to pole order `m` at width `m` via `poleOrder_nat_mul`, and `laurentqExpansion.poleOrder_to_order` converts the analytic pole order into the Hahn-series order; `j_cuspFunction_meromorphicAt` and `j_periodic` supply the analytic hypotheses.
- **Hypotheses**: `m` a positive natural.
- **Uses from project**: [`laurentqExpansion`, `j`, `poleOrder`, `j_poleOrder`, `poleOrder_nat_mul`, `j_cuspFunction_meromorphicAt`, `j_periodic`, `laurentqExpansion.poleOrder_to_order`, `j_widthM_cuspMeromorphicAt`]
- **Used by**: `laurentqExpansion_j_leadingCoeff_widthM`, `cox_diagonal_factor_leadingCoeff`, `laurentqExpansion_j_pow_order_widthM`
- **Visibility**: public
- **Lines**: 32–40, proof ~8 lines
- **Notes**: none

### `theorem laurentqExpansion_j_leadingCoeff_widthM`
- **Type**: `(m : ℕ+) : (laurentqExpansion ((m : ℕ) : ℝ) j).leadingCoeff = 1`
- **What**: The leading (most negative order) Laurent coefficient of `j` remains 1 in the width-`m` local parameter, matching `j = q⁻¹ + 744 + …`.
- **How**: By `HahnSeries.leadingCoeff_eq` and the order computation `laurentqExpansion_j_order_widthM`, the leading coefficient is the coefficient at `−m`; the reindexing lemma `laurentqExpansion_nat_mul_coeff` identifies it with the width-1 coefficient at `−1`, which is `jIntCoeff (−1) = 1` by `jIntCoeff_spec` and `jIntCoeff_neg_one`.
- **Hypotheses**: `m` a positive natural.
- **Uses from project**: [`laurentqExpansion`, `j`, `laurentqExpansion_j_order_widthM`, `laurentqExpansion_nat_mul_coeff`, `j_cuspFunction_meromorphicAt`, `j_periodic`, `jIntCoeff_spec`, `jIntCoeff_neg_one`]
- **Used by**: `cox_diagonal_factor_leadingCoeff`, `laurentqExpansion_j_pow_leadingCoeff_widthM`
- **Visibility**: public
- **Lines**: 43–53, proof ~10 lines
- **Notes**: none

### `theorem transformedJSeries_coeff_order` (private)
- **Type**: `{K : Type*} [Field K] {m : ℕ+} (ζ : K) (σ : CoxMatrix m) : (transformedJSeries ζ σ).coeff (-((σ.a : ℤ) ^ 2)) = ζ ^ (-((σ.a : ℤ) * (σ.b : ℤ)))`
- **What**: The coefficient of the transformed `j`-series (the formal expansion of `j((aτ+b)/d)` with phase `ζ`) at the candidate leading exponent `−a²` equals the phase factor `ζ^(−ab)` from Cox (11.13).
- **How**: Evaluates the closed coefficient formula `transformedJSeries_coeff` at `k = −a²`: the divisibility/support condition is met with quotient `−1` (using `a > 0` from `σ.a_pos`), and the width-1 `j`-coefficient there is `jIntCoeff (−1) = 1`.
- **Hypotheses**: `K` a field; `σ` a Cox matrix of level `m` (upper-triangular `[[a,b],[0,d]]`, `ad = m`).
- **Uses from project**: [`transformedJSeries`, `transformedJSeries_coeff`, `CoxMatrix` (field `a_pos`), `jIntCoeff_neg_one`]
- **Used by**: `transformedJSeries_order`, `transformedJSeries_leadingCoeff`
- **Visibility**: private
- **Lines**: 55–61, proof ~6 lines
- **Notes**: none

### `theorem transformedJSeries_order`
- **Type**: `{K : Type*} [Field K] {m : ℕ+} (ζ : K) (hζ : ζ ≠ 0) (σ : CoxMatrix m) : (transformedJSeries ζ σ).order = -((σ.a : ℤ) ^ 2)`
- **What**: A transformed `j`-series with nonzero phase has Hahn-series order exactly `−a²`: the pole of `j∘σ` in the width-`m` parameter has order `a²`.
- **How**: The coefficient at `−a²` is `ζ^(−ab) ≠ 0` (`transformedJSeries_coeff_order`, `zpow_ne_zero`), while the coefficient formula `transformedJSeries_coeff` shows every nonzero coefficient sits at exponent ≥ `−a²`; `HahnSeries.orderTop_eq_of_le` then pins `orderTop`, converted to `order` by `HahnSeries.order_eq_orderTop_of_ne_zero`.
- **Hypotheses**: `ζ ≠ 0` in a field `K`; `σ` a Cox matrix of level `m`.
- **Uses from project**: [`transformedJSeries`, `transformedJSeries_coeff_order`, `transformedJSeries_coeff`, `CoxMatrix`]
- **Used by**: `transformedJSeries_leadingCoeff`, `cox_diagonal_factor_leadingCoeff`
- **Visibility**: public
- **Lines**: 64–83, proof ~19 lines
- **Notes**: none

### `theorem transformedJSeries_leadingCoeff`
- **Type**: `{K : Type*} [Field K] {m : ℕ+} (ζ : K) (hζ : ζ ≠ 0) (σ : CoxMatrix m) : (transformedJSeries ζ σ).leadingCoeff = ζ ^ (-((σ.a : ℤ) * (σ.b : ℤ)))`
- **What**: The leading coefficient of a transformed root series is exactly its phase `ζ^(−ab)` — the root-of-unity factor of Cox (11.13).
- **How**: Combines `HahnSeries.leadingCoeff_eq` with the order computation `transformedJSeries_order` and the coefficient value `transformedJSeries_coeff_order`.
- **Hypotheses**: `ζ ≠ 0` in a field `K`; `σ` a Cox matrix of level `m`.
- **Uses from project**: [`transformedJSeries`, `transformedJSeries_order`, `transformedJSeries_coeff_order`, `CoxMatrix`]
- **Used by**: `cox_diagonal_factor_leadingCoeff`
- **Visibility**: public
- **Lines**: 86–91, proof 2 lines
- **Notes**: none

### `theorem cox_diagonal_factor_leadingCoeff`
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) (σ : CoxMatrix m) : (laurentqExpansion ((m : ℕ) : ℝ) j - transformedJSeries (zeta m) σ).leadingCoeff = if σ.a ^ 2 < (m : ℕ) then 1 else -(zeta m ^ (-((σ.a : ℤ) * (σ.b : ℤ))))`
- **What**: The heart of Cox (11.19): each diagonal factor `j − (j∘σ)` of the diagonal Cox product has leading coefficient either `1` (when `j`'s pole `−m` is deeper) or `−ζ_m^(−ab)` (when the transformed pole `−a²` is deeper). Nonsquareness guarantees the orders `−m` and `−a²` never tie.
- **How**: Since `m` nonsquare gives `a² ≠ m`, exactly one of the two series has strictly smaller order; `HahnSeries.leadingCoeff_sub` (leading coefficient of a difference where one order dominates) picks out either `laurentqExpansion_j_leadingCoeff_widthM` (= 1) or, after rewriting `J − T = −(T − J)` and `HahnSeries.leadingCoeff_neg`, the negated phase `transformedJSeries_leadingCoeff`. Orders come from `laurentqExpansion_j_order_widthM` and `transformedJSeries_order`; `ζ_m ≠ 0` from `zeta_isPrimitiveRoot`.
- **Hypotheses**: `m` not a perfect square; `σ` a Cox matrix of level `m`.
- **Uses from project**: [`laurentqExpansion`, `j`, `transformedJSeries`, `zeta`, `zeta_isPrimitiveRoot`, `CoxMatrix`, `laurentqExpansion_j_leadingCoeff_widthM`, `transformedJSeries_leadingCoeff`, `laurentqExpansion_j_order_widthM`, `transformedJSeries_order`]
- **Used by**: `cox_diagonal_factor_leadingCoeff_pow`
- **Visibility**: public
- **Lines**: 95–141, proof ~46 lines
- **Notes**: proof >30 lines

### `theorem cox_diagonal_factor_leadingCoeff_pow`
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) (σ : CoxMatrix m) : (laurentqExpansion ((m : ℕ) : ℝ) j - transformedJSeries (zeta m) σ).leadingCoeff ^ (2 * (m : ℕ)) = 1`
- **What**: Each diagonal Cox factor's leading coefficient is a root of unity of exponent dividing `2m` (the `2` absorbs the sign, the `m` the power of `ζ_m`).
- **How**: Case split on `cox_diagonal_factor_leadingCoeff`: the value 1 is trivial; for `−ζ_m^(−ab)`, first `x^m = 1` for any ℤ-power `x` of `ζ_m` by `zeta_isPrimitiveRoot.zpow_eq_one`, then `(−x)^(2m) = ((−x)²)^m = (x²)^m = (x^m)² = 1` by exponent shuffling.
- **Hypotheses**: `m` not a perfect square; `σ` a Cox matrix of level `m`.
- **Uses from project**: [`laurentqExpansion`, `j`, `transformedJSeries`, `zeta`, `zeta_isPrimitiveRoot`, `cox_diagonal_factor_leadingCoeff`, `CoxMatrix`]
- **Used by**: `diagonal_cox_product_leadingCoeff_pow`
- **Visibility**: public
- **Lines**: 144–161, proof ~17 lines
- **Notes**: none

### `theorem laurentqExpansion_j_pow_widthM` (private)
- **Type**: `(m : ℕ+) (n : ℕ) : laurentqExpansion ((m : ℕ) : ℝ) (fun τ ↦ j τ ^ n) = (laurentqExpansion ((m : ℕ) : ℝ) j) ^ n`
- **What**: The width-`m` Laurent expansion is multiplicative on powers of `j`: expanding `j^n` gives the `n`-th power of the expansion of `j`.
- **How**: Specializes the general product rule `laurentqExpansion_finset_prod` to the constant family `fun _ ↦ j` over `Finset.range n`, with meromorphy supplied by `j_widthM_cuspMeromorphicAt`.
- **Hypotheses**: `m` a positive natural, `n` a natural exponent.
- **Uses from project**: [`laurentqExpansion`, `j`, `laurentqExpansion_finset_prod`, `j_widthM_cuspMeromorphicAt`]
- **Used by**: `laurentqExpansion_polynomialIn_j_widthM`
- **Visibility**: private
- **Lines**: 163–168, proof ~4 lines
- **Notes**: none

### `theorem polynomialIn_widthM_cuspMeromorphicAt` (private)
- **Type**: `(m : ℕ+) (P : Polynomial ℂ) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (polynomialIn P j)) 0`
- **What**: Any polynomial in `j` (as a function on ℍ) has width-`m` cusp function meromorphic at 0.
- **How**: `IsGamma0ModularFunction.polynomialIn` closes Γ₀(m)-modular functions under polynomial substitution, applied to `j_isGamma0ModularFunction m`; the meromorphy component is extracted at the identity coset.
- **Hypotheses**: `m` a positive natural, `P` a complex polynomial.
- **Uses from project**: [`cuspFunction`, `polynomialIn`, `j`, `j_isGamma0ModularFunction`, `IsGamma0ModularFunction.polynomialIn`]
- **Used by**: `laurentqExpansion_polynomialIn_j_widthM`
- **Visibility**: private
- **Lines**: 170–172, proof 1 line
- **Notes**: none

### `theorem laurentqExpansion_polynomialIn_j_widthM`
- **Type**: `(m : ℕ+) (P : Polynomial ℂ) : laurentqExpansion ((m : ℕ) : ℝ) (polynomialIn P j) = P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion ((m : ℕ) : ℝ) j)`
- **What**: The width-`m` Laurent expansion is a ring-homomorphism-like operation on polynomials in `j`: expanding `P(j)` equals substituting the expansion of `j` into `P` with constants embedded via `HahnSeries.C`.
- **How**: Induction on `P` by `Polynomial.induction_on'`: the additive case uses the linearity rule `laurentqExpansion_add` (with meromorphy from `polynomialIn_widthM_cuspMeromorphicAt`); the monomial case `a·j^n` splits the constant with `laurentqExpansion_mul` and `meromorphicAt_cuspFunction_const`, then applies the power rule `laurentqExpansion_j_pow_widthM`.
- **Hypotheses**: `m` a positive natural, `P` a complex polynomial.
- **Uses from project**: [`laurentqExpansion`, `polynomialIn`, `j`, `laurentqExpansion_add`, `laurentqExpansion_mul`, `meromorphicAt_cuspFunction_const`, `polynomialIn_widthM_cuspMeromorphicAt`, `laurentqExpansion_j_pow_widthM`, `j_isGamma0ModularFunction`, `IsGamma0ModularFunction.polynomialIn`]
- **Used by**: `formalCoxPolynomial_eq_modularPolynomialC_map_j`
- **Visibility**: public
- **Lines**: 175–215, proof ~40 lines
- **Notes**: proof >30 lines

### `theorem formalCoxPolynomial_eq_modularPolynomialC_map_j`
- **Type**: `(m : ℕ+) : formalCoxPolynomial m (zeta m) = Polynomial.map (Polynomial.eval₂RingHom (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion ((m : ℕ) : ℝ) j)) (modularPolynomialC m)`
- **What**: The formal Cox polynomial (the product `∏_σ (X − transformedJSeries ζ_m σ)` over Laurent series) is obtained from `Φ_m` by substituting the width-`m` Laurent series of `j` into the coefficient variable `Y` — connecting the formal `q`-expansion world to the polynomial `Φ_m`.
- **How**: Coefficientwise (`Polynomial.ext`): each coefficient of the formal product is the width-`m` Laurent expansion of the corresponding `coxPhiFunction` coefficient (`coxPhiFunction_coeff_laurentqExpansion_widthM`), which is a polynomial in `j` matching the coefficient of `Φ_m` (`modularPolynomialC_coeff_polynomialIn`); the substitution identity `laurentqExpansion_polynomialIn_j_widthM` finishes.
- **Hypotheses**: `m` a positive natural.
- **Uses from project**: [`formalCoxPolynomial`, `zeta`, `modularPolynomialC`, `laurentqExpansion`, `j`, `coxPhiFunction_coeff_laurentqExpansion_widthM`, `modularPolynomialC_coeff_polynomialIn`, `laurentqExpansion_polynomialIn_j_widthM`]
- **Used by**: `modularPolynomialC_diagonal_series`
- **Visibility**: public
- **Lines**: 219–229, proof ~10 lines
- **Notes**: none

### `theorem modularPolynomialC_diagonal_series`
- **Type**: `(m : ℕ+) : (BivariatePolynomial.diagonal (modularPolynomialC m)).eval₂ (HahnSeries.C) (laurentqExpansion ((m : ℕ) : ℝ) j) = ∏ σ : CoxMatrix m, (laurentqExpansion ((m : ℕ) : ℝ) j - transformedJSeries (zeta m) σ)`
- **What**: Substituting the width-`m` Laurent series of `j` into the diagonal `Φ_m(X,X)` yields exactly the product of the diagonal Cox factors `∏_σ (j − j∘σ)` as Laurent series — the series form of Cox's diagonal factorization.
- **How**: `BivariatePolynomial.diagonal_eval₂` commutes the diagonal with `eval₂`; rewriting through `formalCoxPolynomial_eq_modularPolynomialC_map_j` turns the substituted `Φ_m` into `formalCoxPolynomial`, whose definition as `∏ (X − transformedJSeries)` evaluates by `Polynomial.eval_prod`.
- **Hypotheses**: `m` a positive natural.
- **Uses from project**: [`BivariatePolynomial.diagonal`, `BivariatePolynomial.diagonal_eval₂`, `modularPolynomialC`, `laurentqExpansion`, `j`, `formalCoxPolynomial`, `formalCoxPolynomial_eq_modularPolynomialC_map_j`, `transformedJSeries`, `zeta`, `CoxMatrix`]
- **Used by**: `modularPolynomialC_diagonal_leadingCoeff_pow`
- **Visibility**: public
- **Lines**: 233–242, proof ~9 lines
- **Notes**: none

### `theorem laurentqExpansion_j_pow_order_widthM` (private)
- **Type**: `(m : ℕ+) (n : ℕ) : ((laurentqExpansion ((m : ℕ) : ℝ) j) ^ n).order = -((m : ℤ) * (n : ℤ))`
- **What**: The `n`-th power of the width-`m` expansion of `j` has order `−mn` (orders add under multiplication in an integral domain of Hahn series).
- **How**: `HahnSeries.order_pow` (order of a power is `n` times the order) combined with `laurentqExpansion_j_order_widthM`.
- **Hypotheses**: `m` a positive natural, `n` a natural.
- **Uses from project**: [`laurentqExpansion`, `j`, `laurentqExpansion_j_order_widthM`]
- **Used by**: `eval₂_laurentqExpansion_j_coeff_widthM`, `eval₂_laurentqExpansion_j_coeff_eq_zero_of_lt_widthM`
- **Visibility**: private
- **Lines**: 244–248, proof 2 lines
- **Notes**: none

### `theorem laurentqExpansion_j_pow_leadingCoeff_widthM` (private)
- **Type**: `(m : ℕ+) (n : ℕ) : ((laurentqExpansion ((m : ℕ) : ℝ) j) ^ n).leadingCoeff = 1`
- **What**: Powers of the width-`m` expansion of `j` all have leading coefficient 1 (leading coefficients are multiplicative and `j`'s is 1).
- **How**: Induction on `n` using `HahnSeries.leadingCoeff_mul` and `laurentqExpansion_j_leadingCoeff_widthM`; base case by `HahnSeries.leadingCoeff_one`.
- **Hypotheses**: `m` a positive natural, `n` a natural.
- **Uses from project**: [`laurentqExpansion`, `j`, `laurentqExpansion_j_leadingCoeff_widthM`]
- **Used by**: `eval₂_laurentqExpansion_j_coeff_widthM`
- **Visibility**: private
- **Lines**: 250–256, proof ~6 lines
- **Notes**: none

### `theorem eval₂_laurentqExpansion_j_coeff_widthM` (private)
- **Type**: `(m : ℕ+) (P : Polynomial ℂ) : (P.eval₂ (HahnSeries.C) (laurentqExpansion ((m : ℕ) : ℝ) j)).coeff (-((m : ℤ) * (P.natDegree : ℤ))) = P.leadingCoeff`
- **What**: When a complex polynomial `P` is evaluated at the width-`m` expansion of `j`, the coefficient at the extremal exponent `−m·deg P` equals `P`'s leading coefficient: only the top term of `P` can reach that depth.
- **How**: Expands `eval₂` as a finite sum (`Polynomial.eval₂_eq_sum_range`, `HahnSeries.coeff_sum`) and isolates the `i = deg P` term with `Finset.sum_eq_single`: for `i < deg P` the term's order `−mi` exceeds `−m·deg P` so its coefficient vanishes (`laurentqExpansion_j_pow_order_widthM`, `HahnSeries.coeff_eq_zero_of_lt_order`); the top term contributes `leadingCoeff · 1` by `laurentqExpansion_j_pow_leadingCoeff_widthM`.
- **Hypotheses**: `m` a positive natural, `P` a complex polynomial.
- **Uses from project**: [`laurentqExpansion`, `j`, `laurentqExpansion_j_pow_order_widthM`, `laurentqExpansion_j_pow_leadingCoeff_widthM`]
- **Used by**: `eval₂_laurentqExpansion_j_leadingCoeff_widthM`
- **Visibility**: private
- **Lines**: 258–294, proof ~36 lines
- **Notes**: proof >30 lines

### `theorem eval₂_laurentqExpansion_j_coeff_eq_zero_of_lt_widthM` (private)
- **Type**: `(m : ℕ+) (P : Polynomial ℂ) (k : ℤ) (hk : k < -((m : ℤ) * (P.natDegree : ℤ))) : (P.eval₂ (HahnSeries.C) (laurentqExpansion ((m : ℕ) : ℝ) j)).coeff k = 0`
- **What**: Below the extremal exponent `−m·deg P`, every coefficient of `P` evaluated at the expansion of `j` vanishes — the substituted series has no deeper pole.
- **How**: Same sum expansion as the previous lemma, but every summand dies: each term `C(P.coeff n)·J^n` has order `−mn ≥ −m·deg P > k` by `laurentqExpansion_j_pow_order_widthM`, so `HahnSeries.coeff_eq_zero_of_lt_order` kills it termwise via `Finset.sum_eq_zero`.
- **Hypotheses**: `k < −m·deg P`.
- **Uses from project**: [`laurentqExpansion`, `j`, `laurentqExpansion_j_pow_order_widthM`]
- **Used by**: `eval₂_laurentqExpansion_j_leadingCoeff_widthM`
- **Visibility**: private
- **Lines**: 296–312, proof ~16 lines
- **Notes**: none

### `theorem eval₂_laurentqExpansion_j_leadingCoeff_widthM` (private)
- **Type**: `(m : ℕ+) (P : Polynomial ℂ) : (P.eval₂ (HahnSeries.C) (laurentqExpansion ((m : ℕ) : ℝ) j)).leadingCoeff = P.leadingCoeff`
- **What**: Substituting the width-`m` expansion of `j` into a polynomial preserves the leading coefficient: the leading coefficient of `P(J)` as a Laurent series equals `P`'s leading coefficient.
- **How**: For `P ≠ 0`, the coefficient at `k = −m·deg P` is nonzero and equals `P.leadingCoeff` (`eval₂_laurentqExpansion_j_coeff_widthM`), and everything below vanishes (`eval₂_laurentqExpansion_j_coeff_eq_zero_of_lt_widthM`), so `HahnSeries.orderTop_eq_of_le` pins the order at `k` and the leading coefficient reads off there.
- **Hypotheses**: `m` a positive natural, `P` a complex polynomial (case `P = 0` handled trivially).
- **Uses from project**: [`laurentqExpansion`, `j`, `eval₂_laurentqExpansion_j_coeff_widthM`, `eval₂_laurentqExpansion_j_coeff_eq_zero_of_lt_widthM`]
- **Used by**: `modularPolynomialC_diagonal_leadingCoeff_pow`
- **Visibility**: private
- **Lines**: 314–339, proof ~25 lines
- **Notes**: none

### `theorem diagonal_cox_product_leadingCoeff_pow` (private)
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) : (∏ σ : CoxMatrix m, (laurentqExpansion ((m : ℕ) : ℝ) j - transformedJSeries (zeta m) σ)).leadingCoeff ^ (2 * (m : ℕ)) = 1`
- **What**: The leading coefficient of the full diagonal Cox product `∏_σ (j − j∘σ)` has `2m`-th power 1, since each factor does and leading coefficients are multiplicative.
- **How**: Strengthens to arbitrary finite subsets and inducts with `Finset.induction_on`: the insert step distributes the power over `HahnSeries.leadingCoeff_mul` and discharges the new factor with `cox_diagonal_factor_leadingCoeff_pow`; base case via `HahnSeries.leadingCoeff_one`.
- **Hypotheses**: `m` not a perfect square.
- **Uses from project**: [`laurentqExpansion`, `j`, `transformedJSeries`, `zeta`, `CoxMatrix`, `cox_diagonal_factor_leadingCoeff_pow`]
- **Used by**: `modularPolynomialC_diagonal_leadingCoeff_pow`
- **Visibility**: private
- **Lines**: 341–357, proof ~16 lines
- **Notes**: uses `classical`

### `theorem modularPolynomialC_diagonal_leadingCoeff_pow`
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) : (BivariatePolynomial.diagonal (modularPolynomialC m)).leadingCoeff ^ (2 * (m : ℕ)) = 1`
- **What**: Cox equation (11.19), complex form: for nonsquare `m` the leading coefficient of the diagonal `Φ_m(X,X) ∈ ℂ[X]` is a root of unity of exponent `2m`. This is the file's exported result, consumed in `Arithmetic.lean` to prove Theorem 11.18(iv).
- **How**: The substitution `X ↦ J` (width-`m` expansion of `j`) preserves the leading coefficient (`eval₂_laurentqExpansion_j_leadingCoeff_widthM`), identifies the substituted diagonal with the Cox product (`modularPolynomialC_diagonal_series`), and the product's leading coefficient has `2m`-th power 1 (`diagonal_cox_product_leadingCoeff_pow`).
- **Hypotheses**: `m` not a perfect square.
- **Uses from project**: [`BivariatePolynomial.diagonal`, `modularPolynomialC`, `eval₂_laurentqExpansion_j_leadingCoeff_widthM`, `modularPolynomialC_diagonal_series`, `diagonal_cox_product_leadingCoeff_pow`]
- **Used by**: unused in file (consumed by `Arithmetic.lean`: `modularPolynomialDiagonal_leadingCoeff_pow_two_mul`)
- **Visibility**: public
- **Lines**: 361–368, proof ~7 lines
- **Notes**: none

### File Summary
- Total declarations: 20 (0 defs, 20 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): [`laurentqExpansion_j_order_widthM` (3: `laurentqExpansion_j_leadingCoeff_widthM`, `cox_diagonal_factor_leadingCoeff`, `laurentqExpansion_j_pow_order_widthM`)]
- Unused declarations (not used by anything in this file): [`modularPolynomialC_diagonal_leadingCoeff_pow`] — the file's exported end result, used by `Arithmetic.lean`
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [`cox_diagonal_factor_leadingCoeff` (~46), `laurentqExpansion_polynomialIn_j_widthM` (~40), `eval₂_laurentqExpansion_j_coeff_widthM` (~36)]
- File-level note: the copyright header block is duplicated (lines 1–10) — style cleanup candidate.
