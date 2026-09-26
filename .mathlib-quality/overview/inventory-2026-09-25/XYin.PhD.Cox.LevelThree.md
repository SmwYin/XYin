# Inventory: XYin/PhD/Cox/LevelThree.lean  (858 lines)

Proves Cox's explicit level-three modular polynomial (equation (11.22)) from the single hypothesis
that the complex `Φ₃` is symmetric under `X ↔ Y`. Analytic input: `Φ₃ᶜ(T, J) = 0` where
`T = transformedJSeries ζ₃ σ₀` (the series of `j(3τ)` in `t = q^{1/3}`, order `−9`) and
`J = laurentqExpansion 3 j` (order `−3`). The difference `D = Φ₃ᶜ − Eᶜ` (`E` = explicit candidate)
is symmetric of bidegree `≤ (3,3)`, and `D(T,J) = −E(T,J)` has ten "triangular" Laurent
coefficients (`t^0, t^{-9}, …, t^{-36}`) equal to zero, which forces `D = 0` by
`symmetric_bidegree_three_eq_zero_of_laurent_coeff`. The ten coefficients are certified over `ℤ`
by `decide +kernel` on a hand-rolled "jet" (`ℕ → ℤ` truncated power series) model of the integral
`q`-expansion of `q·j` and its 3- and 9-fold expansions. Verified by `#print axioms` (scratch run):
the public theorem depends only on `propext, Classical.choice, Quot.sound` — no `Lean.ofReduceBool`.

## Declarations

### `def Cox.modularPolynomialThreeExplicit`
- **Type**: `BivariatePolynomial ℤ`
- **What**: Cox's explicit `Φ₃(X,Y)` (eq. 11.22): `X(X+2¹⁵·3·5³)³ + Y(Y+2¹⁵·3·5³)³ − X³Y³ + 2³·3²·31·X²Y²(X+Y) − 2²·3³·9907·XY(X²+Y²) + 2·3⁴·13·193·6367·X²Y² + 2¹⁶·3⁵·5³·17·263·XY(X+Y) − 2³¹·5⁶·22973·XY`.
- **How**: Literal polynomial expression in `BivariatePolynomial.varX`/`varY` with `let` bindings.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial`, `BivariatePolynomial.varX`, `BivariatePolynomial.varY`]
- **Used by**: `modularPolynomialThreeExplicit_eq_table`, `_monic`, `_natDegree`, `_swap`, `explicitCandidateLaurentEvalThree`, `explicitCandidateLaurentEvalComplexThree`, `modularPolynomialThreeComplexExplicit`, `modularPolynomial_three_of_complex_swap`
- **Visibility**: public
- **Lines**: 29–40, body ≈ 10 lines
- **Notes**: One of only two public declarations. Not referenced by any other XYin file except `Arithmetic.lean` (`modularPolynomial_three`).

### `def Cox.qjCoeffTableThree` (private)
- **Type**: `ℕ → ℤ`
- **What**: The first 13 coefficients `c(−1..11)` of `q·j = 1 + 744q + 196884q² + …` as a literal list, `0` beyond index 12.
- **How**: `List.getD` on a 13-element literal.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `qjCoeffInt_eq_tableThree`, `sigmaJetThree`, `widthJetThree`, `qjIntegralPowerSeriesThree_coeff_eq_table`
- **Visibility**: private
- **Lines**: 42–45, body ≈ 3
- **Notes**: Duplicates the values that `qjCoeffInt` (qExpansion_tactic/Qj.lean:141, array pipeline) computes; reconciled at L47.

### `theorem Cox.qjCoeffInt_eq_tableThree` (private)
- **Type**: `(n : Fin 13) → qjCoeffInt n = qjCoeffTableThree n`
- **What**: The tactic's computed `q·j` coefficients agree with the literal table for `n < 13`.
- **How**: `fin_cases n <;> decide +kernel` — kernel evaluation of the `Array`-based `qjCoeffsArrayUpTo` pipeline.
- **Hypotheses**: `n < 13`.
- **Uses from project**: [`qjCoeffInt`, `qjCoeffTableThree`]
- **Used by**: `qjIntegralPowerSeriesThree_coeff_eq_table`
- **Visibility**: private
- **Lines**: 47–49, body ≈ 1
- **Notes**: `decide +kernel` (13 cases). This is the sole bridge between the native-oriented `Qj.lean` arrays and this file's kernel-only policy.

### `def Cox.explicitCoeffThree` (private)
- **Type**: `Fin 5 → ℕ → ℤ`
- **What**: The 5×5 coefficient matrix `[X^i Y^d] Φ₃` of the explicit polynomial (e.g. `(0,1) = 1855425871872000000000`, `(3,3) = −1`, `(4,0) = 1`).
- **How**: `match` on `i` returning `List.getD` of literal rows.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `modularPolynomialThreeTable`, `modularPolynomialThreeExplicit_eq_table`, `explicitCandidateClearedJetTermThree`, `explicitCandidateClearedLaurentTermThree`, `explicitCandidateClearedPowerSeriesThree`, `explicitCandidateClearedJetTermThree_eighteen_three_three`
- **Visibility**: private
- **Lines**: 51–59, body ≈ 8
- **Notes**: Second encoding of the same data as `modularPolynomialThreeExplicit`; exists so the kernel can read coefficients.

### `def Cox.modularPolynomialThreeTable` (private)
- **Type**: `BivariatePolynomial ℤ`
- **What**: `∑_{i,d<5} explicitCoeffThree i d · X^i Y^d`.
- **How**: Double `Finset.sum` over `Fin 5`.
- **Hypotheses**: none.
- **Uses from project**: [`explicitCoeffThree`, `BivariatePolynomial.varX`, `BivariatePolynomial.varY`]
- **Used by**: `modularPolynomialThreeExplicit_eq_table`, `explicitCandidateClearedLaurentEvalThree`
- **Visibility**: private
- **Lines**: 61–64, body ≈ 3

### `theorem Cox.modularPolynomialThreeExplicit_eq_table` (private)
- **Type**: `modularPolynomialThreeExplicit = modularPolynomialThreeTable`
- **What**: The closed-form and the tabulated `Φ₃` coincide.
- **How**: Unfold both, expand `Fin.sum_univ_succ`/`List.getD_cons_*`, then `ring_nf`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialThreeExplicit`, `modularPolynomialThreeTable`, `explicitCoeffThree`, `BivariatePolynomial.varX`, `BivariatePolynomial.varY`]
- **Used by**: `explicitCandidateClearedLaurentEvalThree`
- **Visibility**: private
- **Lines**: 66–72, body ≈ 5

### `theorem Cox.modularPolynomialThreeExplicit_monic` (private)
- **Type**: `modularPolynomialThreeExplicit.Monic`
- **What**: `Φ₃` is monic in `X` (leading term `X⁴`).
- **How**: `ring_nf` then `monicity!`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialThreeExplicit`, `BivariatePolynomial.varX`, `BivariatePolynomial.varY`]
- **Used by**: `modularPolynomialThreeComplexExplicit_monic`, `modularPolynomialThreeComplexExplicit_natDegree`
- **Visibility**: private
- **Lines**: 74–78, body ≈ 3

### `theorem Cox.modularPolynomialThreeExplicit_natDegree` (private)
- **Type**: `modularPolynomialThreeExplicit.natDegree = 4`
- **What**: Degree 4 in `X`.
- **How**: `ring_nf` then `compute_degree!`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialThreeExplicit`, `BivariatePolynomial.varX`, `BivariatePolynomial.varY`]
- **Used by**: `modularPolynomialThreeComplexExplicit_natDegree`
- **Visibility**: private
- **Lines**: 80–84, body ≈ 3

### `theorem Cox.modularPolynomialThreeExplicit_swap` (private)
- **Type**: `Polynomial.Bivariate.swap modularPolynomialThreeExplicit = modularPolynomialThreeExplicit`
- **What**: The explicit `Φ₃` is symmetric in `X, Y`.
- **How**: Push `swap` (a ring hom) through the expression with `map_add/map_mul/…`, `Polynomial.Bivariate.swap_X/swap_Y`, then `ring`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialThreeExplicit`, `BivariatePolynomial.varX`, `BivariatePolynomial.varY`]
- **Used by**: `modularPolynomialThreeComplexExplicit_swap`
- **Visibility**: private
- **Lines**: 86–92, body ≈ 4

### `def Cox.jetMul` (private)
- **Type**: `(ℕ → ℤ) → (ℕ → ℤ) → ℕ → ℤ`
- **What**: Cauchy product of coefficient sequences: `(F*G)(n) = ∑_{i≤n} F i · G (n−i)`.
- **How**: `Finset.sum` over `Finset.range (n+1)`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `jetPow`, `explicitCandidateClearedJetTermThree`, `powerSeries_coeff_mul_eq_jetMul`, `explicitCandidateClearedJetTermThree_eighteen_three_three`
- **Visibility**: private
- **Lines**: 94–95, body ≈ 1
- **Notes**: Computable mirror of `PowerSeries.coeff_mul` (mathlib RingTheory/PowerSeries/Basic.lean:243); also duplicates `convArrayUpTo` in qExpansion_tactic/Qj.lean (array convolution).

### `def Cox.jetPow` (private)
- **Type**: `(ℕ → ℤ) → ℕ → ℕ → ℤ`
- **What**: `d`-th Cauchy power of a coefficient sequence, `F^0 = δ₀`, `F^{d+1} = F^d * F`.
- **How**: Structural recursion on `d` via `jetMul`.
- **Hypotheses**: none.
- **Uses from project**: [`jetMul`]
- **Used by**: `explicitCandidateClearedJetTermThree`, `powerSeries_coeff_pow_eq_jetPow`, `explicitCandidateThreeThreeCore_left_lower`, `_left_upper`, `_left`, `_right`
- **Visibility**: private
- **Lines**: 97–99, body ≈ 2

### `def Cox.jetShift` (private)
- **Type**: `ℕ → (ℕ → ℤ) → ℕ → ℤ`
- **What**: Multiplication by `q^k` on coefficients: `(q^k F)(n) = F (n−k)` if `k ≤ n`, else `0`.
- **How**: `if k ≤ n then F (n - k) else 0`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `explicitCandidateClearedJetTermThree`, `powerSeries_coeff_shift_eq_jetShift`, `explicitCandidateClearedJetTermThree_eighteen_three_three`
- **Visibility**: private
- **Lines**: 101–102, body ≈ 1
- **Notes**: Mirror of `PowerSeries.coeff_X_pow_mul'` (RingTheory/PowerSeries/Basic.lean:405).

### `def Cox.jetExpand` (private)
- **Type**: `ℕ → (ℕ → ℤ) → ℕ → ℤ`
- **What**: Coefficients of `F(q^k)`: `F(n/k)` if `k ∣ n`, else `0`.
- **How**: `if k ∣ n then F (n / k) else 0`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `sigmaJetThree`, `widthJetThree`, `sigmaPowerSeriesThree_coeff_eq_jet`, `widthPowerSeriesThree_coeff_eq_jet`
- **Visibility**: private
- **Lines**: 104–105, body ≈ 1
- **Notes**: Mirror of `PowerSeries.coeff_expand` (RingTheory/PowerSeries/Expand.lean:110; also `coeff_expand_mul`:87, `coeff_expand_of_not_dvd`:97).

### `def Cox.sigmaJetThree` (private)
- **Type**: `ℕ → ℤ`
- **What**: Jet of `(q·j)(t⁹)`, i.e. the integral series of `t⁹·j(3τ)` in `t = q^{1/3}`.
- **How**: `jetExpand 9 qjCoeffTableThree`.
- **Hypotheses**: none.
- **Uses from project**: [`jetExpand`, `qjCoeffTableThree`]
- **Used by**: `explicitCandidateClearedJetTermThree`, `sigmaPowerSeriesThree_coeff_eq_jet`, `explicitCandidateThreeThreeCore_*` (4)
- **Visibility**: private
- **Lines**: 107

### `def Cox.widthJetThree` (private)
- **Type**: `ℕ → ℤ`
- **What**: Jet of `(q·j)(t³)`, i.e. `t³·j(τ)` in `t = q^{1/3}`.
- **How**: `jetExpand 3 qjCoeffTableThree`.
- **Hypotheses**: none.
- **Uses from project**: [`jetExpand`, `qjCoeffTableThree`]
- **Used by**: `explicitCandidateClearedJetTermThree`, `widthPowerSeriesThree_coeff_eq_jet`, `explicitCandidateThreeThreeCore_*` (4)
- **Visibility**: private
- **Lines**: 109

### `def Cox.explicitCandidateClearedJetTermThree` (private)
- **Type**: `Fin 5 → Fin 5 → ℕ → ℤ`
- **What**: Jet of the `(i,d)` monomial of `t³⁶·Φ₃(T,J)`: `c_{id} · t^{36−9i−3d} · (t⁹T)^i (t³J)^d`.
- **How**: `explicitCoeffThree i d * jetShift (36 − (9i+3d)) (jetMul (jetPow σ i) (jetPow w d))`.
- **Hypotheses**: none (note `36 − (9i+3d)` is truncated `ℕ`-subtraction, harmless since `9i+3d ≤ 36+…`; for `i=d=4` it is `36−48 ↦ 0` but `c_{44}=0`).
- **Uses from project**: [`explicitCoeffThree`, `jetShift`, `jetMul`, `jetPow`, `sigmaJetThree`, `widthJetThree`]
- **Used by**: `explicitCandidateClearedJetRowThree`, `explicitCandidateClearedPowerSeriesThree_coeff_eq_jet`, and the 12 `…TermThree_eighteen_*` facts
- **Visibility**: private
- **Lines**: 111–114, body ≈ 3

### `def Cox.explicitCandidateClearedJetRowThree` (private)
- **Type**: `Fin 5 → ℕ → ℤ`
- **What**: Row sum over `d` of the term jets.
- **How**: `∑ d : Fin 5, …TermThree i d n`.
- **Hypotheses**: none.
- **Uses from project**: [`explicitCandidateClearedJetTermThree`]
- **Used by**: `explicitCandidateClearedJetThree`, `explicitCandidateClearedPowerSeriesThree_coeff_eq_jet`, the 11 `…RowThree_*` facts
- **Visibility**: private
- **Lines**: 116–117

### `def Cox.explicitCandidateClearedJetThree` (private)
- **Type**: `ℕ → ℤ`
- **What**: The full jet of `t³⁶·Φ₃(T,J)` (sum over `i`).
- **How**: `∑ i : Fin 5, …RowThree i n`.
- **Hypotheses**: none.
- **Uses from project**: [`explicitCandidateClearedJetRowThree`]
- **Used by**: `explicitCandidateClearedPowerSeriesThree_coeff_eq_jet`, `explicitCandidateLaurentEvalThree_coeff_eq_jet`, the 10 `…JetThree_<n>` facts
- **Visibility**: private
- **Lines**: 119–120

### `theorem Cox.jIntCoeff_eq_qjCoeffInt_three` (private)
- **Type**: `(n : ℕ) → jIntCoeff ((n : ℤ) − 1) = qjCoeffInt n`
- **What**: The abstract integral Laurent coefficient of `j` at `n−1` equals the tactic's computed coefficient of `q·j` at `n`.
- **How**: Inject into `ℂ` via `jIntCoeff_spec`, pass from the Laurent to the `q`-expansion with `laurentqExpansion.coeff_of_geq` and `j_poleOrder`, then `j_to_qExpansion`, `qj_qexpansion`, `qj_qxp_coeff_link`.
- **Hypotheses**: none.
- **Uses from project**: [`jIntCoeff`, `jIntCoeff_spec`, `qjCoeffInt`, `poleOrder`, `j_poleOrder`, `laurentqExpansion.coeff_of_geq`, `j_to_qExpansion`, `qj_qexpansion`, `qj_qxp_coeff_link`, `j`]
- **Used by**: `qjIntegralPowerSeriesThree_coeff_eq_table`
- **Visibility**: private
- **Lines**: 122–130, body ≈ 7
- **Notes**: Not level-3 specific (the `_three` suffix is misleading); belongs next to `jIntCoeff_spec` in CoxMatrices/LaurentExpansion.lean or Kronecker.lean.

### `def Cox.qjIntegralPowerSeriesThree` (private)
- **Type**: `PowerSeries ℤ`
- **What**: `∑ jIntCoeff(n−1) qⁿ`, the integral power series of `q·j`.
- **How**: `PowerSeries.mk`.
- **Hypotheses**: none.
- **Uses from project**: [`jIntCoeff`]
- **Used by**: `sigmaPowerSeriesThree`, `widthPowerSeriesThree`, `qjIntegralPowerSeriesThree_coeff_eq_table`, `widthLaurentSeriesThree_eq_integral`, `sigmaLaurentSeriesThree_map_complex`
- **Visibility**: private
- **Lines**: 132–133
- **Notes**: Level-independent; morally equals `qj_qexpansion` (Qj.lean:148) under `jIntCoeff_eq_qjCoeffInt_three`.

### `def Cox.sigmaPowerSeriesThree` (private)
- **Type**: `PowerSeries ℤ`
- **What**: `(q·j)(t⁹)` as a power series in `t`.
- **How**: `PowerSeries.expand 9`.
- **Hypotheses**: none.
- **Uses from project**: [`qjIntegralPowerSeriesThree`]
- **Used by**: `sigmaLaurentSeriesThree`, `explicitCandidateClearedLaurentTermThree`, `sigmaPowerSeriesThree_coeff_eq_jet`, `explicitCandidateClearedPowerSeriesThree`, `sigmaLaurentSeriesThree_map_complex`
- **Visibility**: private
- **Lines**: 135–136

### `def Cox.widthPowerSeriesThree` (private)
- **Type**: `PowerSeries ℤ`
- **What**: `(q·j)(t³)` as a power series in `t`.
- **How**: `PowerSeries.expand 3`.
- **Hypotheses**: none.
- **Uses from project**: [`qjIntegralPowerSeriesThree`]
- **Used by**: `widthLaurentSeriesThree`, `explicitCandidateClearedLaurentTermThree`, `widthPowerSeriesThree_coeff_eq_jet`, `explicitCandidateClearedPowerSeriesThree`, `widthLaurentSeriesThree_eq_integral`
- **Visibility**: private
- **Lines**: 138–139

### `def Cox.sigmaLaurentSeriesThree` (private)
- **Type**: `LaurentSeries ℤ`
- **What**: `t⁻⁹·(q·j)(t⁹)`, the integral Laurent series of `j(3τ)` in `t`.
- **How**: `HahnSeries.single (−9) 1 * ↑sigmaPowerSeriesThree`.
- **Hypotheses**: none.
- **Uses from project**: [`sigmaPowerSeriesThree`]
- **Used by**: `explicitCandidateClearedLaurentTermThree`, `bivariateLaurentEval_intCastThree`, `explicitCandidateLaurentEvalThree`, `sigmaLaurentSeriesThree_map_complex`
- **Visibility**: private
- **Lines**: 141–142
- **Notes**: Equals `jIntegralLaurentSeriesWidth 9` (Kronecker.lean:184) coefficientwise — not stated; see Observations.

### `def Cox.widthLaurentSeriesThree` (private)
- **Type**: `LaurentSeries ℤ`
- **What**: `t⁻³·(q·j)(t³)`, the integral Laurent series of `j(τ)` in `t`.
- **How**: `HahnSeries.single (−3) 1 * ↑widthPowerSeriesThree`.
- **Hypotheses**: none.
- **Uses from project**: [`widthPowerSeriesThree`]
- **Used by**: `explicitCandidateClearedLaurentTermThree`, `bivariateLaurentEval_intCastThree`, `explicitCandidateLaurentEvalThree`, `widthLaurentSeriesThree_eq_integral`, `widthLaurentSeriesThree_map_complex`
- **Visibility**: private
- **Lines**: 144–145

### `theorem Cox.shiftedPowerSeries_pow` (private)
- **Type**: `(a : ℤ) (F : PowerSeries ℤ) (n : ℕ) → (single a 1 * ↑F)^n = single (n • a) 1 * ↑(F^n)`
- **What**: Powers of a shifted power series are shifted powers.
- **How**: `mul_pow`, `HahnSeries.single_pow` (RingTheory/HahnSeries/Multiplication.lean:795), `map_pow`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `explicitCandidateClearedLaurentTermThree`
- **Visibility**: private
- **Lines**: 147–152, body ≈ 3
- **Notes**: General (any `R`); 3-line mathlib wrapper.

### `theorem Cox.shiftedPowerSeries_mul` (private)
- **Type**: `(a b r s : ℤ) (F G) → (single a r * ↑F) * (single b s * ↑G) = single (a+b) (r*s) * ↑(F*G)`
- **What**: Product of two shifted power series.
- **How**: `ac_rfl` regrouping, `HahnSeries.single_mul_single` (Multiplication.lean:776), `ofPowerSeries` is a ring hom.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `clearTwoShiftedPowerSeries`
- **Visibility**: private
- **Lines**: 154–166, body ≈ 7
- **Notes**: General; belongs with `laurentSeriesMapRingHom` helpers in LaurentPolynomialEvaluation.lean.

### `theorem Cox.clearTwoShiftedPowerSeries` (private)
- **Type**: `(c a b : ℤ) (F G) → single 36 1 * (C c * (single a 1 * ↑F) * (single b 1 * ↑G)) = single (36+a+b) c * ↑(F*G)`
- **What**: Clearing denominators: multiplying a scaled product of two shifted series by `t³⁶` gives a single shifted series.
- **How**: Four-step `calc` applying `shiftedPowerSeries_mul` twice and `HahnSeries.single_mul_single`.
- **Hypotheses**: none.
- **Uses from project**: [`shiftedPowerSeries_mul`]
- **Used by**: `explicitCandidateClearedLaurentTermThree`
- **Visibility**: private
- **Lines**: 168–192, body ≈ 18
- **Notes**: Hard-codes `36`; would be 2 lines from `shiftedPowerSeries_mul` if stated with a general exponent.

### `theorem Cox.C_mul_single_one` (private)
- **Type**: `(c k : ℤ) → HahnSeries.C c * single k 1 = single k c`
- **What**: A constant times a monomial is a scaled monomial.
- **How**: `HahnSeries.C_apply`, `single_mul_single`, `simp`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `explicitCandidateClearedLaurentTermThree`
- **Visibility**: private
- **Lines**: 194–198, body ≈ 2
- **Notes**: One-line mathlib composition (`HahnSeries.C_mul_eq_smul`, Multiplication.lean:848, plus `smul_single`-style rewriting).

### `theorem Cox.explicitCandidateClearedLaurentTermThree` (private)
- **Type**: `(i d : Fin 5) → single 36 1 * (C c_{id} * σ^i * w^d) = ↑(PowerSeries.C c_{id} * X^{36−(9i+3d)} * (σ_ps^i * w_ps^d))`
- **What**: Each monomial of `t³⁶·Φ₃(T,J)` is the image of an honest power series.
- **How**: Rewrite with `shiftedPowerSeries_pow` (×2), `HahnSeries.ofPowerSeries_C/_X_pow`, `C_mul_single_one`; then 25 `fin_cases` each closed by `clearTwoShiftedPowerSeries` + `norm_num`.
- **Hypotheses**: none.
- **Uses from project**: [`explicitCoeffThree`, `sigmaLaurentSeriesThree`, `widthLaurentSeriesThree`, `sigmaPowerSeriesThree`, `widthPowerSeriesThree`, `shiftedPowerSeries_pow`, `C_mul_single_one`, `clearTwoShiftedPowerSeries`]
- **Used by**: `explicitCandidateClearedLaurentEvalThree`
- **Visibility**: private
- **Lines**: 200–218, body ≈ 10
- **Notes**: 25-way case split only to evaluate `36 − (9i+3d)` numerically; a lemma `(k ≤ 36) → single 36 1 * single (−k) c * … = single (36−k) c * …` would avoid it.

### `theorem Cox.qjIntegralPowerSeriesThree_coeff_eq_table` (private)
- **Type**: `(n) (hn : n < 13) → PowerSeries.coeff n qjIntegralPowerSeriesThree = qjCoeffTableThree n`
- **What**: The first 13 coefficients of the abstract series are the literal table.
- **How**: `PowerSeries.coeff_mk`, `jIntCoeff_eq_qjCoeffInt_three`, `qjCoeffInt_eq_tableThree`.
- **Hypotheses**: `n < 13`.
- **Uses from project**: [`qjIntegralPowerSeriesThree`, `jIntCoeff_eq_qjCoeffInt_three`, `qjCoeffInt_eq_tableThree`, `qjCoeffTableThree`]
- **Used by**: `sigmaPowerSeriesThree_coeff_eq_jet`, `widthPowerSeriesThree_coeff_eq_jet`
- **Visibility**: private
- **Lines**: 220–225, body ≈ 3

### `theorem Cox.sigmaPowerSeriesThree_coeff_eq_jet` (private)
- **Type**: `(n) (hn : n < 37) → coeff n sigmaPowerSeriesThree = sigmaJetThree n`
- **What**: The 9-fold expansion agrees with its jet below index 37.
- **How**: `PowerSeries.coeff_expand`, unfold `jetExpand`, `split_ifs`; the divisible case reduces to the table via `Nat.mul_div_left` and `qjIntegralPowerSeriesThree_coeff_eq_table` (needs `n/9 < 13`, by `lia`).
- **Hypotheses**: `n < 37`.
- **Uses from project**: [`sigmaPowerSeriesThree`, `sigmaJetThree`, `jetExpand`, `qjIntegralPowerSeriesThree_coeff_eq_table`]
- **Used by**: `explicitCandidateClearedPowerSeriesThree_coeff_eq_jet`
- **Visibility**: private
- **Lines**: 227–236, body ≈ 7
- **Notes**: Identical skeleton to the next entry (only `9`↔`3`): a general `coeff_expand_eq_jetExpand (k) (hk : 0 < k)` would serve both.

### `theorem Cox.widthPowerSeriesThree_coeff_eq_jet` (private)
- **Type**: `(n) (hn : n < 37) → coeff n widthPowerSeriesThree = widthJetThree n`
- **What**: The 3-fold expansion agrees with its jet below 37.
- **How**: As above with `3`.
- **Hypotheses**: `n < 37`.
- **Uses from project**: [`widthPowerSeriesThree`, `widthJetThree`, `jetExpand`, `qjIntegralPowerSeriesThree_coeff_eq_table`]
- **Used by**: `explicitCandidateClearedPowerSeriesThree_coeff_eq_jet`
- **Visibility**: private
- **Lines**: 238–247, body ≈ 7

### `theorem Cox.powerSeries_coeff_mul_eq_jetMul` (private)
- **Type**: `(F G) (f g) (hF : ∀ n < 37, coeff n F = f n) (hG : …) (n) (hn : n < 37) → coeff n (F*G) = jetMul f g n`
- **What**: The Cauchy product of two series is computed by `jetMul` of their jets in the truncation window.
- **How**: `PowerSeries.coeff_mul` (Basic.lean:243) and `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`, then `Finset.sum_congr`.
- **Hypotheses**: jets agree below 37; `n < 37`.
- **Uses from project**: [`jetMul`]
- **Used by**: `powerSeries_coeff_pow_eq_jetPow`, `explicitCandidateClearedPowerSeriesThree_coeff_eq_jet`
- **Visibility**: private
- **Lines**: 249–262, body ≈ 8
- **Notes**: The window `37` is hard-coded in the statement; should be a parameter `N`.

### `theorem Cox.powerSeries_coeff_pow_eq_jetPow` (private)
- **Type**: `(F) (f) (hF : ∀ n < 37, …) (d n) (hn : n < 37) → coeff n (F^d) = jetPow f d n`
- **What**: Powers agree with `jetPow` in the window.
- **How**: Induction on `d` with `pow_succ` and `powerSeries_coeff_mul_eq_jetMul`; base case `PowerSeries.coeff_one`.
- **Hypotheses**: as above.
- **Uses from project**: [`jetPow`, `powerSeries_coeff_mul_eq_jetMul`]
- **Used by**: `explicitCandidateClearedPowerSeriesThree_coeff_eq_jet`
- **Visibility**: private
- **Lines**: 264–273, body ≈ 5

### `theorem Cox.powerSeries_coeff_shift_eq_jetShift` (private)
- **Type**: `(F) (f) (hF) (k n) (hn : n < 37) → coeff n (X^k * F) = jetShift k f n`
- **What**: Shifts agree with `jetShift` in the window.
- **How**: `PowerSeries.coeff_X_pow_mul'` (Basic.lean:405), `split_ifs`.
- **Hypotheses**: as above.
- **Uses from project**: [`jetShift`]
- **Used by**: `explicitCandidateClearedPowerSeriesThree_coeff_eq_jet`
- **Visibility**: private
- **Lines**: 275–283, body ≈ 4

### `def Cox.explicitCandidateClearedPowerSeriesThree` (private)
- **Type**: `PowerSeries ℤ`
- **What**: The power series `t³⁶·Φ₃(T,J)` written as `∑_{i,d} c_{id} X^{36−9i−3d} σ^i w^d`.
- **How**: Double `Finset.sum`.
- **Hypotheses**: none.
- **Uses from project**: [`explicitCoeffThree`, `sigmaPowerSeriesThree`, `widthPowerSeriesThree`]
- **Used by**: `explicitCandidateClearedPowerSeriesThree_coeff_eq_jet`, `explicitCandidateClearedLaurentEvalThree`, `explicitCandidateLaurentEvalThree_coeff_eq_jet`
- **Visibility**: private
- **Lines**: 285–289, body ≈ 4

### `theorem Cox.explicitCandidateClearedPowerSeriesThree_coeff_eq_jet` (private)
- **Type**: `(n) (hn : n < 37) → coeff n explicitCandidateClearedPowerSeriesThree = explicitCandidateClearedJetThree n`
- **What**: The abstract cleared series and the computable jet agree below 37.
- **How**: `map_sum`, `PowerSeries.coeff_C_mul`, two `Finset.sum_congr`, then chain `powerSeries_coeff_shift_eq_jetShift` → `_mul_eq_jetMul` → `_pow_eq_jetPow` fed by the two `_coeff_eq_jet` lemmas.
- **Hypotheses**: `n < 37`.
- **Uses from project**: [`explicitCandidateClearedPowerSeriesThree`, `explicitCandidateClearedJetThree`, `explicitCandidateClearedJetRowThree`, `explicitCandidateClearedJetTermThree`, `powerSeries_coeff_shift_eq_jetShift`, `powerSeries_coeff_mul_eq_jetMul`, `powerSeries_coeff_pow_eq_jetPow`, `sigmaPowerSeriesThree_coeff_eq_jet`, `widthPowerSeriesThree_coeff_eq_jet`]
- **Used by**: `explicitCandidateLaurentEvalThree_coeff_eq_jet`
- **Visibility**: private
- **Lines**: 291–309, body ≈ 15

### `theorem Cox.bivariateLaurentEval_intCastThree` (private, `@[simp]`)
- **Type**: `(z : ℤ) → eval₂ (eval₂RingHom C widthLaurentSeriesThree) sigmaLaurentSeriesThree (z : BivariatePolynomial ℤ) = HahnSeries.C z`
- **What**: Integer constants evaluate to constants under the bivariate Laurent evaluation.
- **How**: `Polynomial.C_eq_intCast`, `eval₂_C` twice, `simp`.
- **Hypotheses**: none.
- **Uses from project**: [`sigmaLaurentSeriesThree`, `widthLaurentSeriesThree`, `BivariatePolynomial`]
- **Used by**: `explicitCandidateClearedLaurentEvalThree`
- **Visibility**: private
- **Lines**: 311–320, body ≈ 4
- **Notes**: `@[simp]` on a private lemma that is only ever passed explicitly to `simpa only [...]` (L345) — tag is dead. Follows from `Polynomial.eval₂_intCast`-style mathlib lemmas (`map_intCast` of the composite ring hom).

### `def Cox.explicitCandidateLaurentEvalThree` (private)
- **Type**: `LaurentSeries ℤ`
- **What**: `E(T_ℤ, J_ℤ)`: the explicit `Φ₃` evaluated at the integral series `(σ, w)` (`X ↦ σ`, `Y ↦ w`).
- **How**: `Polynomial.eval₂RingHom (Polynomial.eval₂RingHom C w) σ`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialThreeExplicit`, `sigmaLaurentSeriesThree`, `widthLaurentSeriesThree`]
- **Used by**: `explicitCandidateClearedLaurentEvalThree`, `explicitCandidateLaurentEvalThree_coeff_eq_jet`, `_observed_coefficients`, `_map_complex`, `explicitCandidateLaurentEvalComplexThree_coeff`
- **Visibility**: private
- **Lines**: 322–326, body ≈ 4

### `theorem Cox.explicitCandidateClearedLaurentEvalThree` (private)
- **Type**: `single 36 1 * explicitCandidateLaurentEvalThree = ↑explicitCandidateClearedPowerSeriesThree`
- **What**: `t³⁶·E(T,J)` is the coercion of the cleared power series.
- **How**: Replace `Φ₃` by its table (`modularPolynomialThreeExplicit_eq_table`), push `eval₂` through sums/products (`map_sum`, `Polynomial.eval₂_X/_C`), distribute with `Finset.mul_sum` twice and finish termwise with `explicitCandidateClearedLaurentTermThree` and `bivariateLaurentEval_intCastThree`.
- **Hypotheses**: none.
- **Uses from project**: [`explicitCandidateLaurentEvalThree`, `modularPolynomialThreeExplicit_eq_table`, `modularPolynomialThreeTable`, `explicitCandidateClearedPowerSeriesThree`, `BivariatePolynomial.varX`, `BivariatePolynomial.varY`, `bivariateLaurentEval_intCastThree`, `explicitCandidateClearedLaurentTermThree`]
- **Used by**: `explicitCandidateLaurentEvalThree_coeff_eq_jet`
- **Visibility**: private
- **Lines**: 328–347, body ≈ 16

### Mechanical jet-coefficient facts (lines 349–502; all private theorems, all closed by `decide +kernel` unless noted)

Every one of these is a numerical identity about the private jets above; `Used by` is the immediately enclosing aggregate. `Uses from project` is exactly the definition named in the statement (plus the listed sub-facts). No `set_option` anywhere.

| name | lines | statement | how | used by |
|---|---|---|---|---|
| `explicitCandidateClearedJetThree_zero` | 349–350 | jet 0 = 0 | `decide +kernel` | `…LaurentEvalThree_observed_coefficients` |
| `explicitCandidateClearedJetThree_three` | 352–353 | jet 3 = 0 | `decide +kernel` | same |
| `explicitCandidateClearedJetThree_six` | 355–356 | jet 6 = 0 | `decide +kernel` | same |
| `explicitCandidateClearedJetThree_nine` | 358–359 | jet 9 = 0 | `decide +kernel` | same |
| `explicitCandidateClearedJetThree_twelve` | 361–362 | jet 12 = 0 | `decide +kernel` | same |
| `explicitCandidateClearedJetRowThree_fifteen` | 364–367 | row `i` at 15 = `[0,0,12756069900288,−12756069900288,0].getD i 0` | `fin_cases i <;> decide +kernel` | `…JetThree_fifteen` |
| `explicitCandidateClearedJetThree_fifteen` | 369–372 | jet 15 = 0 | `simp [Fin.sum_univ_succ, row lemma]` | `…observed_coefficients` |
| `explicitCandidateClearedJetRowThree_eighteen_zero` | 374–375 | row 0 at 18 = 0 | `decide +kernel` | `…JetThree_eighteen` |
| `explicitCandidateClearedJetRowThree_eighteen_one` | 377–378 | row 1 at 18 = −1069956 | `decide +kernel` | same |
| `explicitCandidateClearedJetTermThree_eighteen_two_zero` | 380–381 | term (2,0) at 18 = 452984832000000 | `decide +kernel` | `…RowThree_eighteen_two` |
| `explicitCandidateClearedJetTermThree_eighteen_two_one` | 383–384 | term (2,1) at 18 = 6621765894144000 | `decide +kernel` | same |
| `explicitCandidateClearedJetTermThree_eighteen_two_two` | 386–387 | term (2,2) at 18 = 2451545154540144 | `decide +kernel` | same |
| `explicitCandidateClearedJetTermThree_eighteen_two_three` | 389–390 | term (2,3) at 18 = 3024814720896 | `decide +kernel` | same |
| `explicitCandidateClearedJetTermThree_eighteen_two_four` | 392–393 | term (2,4) at 18 = 0 | `decide +kernel` | same |
| `explicitCandidateClearedJetRowThree_eighteen_two` | 395–402 | row 2 at 18 = 9529320695405040 | `simp [Fin.sum_univ_succ, 5 term lemmas]` | `…JetThree_eighteen` |
| `explicitCandidateClearedJetTermThree_eighteen_three_zero` | 404–405 | term (3,0) at 18 = 82280448000 | `decide +kernel` | `…RowThree_eighteen_three` |
| `explicitCandidateClearedJetTermThree_eighteen_three_one` | 407–408 | term (3,1) at 18 = −926539716194568 | `decide +kernel` | same |
| `explicitCandidateClearedJetTermThree_eighteen_three_two` | 410–411 | term (3,2) at 18 = 21856278202594560 | `decide +kernel` | same |
| `explicitCandidateThreeThreeCore_left_lower` | 413–416 | `∑_{k<5} σ³(k)·w³(18−k) = 30456116651640888` | `decide +kernel` | `…Core_left` |
| `explicitCandidateThreeThreeCore_left_upper` | 418–421 | `∑_{5≤k<10} … = 3024811399680` | `decide +kernel` | `…Core_left` |
| `explicitCandidateThreeThreeCore_left` | 423–430 | `∑_{k<10} … = 30459141463040568` | `Finset.sum_range_add_sum_Ico` + `norm_num` | `…Term_eighteen_three_three` |
| `explicitCandidateThreeThreeCore_right` | 432–435 | `∑_{10≤k<19} … = 2251260` | `decide +kernel` | `…Term_eighteen_three_three` |
| `explicitCandidateClearedJetTermThree_eighteen_three_three` | 437–443 | term (3,3) at 18 = −30459141465291828 | `norm_num [defs]`, `rw [jetMul]`, split range at 10, `norm_num` | `…RowThree_eighteen_three` |
| `explicitCandidateClearedJetTermThree_eighteen_three_four` | 445–446 | term (3,4) at 18 = 0 | `decide +kernel` | same |
| `explicitCandidateClearedJetRowThree_eighteen_three` | 448–455 | row 3 at 18 = −9529320698443836 | `simp [Fin.sum_univ_succ, 5 term lemmas]` | `…JetThree_eighteen` |
| `explicitCandidateClearedJetRowThree_eighteen_four` | 457–458 | row 4 at 18 = 4108752 | `decide +kernel` | same |
| `explicitCandidateClearedJetThree_eighteen` | 460–467 | jet 18 = 0 | `simp [Fin.sum_univ_succ, 5 row lemmas]` | `…observed_coefficients` |
| `explicitCandidateClearedJetThree_twenty_four` | 469–470 | jet 24 = 0 | `decide +kernel` | same |
| `explicitCandidateClearedJetThree_twenty_seven` | 472–473 | jet 27 = 0 | `decide +kernel` | same |
| `explicitCandidateClearedJetRowThree_thirty_six_zero` | 475–477 | row 0 at 36 = 1380866012976278427391080 | `decide +kernel` | `…JetThree_thirty_six` |
| `explicitCandidateClearedJetRowThree_thirty_six_one` | 479–481 | row 1 at 36 = −578180419613894699719321392 | `decide +kernel` | same |
| `explicitCandidateClearedJetRowThree_thirty_six_two` | 483–485 | row 2 at 36 = 4714247207166783486045878412 | `decide +kernel` | same |
| `explicitCandidateClearedJetRowThree_thirty_six_three` | 487–489 | row 3 at 36 = −4137447653565867106877979180 | `decide +kernel` | same |
| `explicitCandidateClearedJetRowThree_thirty_six_four` | 491–493 | row 4 at 36 = 2042124031080 | `decide +kernel` | same |
| `explicitCandidateClearedJetThree_thirty_six` | 495–502 | jet 36 = 0 | `simp [Fin.sum_univ_succ, 5 row lemmas]` | `…observed_coefficients` |

(35 declarations; `Uses from project` for each: the jet definition in its statement, `jetPow`/`sigmaJetThree`/`widthJetThree` for the four `Core_*` facts, plus the sub-facts named in the `how` column. `explicitCandidateClearedJetTermThree_eighteen_three_three` additionally unfolds `explicitCoeffThree`, `jetShift`, `jetMul`.)

### `theorem Cox.explicitCandidateLaurentEvalThree_coeff_eq_jet` (private)
- **Type**: `(n) (hn : n < 37) → explicitCandidateLaurentEvalThree.coeff ((n:ℤ) − 36) = explicitCandidateClearedJetThree n`
- **What**: Coefficient `t^{n−36}` of `E(T,J)` is the jet value at `n`.
- **How**: Apply `coeff n` to `explicitCandidateClearedLaurentEvalThree`; `HahnSeries.coeff_single_mul` (Multiplication.lean:471), `LaurentSeries.coeff_coe_powerSeries` (RingTheory/LaurentSeries.lean:204), then `explicitCandidateClearedPowerSeriesThree_coeff_eq_jet`.
- **Hypotheses**: `n < 37`.
- **Uses from project**: [`explicitCandidateLaurentEvalThree`, `explicitCandidateClearedLaurentEvalThree`, `explicitCandidateClearedPowerSeriesThree`, `explicitCandidateClearedPowerSeriesThree_coeff_eq_jet`, `explicitCandidateClearedJetThree`]
- **Used by**: `explicitCandidateLaurentEvalThree_observed_coefficients`
- **Visibility**: private
- **Lines**: 504–516, body ≈ 9

### `theorem Cox.explicitCandidateLaurentEvalThree_observed_coefficients` (private)
- **Type**: 10-fold conjunction `E.coeff 0 = 0 ∧ E.coeff (−9) = 0 ∧ … ∧ E.coeff (−36) = 0` (exponents `0,−9,−12,−18,−21,−24,−27,−30,−33,−36`)
- **What**: The ten triangular Laurent coefficients of `E(T_ℤ,J_ℤ)` vanish.
- **How**: Ten `constructor` blocks, each `simpa using (…_coeff_eq_jet n _).trans …JetThree_<n>` for `n ∈ {36,27,24,18,15,12,9,6,3,0}`.
- **Hypotheses**: none.
- **Uses from project**: [`explicitCandidateLaurentEvalThree`, `explicitCandidateLaurentEvalThree_coeff_eq_jet`, the ten `explicitCandidateClearedJetThree_<n>` facts]
- **Used by**: `explicitCandidateLaurentEvalComplexThree_observed_coefficients`
- **Visibility**: private
- **Lines**: 518–557, body ≈ 29
- **Notes**: Conjunction shape is dictated by the consumer `symmetric_bidegree_three_eq_zero_of_laurent_coeff` (SymmetricCubicLaurent.lean:368). Could be `refine ⟨?_, …⟩ <;> simpa using …` in ~4 lines.

### `theorem Cox.int_dvd_iff_dvd_add_natAbs` (private)
- **Type**: `(d : ℕ) (k : ℤ) → (d:ℤ) ∣ k ↔ d ∣ (k + d).natAbs`
- **What**: Divisibility by `d` of an integer is divisibility of `|k + d|` in `ℕ`.
- **How**: `Int.natCast_dvd` (Data/Int/Basic.lean:72) and `Dvd.dvd.add`/`.sub` with `dvd_refl`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `three_dvd_iff_dvd_shift_natAbs`, `nine_dvd_iff_dvd_shift_natAbs`
- **Visibility**: private
- **Lines**: 559–567, body ≈ 7
- **Notes**: Equals `Int.natCast_dvd.trans` of `(dvd_add_self_right).symm` (Algebra/Ring/Divisibility/Basic.lean:164) — 1 line from mathlib.

### `theorem Cox.three_dvd_iff_dvd_shift_natAbs` / `nine_dvd_iff_dvd_shift_natAbs` (private)
- **Type**: `(k : ℤ) → (3:ℤ) ∣ k ↔ 3 ∣ (k+3).natAbs` and the same with `9`
- **What**: Numeric instances of the previous lemma.
- **How**: `simpa using int_dvd_iff_dvd_add_natAbs 3 k` (resp. `9`).
- **Hypotheses**: none.
- **Uses from project**: [`int_dvd_iff_dvd_add_natAbs`]
- **Used by**: `widthLaurentSeriesThree_eq_integral` (3) / `sigmaLaurentSeriesThree_map_complex` (9)
- **Visibility**: private
- **Lines**: 569–571 / 573–575, body ≈ 1 each
- **Notes**: Exist only so `rw` can match; junk once the two consumers are generalized.

### `theorem Cox.widthLaurentSeriesThree_eq_integral` (private)
- **Type**: `widthLaurentSeriesThree = jIntegralLaurentSeriesWidth 3`
- **What**: The `t⁻³·expand 3` construction coincides with the project's width-3 integral Laurent series of `j`.
- **How**: `ext k`; `HahnSeries.coeff_single_mul`, `jIntegralLaurentSeriesWidth_coeff`; case on `−3 ≤ k` and on `3 ∣ k`; `PowerSeries.coeff_expand`, `Int.natCast_div`, `Int.natCast_natAbs`, `Int.mul_ediv_cancel_left`.
- **Hypotheses**: none.
- **Uses from project**: [`widthLaurentSeriesThree`, `widthPowerSeriesThree`, `qjIntegralPowerSeriesThree`, `jIntegralLaurentSeriesWidth`, `jIntegralLaurentSeriesWidth_coeff`, `three_dvd_iff_dvd_shift_natAbs`]
- **Used by**: `widthLaurentSeriesThree_map_complex`
- **Visibility**: private
- **Lines**: 577–600, body ≈ 22
- **Notes**: Same skeleton as `sigmaLaurentSeriesThree_map_complex` (L609–636). The general statement `jIntegralLaurentSeriesWidth m = single (−m) 1 * ↑((PowerSeries.mk fun n ↦ jIntCoeff (n−1)).expand m)` belongs in Kronecker.lean.

### `theorem Cox.widthLaurentSeriesThree_map_complex` (private)
- **Type**: `widthLaurentSeriesThree.map (Int.castRingHom ℂ) = laurentqExpansion 3 j`
- **What**: Over `ℂ`, the integral width-3 series is the analytic Laurent expansion of `j` in `q^{1/3}`.
- **How**: `widthLaurentSeriesThree_eq_integral` + `jIntegralLaurentSeriesWidth_map_complex` + `norm_num` (`((3:ℕ):ℝ) = 3`).
- **Hypotheses**: none.
- **Uses from project**: [`widthLaurentSeriesThree`, `widthLaurentSeriesThree_eq_integral`, `jIntegralLaurentSeriesWidth_map_complex`, `laurentqExpansion`, `j`]
- **Used by**: `explicitCandidateLaurentEvalThree_map_complex`
- **Visibility**: private
- **Lines**: 602–607, body ≈ 3

### `theorem Cox.sigmaLaurentSeriesThree_map_complex` (private)
- **Type**: `sigmaLaurentSeriesThree.map (Int.castRingHom ℂ) = transformedJSeries (zeta 3) (sigmaZero 3)`
- **What**: Over `ℂ`, the integral `t⁻⁹·expand 9` series is the transformed series of `j` at `σ₀ = diag(3,1)` (whose phase `ζ^{a·b·…}` is `1` since `b = 0`).
- **How**: `ext k`; `transformedJSeries_coeff`, `norm_num [sigmaZero]` (turns `a² = 9`, `a·b = 0`); then the same two-level case split as `widthLaurentSeriesThree_eq_integral` with `nine_dvd_iff_dvd_shift_natAbs`.
- **Hypotheses**: none.
- **Uses from project**: [`sigmaLaurentSeriesThree`, `sigmaPowerSeriesThree`, `qjIntegralPowerSeriesThree`, `transformedJSeries`, `transformedJSeries_coeff`, `zeta`, `sigmaZero`, `nine_dvd_iff_dvd_shift_natAbs`]
- **Used by**: `explicitCandidateLaurentEvalThree_map_complex`
- **Visibility**: private
- **Lines**: 609–636, body ≈ 25
- **Notes**: Moral duplicate of L577–600. A Kronecker-level lemma `transformedJSeries ζ (sigmaZero m) = (jIntegralLaurentSeriesWidth (m*m)).map (Int.castRingHom K)` (true for every `m`, since `sigmaZero.b = 0`) would reduce this to `sigmaLaurentSeriesThree = jIntegralLaurentSeriesWidth 9` (a copy of the width lemma) — see Observations.

### `theorem Cox.bivariateLaurentEval_map` (private)
- **Type**: `{R S} [CommRing R] [CommRing S] (f : R →+* S) (T J) (T' J') (hT : laurentSeriesMapRingHom f T = T') (hJ : … J = J') (P : BivariatePolynomial R) → laurentSeriesMapRingHom f (P.eval₂ (eval₂RingHom C J) T) = (BivariatePolynomial.map f P).eval₂ (eval₂RingHom C J') T'`
- **What**: Bivariate Laurent evaluation commutes with coefficientwise base change.
- **How**: Rewrite both sides as `Polynomial.eval` of `bivariateSpecializeLaurent`, use `Polynomial.eval₂_at_apply`, `Polynomial.eval_map`, and `bivariateSpecializeLaurent_map_apply`.
- **Hypotheses**: `T', J'` are the images of `T, J`.
- **Uses from project**: [`laurentSeriesMapRingHom`, `bivariateSpecializeLaurent`, `bivariateSpecializeLaurent_map_apply`, `BivariatePolynomial.map`]
- **Used by**: `explicitCandidateLaurentEvalThree_map_complex`
- **Visibility**: private
- **Lines**: 638–654, body ≈ 7
- **Notes**: Fully general (no level-3 content); belongs in LaurentPolynomialEvaluation.lean as public API. Mathlib route: `Polynomial.hom_eval₂` (Algebra/Polynomial/Eval/Coeff.lean:172) + `Polynomial.eval₂_map` + `Polynomial.ringHom_ext`.

### `def Cox.explicitCandidateLaurentEvalComplexThree` (private)
- **Type**: `LaurentSeries ℂ`
- **What**: `Eᶜ(T, J)` with `T = transformedJSeries ζ₃ σ₀`, `J = laurentqExpansion 3 j`.
- **How**: `BivariatePolynomial.eval₂` of the complexified explicit polynomial.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial.map`, `modularPolynomialThreeExplicit`, `laurentqExpansion`, `j`, `transformedJSeries`, `zeta`, `sigmaZero`]
- **Used by**: `explicitCandidateLaurentEvalThree_map_complex`, `_coeff`, `_observed_coefficients`, `modularPolynomialThreeDifferenceLaurentEval_eq`
- **Visibility**: private
- **Lines**: 656–659, body ≈ 3

### `theorem Cox.explicitCandidateLaurentEvalThree_map_complex` (private)
- **Type**: `laurentSeriesMapRingHom (Int.castRingHom ℂ) explicitCandidateLaurentEvalThree = explicitCandidateLaurentEvalComplexThree`
- **What**: The complex evaluation is the base change of the integral one.
- **How**: `bivariateLaurentEval_map` with `sigmaLaurentSeriesThree_map_complex`, `widthLaurentSeriesThree_map_complex`.
- **Hypotheses**: none.
- **Uses from project**: [`laurentSeriesMapRingHom`, `explicitCandidateLaurentEvalThree`, `explicitCandidateLaurentEvalComplexThree`, `bivariateLaurentEval_map`, `sigmaLaurentSeriesThree_map_complex`, `widthLaurentSeriesThree_map_complex`]
- **Used by**: `explicitCandidateLaurentEvalComplexThree_coeff`
- **Visibility**: private
- **Lines**: 661–667, body ≈ 3

### `theorem Cox.explicitCandidateLaurentEvalComplexThree_coeff` (private)
- **Type**: `(k : ℤ) → explicitCandidateLaurentEvalComplexThree.coeff k = (explicitCandidateLaurentEvalThree.coeff k : ℂ)`
- **What**: Complex coefficients are casts of the integral ones.
- **How**: Rewrite by `_map_complex` backwards; `rfl` (`laurentSeriesMapRingHom_coeff`).
- **Hypotheses**: none.
- **Uses from project**: [`explicitCandidateLaurentEvalComplexThree`, `explicitCandidateLaurentEvalThree`, `explicitCandidateLaurentEvalThree_map_complex`]
- **Used by**: `explicitCandidateLaurentEvalComplexThree_observed_coefficients`
- **Visibility**: private
- **Lines**: 669–673, body ≈ 2

### `theorem Cox.explicitCandidateLaurentEvalComplexThree_observed_coefficients` (private)
- **Type**: the same 10-fold conjunction for `explicitCandidateLaurentEvalComplexThree`
- **What**: The ten triangular coefficients of `Eᶜ(T,J)` vanish.
- **How**: `simpa only [_coeff, Int.cast_eq_zero] using` the integral version.
- **Hypotheses**: none.
- **Uses from project**: [`explicitCandidateLaurentEvalComplexThree`, `explicitCandidateLaurentEvalComplexThree_coeff`, `explicitCandidateLaurentEvalThree_observed_coefficients`]
- **Used by**: `modularPolynomialThreeDifference_observed_coefficients`
- **Visibility**: private
- **Lines**: 675–687, body ≈ 2

### `theorem Cox.modularPolynomialC_three_laurent_root` (private)
- **Type**: `(modularPolynomialC 3).eval₂ (eval₂RingHom C (laurentqExpansion 3 j)) (transformedJSeries (zeta 3) (sigmaZero 3)) = 0`
- **What**: The true complex `Φ₃` vanishes at `(T, J)` (formal version of `Φ₃(j(3τ), j(τ)) = 0`).
- **How**: `Polynomial.eval₂_eq_eval_map`, `formalCoxPolynomial_eq_modularPolynomialC_map_j` (DiagonalLaurent.lean:189) turns it into the formal product `∏_σ (X − T_σ)` (`formalCoxPolynomial`), then `Polynomial.eval_prod` and `Finset.prod_eq_zero` at `σ₀`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialC`, `laurentqExpansion`, `j`, `transformedJSeries`, `zeta`, `sigmaZero`, `formalCoxPolynomial_eq_modularPolynomialC_map_j`, `formalCoxPolynomial`]
- **Used by**: `modularPolynomialThreeDifferenceLaurentEval_eq`
- **Visibility**: private
- **Lines**: 689–700, body ≈ 7
- **Notes**: Holds for every `m` and every `σ`; the general statement belongs in DiagonalLaurent.lean.

### `theorem Cox.transformedJSeries_three_sigmaZero_order` (private)
- **Type**: `(transformedJSeries (zeta 3) (sigmaZero 3)).order = −9`
- **What**: `T` has order `−9` (`= −a²` with `a = 3`).
- **How**: `transformedJSeries_order` (DiagonalLaurent.lean:65) with `ζ ≠ 0` from `zeta_isPrimitiveRoot`, `norm_num [sigmaZero]`.
- **Hypotheses**: none.
- **Uses from project**: [`transformedJSeries`, `transformedJSeries_order`, `zeta`, `zeta_isPrimitiveRoot`, `sigmaZero`]
- **Used by**: `modularPolynomialThreeDifference_eq_zero`
- **Visibility**: private
- **Lines**: 702–706, body ≈ 3

### `theorem Cox.transformedJSeries_three_sigmaZero_leadingCoeff` (private)
- **Type**: `(transformedJSeries (zeta 3) (sigmaZero 3)).leadingCoeff = 1`
- **What**: `T` has leading coefficient `1`.
- **How**: `transformedJSeries_leadingCoeff` (DiagonalLaurent.lean:80) + `norm_num [sigmaZero]`.
- **Hypotheses**: none.
- **Uses from project**: [`transformedJSeries`, `transformedJSeries_leadingCoeff`, `zeta`, `zeta_isPrimitiveRoot`, `sigmaZero`]
- **Used by**: `modularPolynomialThreeDifference_eq_zero`
- **Visibility**: private
- **Lines**: 708–713, body ≈ 3

### `theorem Cox.laurentqExpansion_j_order_three` / `laurentqExpansion_j_leadingCoeff_three` (private)
- **Type**: `(laurentqExpansion 3 j).order = −3` / `.leadingCoeff = 1`
- **What**: `J` has order `−3` and leading coefficient `1`.
- **How**: `norm_num` specialization of `laurentqExpansion_j_order_widthM` / `_leadingCoeff_widthM` (DiagonalLaurent.lean:33/44) at `m = 3`.
- **Hypotheses**: none.
- **Uses from project**: [`laurentqExpansion`, `j`, `laurentqExpansion_j_order_widthM` / `laurentqExpansion_j_leadingCoeff_widthM`]
- **Used by**: `modularPolynomialThreeDifference_eq_zero`
- **Visibility**: private
- **Lines**: 715–719 / 721–725, body ≈ 3 each
- **Notes**: Four `norm_num` specializations (L702–725) could be inlined at L828–831.

### `def Cox.modularPolynomialThreeComplexExplicit` (private)
- **Type**: `BivariatePolynomial ℂ`
- **What**: `Eᶜ`, the explicit polynomial with complex coefficients.
- **How**: `BivariatePolynomial.map (Int.castRingHom ℂ)`.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial.map`, `modularPolynomialThreeExplicit`]
- **Used by**: `modularPolynomialThreeDifference`, `_monic`, `_natDegree`, `_swap`, `modularPolynomialC_three_eq_explicit`
- **Visibility**: private
- **Lines**: 727–728

### `def Cox.modularPolynomialThreeDifference` (private)
- **Type**: `BivariatePolynomial ℂ`
- **What**: `D = Φ₃ᶜ − Eᶜ`.
- **How**: Subtraction.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialC`, `modularPolynomialThreeComplexExplicit`]
- **Used by**: `modularPolynomialThreeDifference_swap`, `_natDegree_le`, `_inner_natDegree_le`, `modularPolynomialThreeDifferenceLaurentEval`, `_LaurentEval_eq`, `_eq_zero`
- **Visibility**: private
- **Lines**: 730–731

### `theorem Cox.modularPolynomialC_three_natDegree` (private)
- **Type**: `(modularPolynomialC 3).natDegree = 4`
- **What**: `Φ₃ᶜ` has degree `4 = |C(3)| = 3 + 1` in `X`.
- **How**: `modularPolynomialC_natDegree` and `Fintype.card_congr (primeCoxMatrixEquiv 3)` (Kronecker.lean:130; uses the `Fact (Nat.Prime 3)` instance `Nat.fact_prime_three`).
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialC`, `modularPolynomialC_natDegree`, `primeCoxMatrixEquiv`, `CoxMatrix`]
- **Used by**: `modularPolynomialThreeDifference_natDegree_le`
- **Visibility**: private
- **Lines**: 733–738, body ≈ 4

### `theorem Cox.modularPolynomialThreeComplexExplicit_monic` (private)
- **Type**: `modularPolynomialThreeComplexExplicit.Monic`
- **What**: `Eᶜ` is monic.
- **How**: `Polynomial.Monic.map` of `modularPolynomialThreeExplicit_monic`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialThreeComplexExplicit`, `modularPolynomialThreeExplicit_monic`, `BivariatePolynomial.map`]
- **Used by**: `modularPolynomialThreeDifference_natDegree_le`
- **Visibility**: private
- **Lines**: 740–744, body ≈ 3

### `theorem Cox.modularPolynomialThreeComplexExplicit_natDegree` (private)
- **Type**: `modularPolynomialThreeComplexExplicit.natDegree = 4`
- **What**: `Eᶜ` has degree 4.
- **How**: `Polynomial.Monic.natDegree_map` (Algebra/Polynomial/Monic.lean:391) + `modularPolynomialThreeExplicit_natDegree`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialThreeComplexExplicit`, `modularPolynomialThreeExplicit_monic`, `modularPolynomialThreeExplicit_natDegree`, `BivariatePolynomial.map`]
- **Used by**: `modularPolynomialThreeDifference_natDegree_le`
- **Visibility**: private
- **Lines**: 746–751, body ≈ 4

### `theorem Cox.modularPolynomialThreeComplexExplicit_swap` (private)
- **Type**: `Polynomial.Bivariate.swap modularPolynomialThreeComplexExplicit = modularPolynomialThreeComplexExplicit`
- **What**: `Eᶜ` is symmetric.
- **How**: `BivariatePolynomial.map_swap` + `modularPolynomialThreeExplicit_swap`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialThreeComplexExplicit`, `BivariatePolynomial.map_swap`, `modularPolynomialThreeExplicit_swap`]
- **Used by**: `modularPolynomialThreeDifference_swap`
- **Visibility**: private
- **Lines**: 753–757, body ≈ 2

### `theorem Cox.modularPolynomialThreeDifference_swap` (private)
- **Type**: `(hsymm : swap (modularPolynomialC 3) = modularPolynomialC 3) → swap D = D`
- **What**: `D` is symmetric given `Φ₃ᶜ` is.
- **How**: `map_sub` for the ring hom `swap`, `hsymm`, `modularPolynomialThreeComplexExplicit_swap`.
- **Hypotheses**: complex `Φ₃` symmetric.
- **Uses from project**: [`modularPolynomialThreeDifference`, `modularPolynomialC`, `modularPolynomialThreeComplexExplicit_swap`]
- **Used by**: `modularPolynomialThreeDifference_inner_natDegree_le`, `modularPolynomialThreeDifference_eq_zero`
- **Visibility**: private
- **Lines**: 759–765, body ≈ 2

### `theorem Cox.modularPolynomialThreeDifference_natDegree_le` (private)
- **Type**: `modularPolynomialThreeDifference.natDegree ≤ 3`
- **What**: The difference of two monic degree-4 polynomials has degree `≤ 3`.
- **How**: `Polynomial.IsMonicOfDegree.natDegree_sub_lt` (Algebra/Polynomial/Degree/IsMonicOfDegree.lean:217) with the two `(natDegree, Monic)` pairs.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialThreeDifference`, `modularPolynomialC_three_natDegree`, `modularPolynomialC_monic`, `modularPolynomialThreeComplexExplicit_natDegree`, `modularPolynomialThreeComplexExplicit_monic`]
- **Used by**: `modularPolynomialThreeDifference_inner_natDegree_le`, `modularPolynomialThreeDifference_eq_zero`
- **Visibility**: private
- **Lines**: 767–774, body ≈ 6

### `theorem Cox.modularPolynomialThreeDifference_inner_natDegree_le` (private)
- **Type**: `(hsymm) (i : ℕ) → (modularPolynomialThreeDifference.coeff i).natDegree ≤ 3`
- **What**: Every `X^i`-coefficient of `D` has `Y`-degree `≤ 3` (transport the outer bound through symmetry).
- **How**: `Polynomial.natDegree_le_iff_coeff_eq_zero`, `BivariatePolynomial.coeff_coeff_swap`, `modularPolynomialThreeDifference_swap`, `Polynomial.coeff_eq_zero_of_natDegree_lt` with the outer bound.
- **Hypotheses**: complex `Φ₃` symmetric.
- **Uses from project**: [`modularPolynomialThreeDifference`, `modularPolynomialThreeDifference_swap`, `modularPolynomialThreeDifference_natDegree_le`, `BivariatePolynomial.coeff_coeff_swap`]
- **Used by**: `modularPolynomialThreeDifference_eq_zero`
- **Visibility**: private
- **Lines**: 776–791, body ≈ 12
- **Notes**: General fact "symmetric ⇒ inner degree ≤ outer degree"; deserves a `BivariatePolynomial` lemma in Construction.lean.

### `def Cox.modularPolynomialThreeDifferenceLaurentEval` (private)
- **Type**: `LaurentSeries ℂ`
- **What**: `D(T, J)`.
- **How**: `eval₂` as in `explicitCandidateLaurentEvalComplexThree`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialThreeDifference`, `laurentqExpansion`, `j`, `transformedJSeries`, `zeta`, `sigmaZero`]
- **Used by**: `modularPolynomialThreeDifferenceLaurentEval_eq`, `_observed_coefficients`, `modularPolynomialThreeDifference_eq_zero`
- **Visibility**: private
- **Lines**: 793–796, body ≈ 3

### `theorem Cox.modularPolynomialThreeDifferenceLaurentEval_eq` (private)
- **Type**: `modularPolynomialThreeDifferenceLaurentEval = −explicitCandidateLaurentEvalComplexThree`
- **What**: `D(T,J) = −Eᶜ(T,J)` because `Φ₃ᶜ(T,J) = 0`.
- **How**: `Polynomial.eval₂_sub`, `modularPolynomialC_three_laurent_root`, `zero_sub`, `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialThreeDifferenceLaurentEval`, `modularPolynomialThreeDifference`, `modularPolynomialC_three_laurent_root`, `explicitCandidateLaurentEvalComplexThree`]
- **Used by**: `modularPolynomialThreeDifference_observed_coefficients`
- **Visibility**: private
- **Lines**: 798–804, body ≈ 4

### `theorem Cox.modularPolynomialThreeDifference_observed_coefficients` (private)
- **Type**: the 10-fold conjunction for `modularPolynomialThreeDifferenceLaurentEval`
- **What**: The ten triangular coefficients of `D(T,J)` vanish.
- **How**: `simpa only [_LaurentEval_eq, HahnSeries.coeff_neg, neg_eq_zero]` from the `Eᶜ` version.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialThreeDifferenceLaurentEval`, `modularPolynomialThreeDifferenceLaurentEval_eq`, `explicitCandidateLaurentEvalComplexThree_observed_coefficients`]
- **Used by**: `modularPolynomialThreeDifference_eq_zero`
- **Visibility**: private
- **Lines**: 806–819, body ≈ 3

### `theorem Cox.modularPolynomialThreeDifference_eq_zero` (private)
- **Type**: `(hsymm : swap (modularPolynomialC 3) = modularPolynomialC 3) → modularPolynomialThreeDifference = 0`
- **What**: The rigidity step: a symmetric bidegree-`(≤3,≤3)` polynomial whose evaluation at `(T,J)` (orders `−9, −3`, leading coefficients `1`) has the ten triangular coefficients zero is zero.
- **How**: `symmetric_bidegree_three_eq_zero_of_laurent_coeff` (SymmetricCubicLaurent.lean:368) fed with the eight side conditions.
- **Hypotheses**: complex `Φ₃` symmetric.
- **Uses from project**: [`symmetric_bidegree_three_eq_zero_of_laurent_coeff`, `transformedJSeries`, `zeta`, `sigmaZero`, `laurentqExpansion`, `j`, `transformedJSeries_three_sigmaZero_order`, `transformedJSeries_three_sigmaZero_leadingCoeff`, `laurentqExpansion_j_order_three`, `laurentqExpansion_j_leadingCoeff_three`, `modularPolynomialThreeDifference`, `modularPolynomialThreeDifference_natDegree_le`, `modularPolynomialThreeDifference_inner_natDegree_le`, `modularPolynomialThreeDifference_swap`, `modularPolynomialThreeDifferenceLaurentEval`, `modularPolynomialThreeDifference_observed_coefficients`]
- **Used by**: `modularPolynomialC_three_eq_explicit`
- **Visibility**: private
- **Lines**: 821–836, body ≈ 12

### `theorem Cox.modularPolynomialC_three_eq_explicit` (private)
- **Type**: `(hsymm) → modularPolynomialC 3 = modularPolynomialThreeComplexExplicit`
- **What**: `Φ₃ᶜ = Eᶜ`.
- **How**: `sub_eq_zero` + `modularPolynomialThreeDifference_eq_zero`.
- **Hypotheses**: complex `Φ₃` symmetric.
- **Uses from project**: [`modularPolynomialC`, `modularPolynomialThreeComplexExplicit`, `modularPolynomialThreeDifference_eq_zero`]
- **Used by**: `modularPolynomial_three_of_complex_swap`
- **Visibility**: private
- **Lines**: 838–843, body ≈ 2

### `theorem Cox.modularPolynomial_three_of_complex_swap`
- **Type**: `(hsymm : Polynomial.Bivariate.swap (modularPolynomialC 3) = modularPolynomialC 3) → modularPolynomial 3 = modularPolynomialThreeExplicit`
- **What**: Cox eq. (11.22) for the integral `Φ₃`, conditional on symmetry of the complex `Φ₃`.
- **How**: Map both sides to `ℂ` (`modularPolynomial_map_complex`, `modularPolynomialC_three_eq_explicit`) and cancel the injective map `ℤ[X][Y] → ℂ[X][Y]` (`Polynomial.map_injective` twice, `Int.cast_injective`).
- **Hypotheses**: complex `Φ₃` symmetric (discharged in Arithmetic.lean by `theorem_11_18_iii`).
- **Uses from project**: [`modularPolynomial`, `modularPolynomialC`, `modularPolynomialThreeExplicit`, `modularPolynomial_map_complex`, `BivariatePolynomial.map`, `modularPolynomialC_three_eq_explicit`]
- **Used by**: unused in file (consumed by `Cox.modularPolynomial_three`, Arithmetic.lean:338)
- **Visibility**: public
- **Lines**: 845–856, body ≈ 9
- **Notes**: Axioms: `propext, Classical.choice, Quot.sound` only (verified by `#print axioms` in a scratch file).

## File Summary
- Total declarations: 108 (26 defs, 82 theorems, 0 instances, 0 other); 2 public (`modularPolynomialThreeExplicit`, `modularPolynomial_three_of_complex_swap`), 106 private.
- Key API (used by 3+ others in the file): `modularPolynomialThreeExplicit` (8), `explicitCoeffThree` (6), `jetMul` (4), `jetPow` (6), `sigmaJetThree`/`widthJetThree` (6 each), `explicitCandidateClearedJetTermThree` (14), `explicitCandidateClearedJetRowThree` (13), `explicitCandidateClearedJetThree` (12), `qjCoeffTableThree` (4), `qjIntegralPowerSeriesThree` (5), `sigmaPowerSeriesThree`/`widthPowerSeriesThree` (5 each), `sigmaLaurentSeriesThree` (4), `widthLaurentSeriesThree` (5), `explicitCandidateLaurentEvalThree` (5), `explicitCandidateLaurentEvalComplexThree` (4), `modularPolynomialThreeComplexExplicit` (5), `modularPolynomialThreeDifference` (6), `modularPolynomialThreeDifferenceLaurentEval` (3).
- Unused declarations (not used by anything in this file): `modularPolynomial_three_of_complex_swap` (terminal; used by Arithmetic.lean). Every private declaration is used at least once.
- Declarations with sorry: none.
- Declarations with set_option: none (no `maxHeartbeats`/`maxRecDepth` anywhere in the file).
- Proofs >30 lines: none (longest: `explicitCandidateLaurentEvalThree_observed_coefficients` ≈ 29 body lines, L518–557; `sigmaLaurentSeriesThree_map_complex` ≈ 25, L609–636; `widthLaurentSeriesThree_eq_integral` ≈ 22, L577–600).
- `decide +kernel` sites: 30 (L49 ×13 cases, L350, 353, 356, 359, 362, L367 ×5 cases, 375, 378, 381, 384, 387, 390, 393, 405, 408, 411, 416, 421, 435, 446, 458, 470, 473, 477, 481, 485, 489, 493). No `native_decide`, no `norm_num`-extension oracle.

## Observations (evidence for the analysis phases)

### Mathlib API candidates
- **Jet machinery vs mathlib** (L94–120): `jetMul` is `PowerSeries.coeff_mul` (RingTheory/PowerSeries/Basic.lean:243) re-indexed by `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`; `jetShift` is `PowerSeries.coeff_X_pow_mul'` (Basic.lean:405); `jetExpand` is `PowerSeries.coeff_expand` (RingTheory/PowerSeries/Expand.lean:110, with `coeff_expand_mul`:87 / `coeff_expand_of_not_dvd`:97); `jetPow` is iterated `coeff_mul`. `PowerSeries.trunc` (RingTheory/PowerSeries/Trunc.lean: `coeff_trunc`:63, `trunc_trunc_mul_trunc`:192, `coeff_mul_eq_coeff_trunc_mul_trunc₂`:224) is the mathlib truncation, but it produces a `Polynomial`, which (like `PowerSeries`) is a noncomputable `Finsupp` and cannot be reduced by `decide +kernel`. So the `ℕ → ℤ` jets are not replaceable by `PowerSeries.trunc`/`Polynomial.coeff`; they are the computable mirror the kernel needs, and the four `powerSeries_coeff_*_eq_jet*` lemmas (L249–283) are exactly the mirror-correctness proofs. **Verdict: not a mathlib duplicate, but a project duplicate** — qExpansion_tactic/Qj.lean already has a computable convolution layer (`convArrayUpTo`, `coeffArray`, `qjCoeffsArrayUpTo`, `qjCoeffInt`, Qj.lean:≈95–145) on `Array Int`; `qjCoeffInt_eq_tableThree` (L47) shows the kernel can already evaluate those arrays (13 cases in well under a second). A single shared "kernel-evaluable truncated series" API (`ℕ → ℤ` functions or arrays, with `coeff_mul`/`expand`/`X_pow_mul` bridging lemmas) would serve both this file and the tactic.
- **Import `Mathlib.RingTheory.PowerSeries.Trunc` (L7) is unused**: no `trunc` identifier occurs in the file (grep). `Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree` (L6) is used at L770; `Mathlib.Tactic.ComputeDegree` (L8) at L84.
- **Is `decide +kernel` the right tool?** Measured in a scratch file with verbatim copies of the private defs (`lake env lean`, default `maxHeartbeats`): the *un-split* `explicitCandidateClearedJetThree 18 = 0` kernel-checks in 0.37 s, `… 36 = 0` in 2.2–6.1 s, `… 27 = 0` in 3.1 s, the term `(3,3)` at 18 (which the file splits into four `Finset.Ico` chunks, L413–443) in 2.3 s, and a single `decide +kernel` proving **all ten coefficients at once** in 6.7 s. `native_decide` on the 36-coefficient takes 3.8 s. So (a) the kernel approach is viable and consistent with the file's stated policy (docstring L17–19; confirmed by `#print axioms`: no `Lean.ofReduceBool`), (b) plain `decide` (Meta-level `whnf`) would be far slower and `norm_num` cannot unfold the recursive `jetPow`, so `decide +kernel` is the right primitive, but (c) the 35-declaration term/row/chunk split at L349–502 plus the 29-line conjunction assembly at L518–557 (≈210 lines total) is not needed for feasibility in isolation and can be collapsed to one or two declarations (e.g. one 10-conjunction closed by `decide +kernel`, or `∀ n ∈ ({0,3,…,36} : Finset ℕ), … = 0`). If in-context kernel time turns out higher (the environment size does not affect kernel reduction, so this is unlikely), keep only the per-coefficient split (10 lemmas), not the per-term/per-chunk one.
- `C_mul_single_one` (L194) = `HahnSeries.C_mul_eq_smul` (RingTheory/HahnSeries/Multiplication.lean:848) + `HahnSeries.single_mul_single` (:776); `shiftedPowerSeries_pow` (L147) = `mul_pow` + `HahnSeries.single_pow` (:795) + `map_pow`; `shiftedPowerSeries_mul` (L154) = `mul_mul_mul_comm` + `single_mul_single` + `map_mul`. All three are general-`R` wrappers.
- `int_dvd_iff_dvd_add_natAbs` (L559) = `Int.natCast_dvd` (Data/Int/Basic.lean:72) composed with `dvd_add_self_right` (Algebra/Ring/Divisibility/Basic.lean:164).
- `bivariateLaurentEval_map` (L638) = `Polynomial.hom_eval₂` (Algebra/Polynomial/Eval/Coeff.lean:172) + `Polynomial.eval₂_map` + `Polynomial.ringHom_ext` (for the inner hom), 3–4 lines.
- `modularPolynomialThreeComplexExplicit_monic`/`_natDegree` (L740/746) are `Polynomial.Monic.map` / `Polynomial.Monic.natDegree_map` (Algebra/Polynomial/Monic.lean:391) one-liners once `BivariatePolynomial.map` is unfolded — a `BivariatePolynomial.map` API (`map_monic`, `natDegree_map`) is missing in Construction.lean.
- `Polynomial.Bivariate.swap` used here is mathlib's (Algebra/Polynomial/Bivariate.lean:248, `swap_X`:259, `swap_Y`:261, `swap_swap_apply`:268) — correct reuse.
- No mathlib analogue found for: the level-3 series identifications (`sigma/widthLaurentSeriesThree_map_complex`), `symmetric_bidegree_three…` rigidity (searched: `HahnSeries.order`, `LaurentSeries.order`, `leadingCoeff` files; nothing about bivariate rigidity).

### Missing API / repeated patterns
- **Repeated skeleton** L577–600 vs L609–636 (`by_cases hlower`, `PowerSeries.coeff_coe`, `if_neg hnonneg.not_gt`, `PowerSeries.coeff_expand`, `by_cases hkdiv`, `Int.natCast_div`, `Int.natCast_natAbs`, `abs_of_nonneg`, `obtain ⟨t, rfl⟩`, `norm_num [Int.mul_ediv_cancel_left]`): add to Kronecker.lean
  `theorem jIntegralLaurentSeriesWidth_eq_single_mul_expand (m : ℕ+) : jIntegralLaurentSeriesWidth m = HahnSeries.single (-(m:ℤ)) 1 * ↑((PowerSeries.mk fun n ↦ jIntCoeff ((n:ℤ) - 1)).expand m _)` and to DiagonalLaurent.lean
  `theorem transformedJSeries_sigmaZero (m : ℕ+) (ζ : K) : transformedJSeries ζ (sigmaZero m) = (jIntegralLaurentSeriesWidth ⟨m*m, _⟩).map (Int.castRingHom K)` (true since `(sigmaZero m).b = 0` kills the phase). Then both 22–25-line proofs and `three_/nine_dvd_iff_dvd_shift_natAbs` disappear.
- **Repeated skeleton** L227–236 vs L238–247 (`coeff_expand`, `jetExpand`, `split_ifs`, `Nat.mul_div_left`): one lemma `coeff_expand_eq_jetExpand (k) (hk : 0 < k) (F f) (hF : ∀ n < N, coeff n F = f n) (n) (hn : n < k*N) : coeff n (F.expand k _) = jetExpand k f n`.
- **Hard-coded window `37`** in `powerSeries_coeff_mul_eq_jetMul`, `_pow_eq_jetPow`, `_shift_eq_jetShift` (L249–283) and hard-coded `36` in `clearTwoShiftedPowerSeries` (L168): should be parameters.
- **Five `norm_num` specializations** at `m = 3` (L702–725, `modularPolynomialC_three_natDegree` L733) could be inlined at the consumer (L828–831) with `by simpa using …`.
- **Missing `BivariatePolynomial` companions**: `map_monic`, `map_natDegree`, `map_intCast` (would kill `bivariateLaurentEval_intCastThree`), `eval₂_eval₂RingHom` pushing lemmas; and the general "symmetric ⇒ inner natDegree ≤ outer natDegree" fact (L776–791).
- The 25-case `fin_cases i <;> fin_cases d` at L215–218 exists only to normalize `36 − (9i+3d)`; stating `explicitCandidateClearedLaurentTermThree` with a hypothesis `9i+3d ≤ 36` and a general shift lemma removes the case split.

### Junk candidates
- Dead `@[simp]` on private `bivariateLaurentEval_intCastThree` (L311): only used explicitly inside `simpa only […]` at L345.
- Unused import `Mathlib.RingTheory.PowerSeries.Trunc` (L7).
- `three_dvd_iff_dvd_shift_natAbs`, `nine_dvd_iff_dvd_shift_natAbs` (L569–575): 1-line `simpa` instances of the previous lemma.
- Two encodings of the same polynomial (`modularPolynomialThreeExplicit` L30 vs `explicitCoeffThree`/`modularPolynomialThreeTable` L51–64) reconciled by `ring_nf` at L66–72 — intentional (kernel needs the table) but worth a comment; none present.
- The `_three` suffix on `jIntCoeff_eq_qjCoeffInt_three` (L122) and `qjIntegralPowerSeriesThree` (L132) is misleading: neither is level-specific.
- No `#check`/`#eval`/`example`, no commented-out code, no TODO/FIXME.

### Moral duplicates within this batch
- `widthLaurentSeriesThree_eq_integral` (L577) ↔ `sigmaLaurentSeriesThree_map_complex` (L609): same proof with `3 ↔ 9` (and a trailing `simp` for the `ζ^0` phase).
- `sigmaPowerSeriesThree_coeff_eq_jet` (L227) ↔ `widthPowerSeriesThree_coeff_eq_jet` (L238): identical modulo `9 ↔ 3`.
- `three_dvd_iff…` ↔ `nine_dvd_iff…` (L569/573).
- `explicitCandidateClearedJetRowThree_eighteen_two` (L395) ↔ `…_eighteen_three` (L448) ↔ `…JetThree_eighteen` (L460) ↔ `…JetThree_thirty_six` (L495): same `simp [Fin.sum_univ_succ, five facts]` skeleton.
- `explicitCandidateLaurentEvalThree_observed_coefficients` (L518), `…ComplexThree_observed_coefficients` (L675), `modularPolynomialThreeDifference_observed_coefficients` (L806): three copies of the same 10-conjunction transported along `Int.cast` and negation. A `Prop`-valued abbreviation `TriangularCoeffsVanish (E : LaurentSeries K)` (and `map`/`neg` lemmas for it) would remove the duplication and shorten the statement of `symmetric_bidegree_three_eq_zero_of_laurent_coeff` too.
- Against other files: `modularPolynomialC_three_laurent_root` (L689) is the `m = 3, σ = σ₀` instance of a general fact provable verbatim from `formalCoxPolynomial_eq_modularPolynomialC_map_j` for any `m`, `σ`; `jIntCoeff_eq_qjCoeffInt_three` (L122) overlaps `jIntCoeff_neg_one` (CoxMatrices/LaurentExpansion.lean:38) and `qj_qexpansion_coeff_eq` (Qj.lean:152).

### Generalization notes
- `shiftedPowerSeries_pow`, `shiftedPowerSeries_mul`, `clearTwoShiftedPowerSeries`, `C_mul_single_one` (L147–198): stated for `ℤ`, proofs use only `HahnSeries.single_mul_single`, `single_pow`, `map_mul/pow` — any `CommSemiring R` (for `single_pow` a `Semiring` suffices; `ac_rfl` needs commutativity).
- `powerSeries_coeff_mul_eq_jetMul` / `_pow` / `_shift` (L249–283): `ℤ` → any `Semiring R` (uses `PowerSeries.coeff_mul`, `coeff_one`, `coeff_X_pow_mul'` only).
- `int_dvd_iff_dvd_add_natAbs` (L559): fine as is; mathlib composition preferred.
- `bivariateLaurentEval_map` (L638): already general; make public and move.
- `modularPolynomialThreeDifference_inner_natDegree_le` (L776): the argument only uses `coeff_coeff_swap` and the outer degree bound — holds for any symmetric `P : BivariatePolynomial R` over any `Semiring R`.
