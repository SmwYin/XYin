# Inventory: XYin/PhD/Cox/LevelThree.lean
Project-internal imports: `XYin.PhD.Cox.KroneckerFrobenius`, `XYin.PhD.Cox.SymmetricCubicLaurent`, `XYin.PhD.qExpansion_tactic.link`

All declarations live in namespace `Cox`. The file proves Cox's explicit formula (Cox, *Primes of the form x²+ny²*, eq. (11.22)) for the level-3 modular polynomial Φ₃(X,Y), conditional on a symmetry hypothesis for the complex modular polynomial. Strategy: the difference Δ = Φ₃^ℂ − (explicit polynomial over ℂ) is a symmetric bivariate polynomial of bidegree ≤ (3,3); evaluating it at the pair of Laurent series (transformed j-series at σ₀, q-expansion of j at width 3) gives a Laurent series whose 10 strategically chosen coefficients vanish (certified by kernel `decide` on integer jets of the q-expansion of j), which by `symmetric_bidegree_three_eq_zero_of_laurent_coeff` forces Δ = 0.

### `def modularPolynomialThreeExplicit`
- **Type**: `BivariatePolynomial ℤ`
- **What**: Cox's explicit level-three modular polynomial (equation (11.22)): X(X+2¹⁵·3·5³)³ + Y(Y+2¹⁵·3·5³)³ − X³Y³ + 2³·3²·31·X²Y²(X+Y) − 2²·3³·9907·XY(X²+Y²) + 2·3⁴·13·193·6367·X²Y² + 2¹⁶·3⁵·5³·17·263·XY(X+Y) − 2³¹·5⁶·22973·XY.
- **How**: Direct polynomial expression in `BivariatePolynomial.varX` and `BivariatePolynomial.varY` with the classical prime-factorised coefficients.
- **Hypotheses**: none.
- **Uses from project**: [BivariatePolynomial, BivariatePolynomial.varX, BivariatePolynomial.varY]
- **Used by**: modularPolynomialThreeExplicit_eq_table, modularPolynomialThreeExplicit_monic, modularPolynomialThreeExplicit_natDegree, modularPolynomialThreeExplicit_swap, explicitCandidateLaurentEvalThree, explicitCandidateLaurentEvalComplexThree, modularPolynomialThreeComplexExplicit, modularPolynomial_three_of_complex_swap
- **Visibility**: public
- **Lines**: 29–40 (def, 11 lines)
- **Notes**: the only public def in the file; has docstring.

### `def qjCoeffTableThree` (private)
- **Type**: `ℕ → ℤ`
- **What**: Hard-coded table of the first 13 integer coefficients of the q-expansion of j (i.e. c(−1)=1, c(0)=744, c(1)=196884, …, coefficient of q¹¹ = 146211911499519294), with default 0 beyond index 12.
- **How**: `List.getD` on an explicit 13-element integer list.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: qjCoeffInt_eq_tableThree, sigmaJetThree, widthJetThree, qjIntegralPowerSeriesThree_coeff_eq_table
- **Visibility**: private
- **Lines**: 42–45 (def, 4 lines)
- **Notes**: none

### `theorem qjCoeffInt_eq_tableThree` (private)
- **Type**: `(n : Fin 13) : qjCoeffInt n = qjCoeffTableThree n`
- **What**: The project's certified j-coefficient function `qjCoeffInt` (from the qExpansion tactic infrastructure) agrees with the hard-coded 13-entry table.
- **How**: Case split over Fin 13 (`fin_cases`) followed by kernel-reduction `decide +kernel`, so each of the 13 numeric equalities is checked by the Lean kernel without native code.
- **Hypotheses**: index n < 13.
- **Uses from project**: [qjCoeffInt, qjCoeffTableThree]
- **Used by**: qjIntegralPowerSeriesThree_coeff_eq_table
- **Visibility**: private
- **Lines**: 47–49 (proof 1 line)
- **Notes**: `decide +kernel`

### `def explicitCoeffThree` (private)
- **Type**: `Fin 5 → ℕ → ℤ`
- **What**: The 5×5 coefficient matrix of Cox's explicit Φ₃ written in the monomial basis Xⁱ Yᵈ (i,d ≤ 4); e.g. entry (0,1) = 1855425871872000000000, entry (4,0) = 1, symmetric in (i,d).
- **How**: Match on i with per-row `List.getD` tables of the fully multiplied-out coefficients.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: modularPolynomialThreeTable, modularPolynomialThreeExplicit_eq_table, explicitCandidateClearedJetTermThree, explicitCandidateClearedLaurentTermThree, explicitCandidateClearedPowerSeriesThree, explicitCandidateClearedJetTermThree_eighteen_three_three
- **Visibility**: private
- **Lines**: 51–59 (def, 9 lines)
- **Notes**: none

### `def modularPolynomialThreeTable` (private)
- **Type**: `BivariatePolynomial ℤ`
- **What**: Φ₃ rewritten as the double sum ∑_{i,d<5} explicitCoeffThree i d · Xⁱ Yᵈ — the tabular form of the explicit polynomial, convenient for termwise Laurent evaluation.
- **How**: Finite double sum over Fin 5 × Fin 5 of scalar multiples of monomials in varX, varY.
- **Hypotheses**: none.
- **Uses from project**: [explicitCoeffThree, BivariatePolynomial.varX, BivariatePolynomial.varY]
- **Used by**: modularPolynomialThreeExplicit_eq_table, explicitCandidateClearedLaurentEvalThree
- **Visibility**: private
- **Lines**: 61–64 (def, 4 lines)
- **Notes**: none

### `theorem modularPolynomialThreeExplicit_eq_table` (private)
- **Type**: `modularPolynomialThreeExplicit = modularPolynomialThreeTable`
- **What**: The factored Cox form and the tabular (monomial-basis) form of the explicit polynomial are equal — i.e. the 5×5 table really is the expansion of eq. (11.22).
- **How**: Unfold both sides (`Fin.sum_univ_succ` to expand the finite sums, `List.getD_cons_zero/succ` to evaluate the tables) and close by `ring_nf`, a purely algebraic identity of integer polynomials.
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialThreeExplicit, modularPolynomialThreeTable, explicitCoeffThree, BivariatePolynomial.varX, BivariatePolynomial.varY]
- **Used by**: explicitCandidateClearedLaurentEvalThree
- **Visibility**: private
- **Lines**: 66–72 (proof 6 lines)
- **Notes**: none

### `theorem modularPolynomialThreeExplicit_monic` (private)
- **Type**: `modularPolynomialThreeExplicit.Monic`
- **What**: The explicit polynomial, viewed as a polynomial in X over ℤ[Y], is monic (leading X⁴-coefficient is 1).
- **How**: Unfold and normalise with `ring_nf`, then the `monicity!` tactic (from `Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree` machinery) certifies monicity degree-by-degree.
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialThreeExplicit, BivariatePolynomial.varX, BivariatePolynomial.varY]
- **Used by**: modularPolynomialThreeComplexExplicit_monic, modularPolynomialThreeComplexExplicit_natDegree
- **Visibility**: private
- **Lines**: 74–78 (proof 4 lines)
- **Notes**: none

### `theorem modularPolynomialThreeExplicit_natDegree` (private)
- **Type**: `modularPolynomialThreeExplicit.natDegree = 4`
- **What**: The explicit polynomial has degree 4 in the outer variable X, matching the number of Cox matrices of determinant 3 (i.e. σ₀(3) + 1 = 4... here the 4 cyclic sublattices of index 3).
- **How**: Unfold, `ring_nf`, then `compute_degree!` computes the natDegree of the normalised expression.
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialThreeExplicit, BivariatePolynomial.varX, BivariatePolynomial.varY]
- **Used by**: modularPolynomialThreeComplexExplicit_natDegree
- **Visibility**: private
- **Lines**: 80–84 (proof 4 lines)
- **Notes**: none

### `theorem modularPolynomialThreeExplicit_swap` (private)
- **Type**: `Polynomial.Bivariate.swap modularPolynomialThreeExplicit = modularPolynomialThreeExplicit`
- **What**: The explicit polynomial is symmetric under exchanging X and Y (Φ₃(X,Y) = Φ₃(Y,X)).
- **How**: Push mathlib's `Polynomial.Bivariate.swap` through the arithmetic (`swap_X`, `swap_Y`, ring-hom map lemmas) and close by `ring` — the expression is visibly symmetric in X, Y.
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialThreeExplicit, BivariatePolynomial.varX, BivariatePolynomial.varY]
- **Used by**: modularPolynomialThreeComplexExplicit_swap
- **Visibility**: private
- **Lines**: 86–92 (proof 6 lines)
- **Notes**: none

### `def jetMul` (private)
- **Type**: `(F G : ℕ → ℤ) (n : ℕ) : ℤ`
- **What**: Cauchy product of two coefficient sequences: (F·G)(n) = ∑_{i≤n} F(i)·G(n−i). This is the "jet" (truncated power series) model of power-series multiplication, computable by `decide`.
- **How**: Finite sum over `Finset.range (n+1)`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: jetPow, explicitCandidateClearedJetTermThree, powerSeries_coeff_mul_eq_jetMul, explicitCandidateClearedJetTermThree_eighteen_three_three
- **Visibility**: private
- **Lines**: 94–95 (def, 2 lines)
- **Notes**: none

### `def jetPow` (private)
- **Type**: `(F : ℕ → ℤ) : ℕ → ℕ → ℤ`
- **What**: d-th power of a coefficient sequence under Cauchy product: jetPow F 0 = δ₀, jetPow F (d+1) = jetMul (jetPow F d) F — the jet model of PowerSeries pow.
- **How**: Recursion on the exponent using jetMul.
- **Hypotheses**: none.
- **Uses from project**: [jetMul]
- **Used by**: explicitCandidateClearedJetTermThree, powerSeries_coeff_pow_eq_jetPow, explicitCandidateThreeThreeCore_left_lower, explicitCandidateThreeThreeCore_left_upper, explicitCandidateThreeThreeCore_left, explicitCandidateThreeThreeCore_right
- **Visibility**: private
- **Lines**: 97–99 (def, 3 lines)
- **Notes**: none

### `def jetShift` (private)
- **Type**: `(k : ℕ) (F : ℕ → ℤ) (n : ℕ) : ℤ`
- **What**: Shift a coefficient sequence by k: the jet model of multiplication by qᵏ (returns F(n−k) if k ≤ n, else 0).
- **How**: if-then-else on k ≤ n.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: explicitCandidateClearedJetTermThree, powerSeries_coeff_shift_eq_jetShift, explicitCandidateClearedJetTermThree_eighteen_three_three
- **Visibility**: private
- **Lines**: 101–102 (def, 2 lines)
- **Notes**: none

### `def jetExpand` (private)
- **Type**: `(k : ℕ) (F : ℕ → ℤ) (n : ℕ) : ℤ`
- **What**: Expand a coefficient sequence by k: the jet model of the substitution q ↦ qᵏ (returns F(n/k) when k ∣ n, else 0), i.e. of `PowerSeries.expand`.
- **How**: if-then-else on k ∣ n.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: sigmaJetThree, widthJetThree, sigmaPowerSeriesThree_coeff_eq_jet, widthPowerSeriesThree_coeff_eq_jet
- **Visibility**: private
- **Lines**: 104–105 (def, 2 lines)
- **Notes**: none

### `def sigmaJetThree` (private)
- **Type**: `ℕ → ℤ`
- **What**: The jet (coefficient table) of the q⁹-expanded j-series: the power-series part of j((τ)/... at the σ₀ Cox matrix) has q-expansion j(q⁹) up to the q⁻⁹ pole shift; this is its coefficient sequence jetExpand 9 (table of j-coefficients).
- **How**: `jetExpand 9 qjCoeffTableThree`.
- **Hypotheses**: none.
- **Uses from project**: [jetExpand, qjCoeffTableThree]
- **Used by**: explicitCandidateClearedJetTermThree, sigmaPowerSeriesThree_coeff_eq_jet, explicitCandidateThreeThreeCore_left_lower, explicitCandidateThreeThreeCore_left_upper, explicitCandidateThreeThreeCore_left, explicitCandidateThreeThreeCore_right
- **Visibility**: private
- **Lines**: 107 (def, 1 line)
- **Notes**: none

### `def widthJetThree` (private)
- **Type**: `ℕ → ℤ`
- **What**: The jet of the q³-expanded j-series (q-expansion of j at width 3, power-series part): coefficient sequence jetExpand 3 (table of j-coefficients).
- **How**: `jetExpand 3 qjCoeffTableThree`.
- **Hypotheses**: none.
- **Uses from project**: [jetExpand, qjCoeffTableThree]
- **Used by**: explicitCandidateClearedJetTermThree, widthPowerSeriesThree_coeff_eq_jet, explicitCandidateThreeThreeCore_left_lower, explicitCandidateThreeThreeCore_left_upper, explicitCandidateThreeThreeCore_left, explicitCandidateThreeThreeCore_right
- **Visibility**: private
- **Lines**: 109 (def, 1 line)
- **Notes**: none

### `def explicitCandidateClearedJetTermThree` (private)
- **Type**: `(i d : Fin 5) (n : ℕ) : ℤ`
- **What**: The n-th coefficient of the (i,d)-term of the pole-cleared candidate series: coefficient c_{i,d} times the jet of q^{36−9i−3d}·(j(q⁹))ⁱ·(j(q³))ᵈ. Multiplying by q³⁶ clears the worst pole q⁻³⁶ of Φ₃(T, J).
- **How**: Composition of jetShift, jetMul, jetPow applied to sigmaJetThree and widthJetThree, scaled by explicitCoeffThree.
- **Hypotheses**: none.
- **Uses from project**: [explicitCoeffThree, jetShift, jetMul, jetPow, sigmaJetThree, widthJetThree]
- **Used by**: explicitCandidateClearedJetRowThree, explicitCandidateClearedJetTermThree_eighteen_two_zero/…_two_one/…_two_two/…_two_three/…_two_four/…_three_zero/…_three_one/…_three_two/…_three_three/…_three_four
- **Visibility**: private
- **Lines**: 111–114 (def, 4 lines)
- **Notes**: none

### `def explicitCandidateClearedJetRowThree` (private)
- **Type**: `(i : Fin 5) (n : ℕ) : ℤ`
- **What**: Row sum over d of the cleared jet terms: the n-th coefficient of the Xⁱ-row of the cleared candidate evaluation.
- **How**: `∑ d : Fin 5` of explicitCandidateClearedJetTermThree.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetTermThree]
- **Used by**: explicitCandidateClearedJetThree, explicitCandidateClearedJetRowThree_fifteen, …_eighteen_zero, …_eighteen_one, …_eighteen_two, …_eighteen_three, …_eighteen_four, …_thirty_six_zero…_thirty_six_four
- **Visibility**: private
- **Lines**: 116–117 (def, 2 lines)
- **Notes**: none

### `def explicitCandidateClearedJetThree` (private)
- **Type**: `(n : ℕ) : ℤ`
- **What**: The full n-th jet coefficient of q³⁶ · Φ₃^explicit(T-series, J-series): double sum over i,d of the cleared jet terms. Vanishing of this at the 10 observation points is the numerical heart of the proof.
- **How**: `∑ i : Fin 5` of the row jets.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetRowThree]
- **Used by**: explicitCandidateClearedPowerSeriesThree_coeff_eq_jet, explicitCandidateLaurentEvalThree_coeff_eq_jet, explicitCandidateClearedJetThree_zero/_three/_six/_nine/_twelve/_fifteen/_eighteen/_twenty_four/_twenty_seven/_thirty_six
- **Visibility**: private
- **Lines**: 119–120 (def, 2 lines)
- **Notes**: none

### `theorem jIntCoeff_eq_qjCoeffInt_three` (private)
- **Type**: `(n : ℕ) : jIntCoeff ((n : ℤ) - 1) = qjCoeffInt n`
- **What**: Bridges the two independent integrality certificates in the project: the Laurent-series integer coefficient function `jIntCoeff` of j (index shifted by the pole at −1) equals the q-expansion-tactic coefficient `qjCoeffInt`.
- **How**: Inject into ℂ, rewrite with `jIntCoeff_spec`, identify the Laurent coefficient above the pole with the qExpansion coefficient via `laurentqExpansion.coeff_of_geq` and `j_poleOrder`, then chain `j_to_qExpansion`, `qj_qexpansion`, `qj_qxp_coeff_link`.
- **Hypotheses**: none (works for all n since poleOrder 1 j = 1).
- **Uses from project**: [jIntCoeff, qjCoeffInt, jIntCoeff_spec, poleOrder, j, j_poleOrder, laurentqExpansion.coeff_of_geq, laurentqExpansion, j_to_qExpansion, qj_qexpansion, qj_qxp_coeff_link]
- **Used by**: qjIntegralPowerSeriesThree_coeff_eq_table
- **Visibility**: private
- **Lines**: 122–130 (proof 8 lines)
- **Notes**: none

### `def qjIntegralPowerSeriesThree` (private)
- **Type**: `PowerSeries ℤ`
- **What**: The integral power series ∑ jIntCoeff(n−1) qⁿ, i.e. q·(Laurent expansion of j) as a power series over ℤ — the integral model of q·j(q).
- **How**: `PowerSeries.mk` on the shifted jIntCoeff.
- **Hypotheses**: none.
- **Uses from project**: [jIntCoeff]
- **Used by**: sigmaPowerSeriesThree, widthPowerSeriesThree, qjIntegralPowerSeriesThree_coeff_eq_table, widthLaurentSeriesThree_eq_integral, sigmaLaurentSeriesThree_map_complex
- **Visibility**: private
- **Lines**: 132–133 (def, 2 lines)
- **Notes**: none

### `def sigmaPowerSeriesThree` (private)
- **Type**: `PowerSeries ℤ`
- **What**: The q ↦ q⁹ expansion of the integral q·j series: power-series part of the σ₀-transformed j-series at level 3 (σ₀ acts as τ ↦ 9τ on q-expansions since the relevant Cox matrix scales by 3² /... width 9).
- **How**: `PowerSeries.expand 9` of qjIntegralPowerSeriesThree.
- **Hypotheses**: none.
- **Uses from project**: [qjIntegralPowerSeriesThree]
- **Used by**: sigmaLaurentSeriesThree, sigmaPowerSeriesThree_coeff_eq_jet, explicitCandidateClearedLaurentTermThree, explicitCandidateClearedPowerSeriesThree, sigmaLaurentSeriesThree_map_complex
- **Visibility**: private
- **Lines**: 135–136 (def, 2 lines)
- **Notes**: none

### `def widthPowerSeriesThree` (private)
- **Type**: `PowerSeries ℤ`
- **What**: The q ↦ q³ expansion of the integral q·j series: power-series part of the width-3 q-expansion of j.
- **How**: `PowerSeries.expand 3` of qjIntegralPowerSeriesThree.
- **Hypotheses**: none.
- **Uses from project**: [qjIntegralPowerSeriesThree]
- **Used by**: widthLaurentSeriesThree, widthPowerSeriesThree_coeff_eq_jet, explicitCandidateClearedLaurentTermThree, explicitCandidateClearedPowerSeriesThree, widthLaurentSeriesThree_eq_integral
- **Visibility**: private
- **Lines**: 138–139 (def, 2 lines)
- **Notes**: none

### `def sigmaLaurentSeriesThree` (private)
- **Type**: `LaurentSeries ℤ`
- **What**: The integral Laurent series q⁻⁹ · sigmaPowerSeriesThree — the full σ₀-transformed j-series at level 3 with its order −9 pole restored.
- **How**: `HahnSeries.single (−9) 1` times the coerced power series.
- **Hypotheses**: none.
- **Uses from project**: [sigmaPowerSeriesThree]
- **Used by**: explicitCandidateClearedLaurentTermThree, bivariateLaurentEval_intCastThree, explicitCandidateLaurentEvalThree, sigmaLaurentSeriesThree_map_complex
- **Visibility**: private
- **Lines**: 141–142 (def, 2 lines)
- **Notes**: none

### `def widthLaurentSeriesThree` (private)
- **Type**: `LaurentSeries ℤ`
- **What**: The integral Laurent series q⁻³ · widthPowerSeriesThree — the width-3 q-expansion of j with its order −3 pole restored.
- **How**: `HahnSeries.single (−3) 1` times the coerced power series.
- **Hypotheses**: none.
- **Uses from project**: [widthPowerSeriesThree]
- **Used by**: explicitCandidateClearedLaurentTermThree, bivariateLaurentEval_intCastThree, explicitCandidateLaurentEvalThree, widthLaurentSeriesThree_eq_integral, widthLaurentSeriesThree_map_complex
- **Visibility**: private
- **Lines**: 144–145 (def, 2 lines)
- **Notes**: none

### `theorem shiftedPowerSeries_pow` (private)
- **Type**: `(a : ℤ) (F : PowerSeries ℤ) (n : ℕ) : (HahnSeries.single a 1 * (F : LaurentSeries ℤ)) ^ n = HahnSeries.single (n • a) 1 * ((F ^ n : PowerSeries ℤ) : LaurentSeries ℤ)`
- **What**: Powers of a monomial-shifted power series: (qᵃ·F)ⁿ = q^{na}·Fⁿ in the Laurent-series ring, with the coercion PowerSeries → LaurentSeries commuting with powers.
- **How**: `mul_pow` plus mathlib's `HahnSeries.single_pow` and `map_pow` for the `HahnSeries.ofPowerSeries` ring hom.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: explicitCandidateClearedLaurentTermThree
- **Visibility**: private
- **Lines**: 147–152 (proof 3 lines)
- **Notes**: none

### `theorem shiftedPowerSeries_mul` (private)
- **Type**: `(a b r s : ℤ) (F G : PowerSeries ℤ) : (single a r * F) * (single b s * G) = single (a+b) (r*s) * ((F*G : PowerSeries ℤ) : LaurentSeries ℤ)`
- **What**: Product of two monomial-shifted power series combines exponents and scalars: (r·qᵃF)(s·qᵇG) = rs·q^{a+b}(FG).
- **How**: Commutative reassociation (`ac_rfl`) then mathlib's `HahnSeries.single_mul_single` and multiplicativity of `HahnSeries.ofPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: clearTwoShiftedPowerSeries
- **Visibility**: private
- **Lines**: 154–166 (proof 7 lines)
- **Notes**: none

### `theorem clearTwoShiftedPowerSeries` (private)
- **Type**: `(c a b : ℤ) (F G : PowerSeries ℤ) : single 36 1 * (C c * (single a 1 * F) * (single b 1 * G)) = single (36+a+b) c * ((F*G : PowerSeries ℤ) : LaurentSeries ℤ)`
- **What**: Pole-clearing computation: multiplying a constant times two shifted power series by q³⁶ produces a single shift q^{36+a+b} of the product power series with scalar c.
- **How**: Calc chain rewriting the constant as `single 0 c * 1` and folding pairs with `shiftedPowerSeries_mul`, finishing with `HahnSeries.single_mul_single`.
- **Hypotheses**: none.
- **Uses from project**: [shiftedPowerSeries_mul]
- **Used by**: explicitCandidateClearedLaurentTermThree
- **Visibility**: private
- **Lines**: 168–192 (proof 24 lines)
- **Notes**: none

### `theorem C_mul_single_one` (private)
- **Type**: `(c k : ℤ) : HahnSeries.C c * (HahnSeries.single k 1 : LaurentSeries ℤ) = HahnSeries.single k c`
- **What**: A constant times a monic monomial in a Laurent series ring is the monomial with that constant coefficient.
- **How**: `HahnSeries.C_apply` and `HahnSeries.single_mul_single` with 0 + k = k.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: explicitCandidateClearedLaurentTermThree
- **Visibility**: private
- **Lines**: 194–198 (proof 3 lines)
- **Notes**: none

### `theorem explicitCandidateClearedLaurentTermThree` (private)
- **Type**: `(i d : Fin 5) : single 36 1 * (C (explicitCoeffThree i d) * sigmaLaurentSeriesThree ^ i * widthLaurentSeriesThree ^ d) = ((C (explicitCoeffThree i d) * X^(36−(9i+3d)) * (sigmaPowerSeriesThree ^ i * widthPowerSeriesThree ^ d) : PowerSeries ℤ) : LaurentSeries ℤ)`
- **What**: Per-monomial pole clearing: q³⁶ times the (i,d)-monomial of the candidate evaluated at the two Laurent series equals an honest power series, namely the coefficient times q^{36−9i−3d} times the expanded power-series powers. Well-defined since 9i+3d ≤ 36 for i,d ≤ 4.
- **How**: Rewrite the Laurent powers with `shiftedPowerSeries_pow`, push the coercion through with `HahnSeries.ofPowerSeries_C/X_pow` and `C_mul_single_one`, then a 25-way `fin_cases i <;> fin_cases d` case split applying `clearTwoShiftedPowerSeries` and `norm_num` to verify each exponent arithmetic 36 + (−9i) + (−3d) = 36 − (9i+3d) in ℤ vs ℕ subtraction.
- **Hypotheses**: i, d < 5 (so the ℕ-subtraction 36−(9i+3d) does not truncate).
- **Uses from project**: [explicitCoeffThree, sigmaLaurentSeriesThree, widthLaurentSeriesThree, sigmaPowerSeriesThree, widthPowerSeriesThree, shiftedPowerSeries_pow, clearTwoShiftedPowerSeries, C_mul_single_one]
- **Used by**: explicitCandidateClearedLaurentEvalThree
- **Visibility**: private
- **Lines**: 200–218 (proof 10 lines)
- **Notes**: none

### `theorem qjIntegralPowerSeriesThree_coeff_eq_table` (private)
- **Type**: `(n : ℕ) (hn : n < 13) : PowerSeries.coeff n qjIntegralPowerSeriesThree = qjCoeffTableThree n`
- **What**: The first 13 coefficients of the integral q·j power series agree with the hard-coded table.
- **How**: `PowerSeries.coeff_mk` plus the bridge `jIntCoeff_eq_qjCoeffInt_three` and the kernel-certified `qjCoeffInt_eq_tableThree`.
- **Hypotheses**: n < 13 (table length).
- **Uses from project**: [qjIntegralPowerSeriesThree, jIntCoeff_eq_qjCoeffInt_three, qjCoeffInt_eq_tableThree, qjCoeffTableThree]
- **Used by**: sigmaPowerSeriesThree_coeff_eq_jet, widthPowerSeriesThree_coeff_eq_jet, widthLaurentSeriesThree_eq_integral (via qjIntegralPowerSeriesThree unfolding — not the lemma), (directly:) sigmaPowerSeriesThree_coeff_eq_jet, widthPowerSeriesThree_coeff_eq_jet
- **Visibility**: private
- **Lines**: 220–225 (proof 5 lines)
- **Notes**: none

### `theorem sigmaPowerSeriesThree_coeff_eq_jet` (private)
- **Type**: `(n : ℕ) (hn : n < 37) : PowerSeries.coeff n sigmaPowerSeriesThree = sigmaJetThree n`
- **What**: The first 37 coefficients of the 9-fold expanded power series agree with the computable jet sigmaJetThree (only indices n/9 < 13 are ever needed, guaranteed by n < 37).
- **How**: `PowerSeries.coeff_expand` splits on 9 ∣ n; in the divisible case reduce to `qjIntegralPowerSeriesThree_coeff_eq_table` at n/9 with the bound discharged by `lia`.
- **Hypotheses**: n < 37 (the jet window; ensures n/9 < 13).
- **Uses from project**: [sigmaPowerSeriesThree, sigmaJetThree, jetExpand, qjIntegralPowerSeriesThree_coeff_eq_table]
- **Used by**: explicitCandidateClearedPowerSeriesThree_coeff_eq_jet
- **Visibility**: private
- **Lines**: 227–236 (proof 9 lines)
- **Notes**: none

### `theorem widthPowerSeriesThree_coeff_eq_jet` (private)
- **Type**: `(n : ℕ) (hn : n < 37) : PowerSeries.coeff n widthPowerSeriesThree = widthJetThree n`
- **What**: Same as the sigma version for the 3-fold expansion: the first 37 coefficients of widthPowerSeriesThree agree with the jet widthJetThree.
- **How**: `PowerSeries.coeff_expand`, split on 3 ∣ n, reduce to `qjIntegralPowerSeriesThree_coeff_eq_table` at n/3 (bound n/3 < 13 by `lia` from n < 37... n/3 ≤ 12).
- **Hypotheses**: n < 37.
- **Uses from project**: [widthPowerSeriesThree, widthJetThree, jetExpand, qjIntegralPowerSeriesThree_coeff_eq_table]
- **Used by**: explicitCandidateClearedPowerSeriesThree_coeff_eq_jet
- **Visibility**: private
- **Lines**: 238–247 (proof 9 lines)
- **Notes**: none

### `theorem powerSeries_coeff_mul_eq_jetMul` (private)
- **Type**: `(F G : PowerSeries ℤ) (f g : ℕ → ℤ) (hF : ∀ n < 37, coeff n F = f n) (hG : …) (n : ℕ) (hn : n < 37) : coeff n (F*G) = jetMul f g n`
- **What**: Soundness of the jet multiplication: if two power series agree with jets up to degree 36, so does their product (the Cauchy product only reads indices ≤ n).
- **How**: `PowerSeries.coeff_mul` plus `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` to convert the antidiagonal sum to the range sum defining jetMul, with index bounds by `lia`.
- **Hypotheses**: both series agree with their jets on indices < 37; n < 37.
- **Uses from project**: [jetMul]
- **Used by**: powerSeries_coeff_pow_eq_jetPow, explicitCandidateClearedPowerSeriesThree_coeff_eq_jet
- **Visibility**: private
- **Lines**: 249–262 (proof 8 lines)
- **Notes**: none

### `theorem powerSeries_coeff_pow_eq_jetPow` (private)
- **Type**: `(F : PowerSeries ℤ) (f : ℕ → ℤ) (hF : ∀ n < 37, coeff n F = f n) (d n : ℕ) (hn : n < 37) : coeff n (F ^ d) = jetPow f d n`
- **What**: Soundness of jet powers: a power series agreeing with a jet up to degree 36 has d-th power agreeing with jetPow f d there.
- **How**: Induction on d; base case `PowerSeries.coeff_one`, step via `pow_succ` and `powerSeries_coeff_mul_eq_jetMul` with the inductive hypothesis.
- **Hypotheses**: series agrees with jet below 37; n < 37.
- **Uses from project**: [jetPow, powerSeries_coeff_mul_eq_jetMul]
- **Used by**: explicitCandidateClearedPowerSeriesThree_coeff_eq_jet
- **Visibility**: private
- **Lines**: 264–273 (proof 7 lines)
- **Notes**: none

### `theorem powerSeries_coeff_shift_eq_jetShift` (private)
- **Type**: `(F : PowerSeries ℤ) (f : ℕ → ℤ) (hF : ∀ n < 37, coeff n F = f n) (k n : ℕ) (hn : n < 37) : coeff n (X ^ k * F) = jetShift k f n`
- **What**: Soundness of the jet shift: multiplying by Xᵏ shifts jet coefficients, matching jetShift.
- **How**: `PowerSeries.coeff_X_pow_mul'` gives the if-split on k ≤ n; apply hF at n−k (bound by `lia`).
- **Hypotheses**: series agrees with jet below 37; n < 37.
- **Uses from project**: [jetShift]
- **Used by**: explicitCandidateClearedPowerSeriesThree_coeff_eq_jet
- **Visibility**: private
- **Lines**: 275–283 (proof 5 lines)
- **Notes**: none

### `def explicitCandidateClearedPowerSeriesThree` (private)
- **Type**: `PowerSeries ℤ`
- **What**: The pole-cleared candidate as an honest integral power series: ∑_{i,d<5} c_{i,d}·X^{36−9i−3d}·(σ-series)ⁱ·(width-series)ᵈ, which equals q³⁶·Φ₃^explicit(T, J) as a Laurent series.
- **How**: Double finite sum of shifted products of the two expanded power series.
- **Hypotheses**: none.
- **Uses from project**: [explicitCoeffThree, sigmaPowerSeriesThree, widthPowerSeriesThree]
- **Used by**: explicitCandidateClearedPowerSeriesThree_coeff_eq_jet, explicitCandidateClearedLaurentEvalThree, explicitCandidateLaurentEvalThree_coeff_eq_jet
- **Visibility**: private
- **Lines**: 285–289 (def, 5 lines)
- **Notes**: none

### `theorem explicitCandidateClearedPowerSeriesThree_coeff_eq_jet` (private)
- **Type**: `(n : ℕ) (hn : n < 37) : coeff n explicitCandidateClearedPowerSeriesThree = explicitCandidateClearedJetThree n`
- **What**: The analytic cleared power series and the computable cleared jet agree on all coefficients below 37 — the bridge from PowerSeries algebra to kernel-decidable integer arithmetic.
- **How**: Reduce termwise (`Finset.sum_congr`) and stack the three soundness lemmas: `powerSeries_coeff_shift_eq_jetShift` outside, `powerSeries_coeff_mul_eq_jetMul` for the product, `powerSeries_coeff_pow_eq_jetPow` fed by `sigmaPowerSeriesThree_coeff_eq_jet` and `widthPowerSeriesThree_coeff_eq_jet`.
- **Hypotheses**: n < 37.
- **Uses from project**: [explicitCandidateClearedPowerSeriesThree, explicitCandidateClearedJetThree, explicitCandidateClearedJetRowThree, explicitCandidateClearedJetTermThree, powerSeries_coeff_shift_eq_jetShift, powerSeries_coeff_mul_eq_jetMul, powerSeries_coeff_pow_eq_jetPow, sigmaPowerSeriesThree_coeff_eq_jet, widthPowerSeriesThree_coeff_eq_jet]
- **Used by**: explicitCandidateLaurentEvalThree_coeff_eq_jet
- **Visibility**: private
- **Lines**: 291–309 (proof 15 lines)
- **Notes**: none

### `theorem bivariateLaurentEval_intCastThree` (private, @[simp])
- **Type**: `(z : ℤ) : Polynomial.eval₂ (eval₂RingHom HahnSeries.C widthLaurentSeriesThree) sigmaLaurentSeriesThree (z : BivariatePolynomial ℤ) = HahnSeries.C z`
- **What**: The two-stage bivariate evaluation map sends integer-constant polynomials to Hahn-series constants — the constants case of the evaluation homomorphism.
- **How**: Rewrite the int cast as `Polynomial.C` twice and use `Polynomial.eval₂_C` at both levels.
- **Hypotheses**: none.
- **Uses from project**: [widthLaurentSeriesThree, sigmaLaurentSeriesThree, BivariatePolynomial]
- **Used by**: explicitCandidateClearedLaurentEvalThree
- **Visibility**: private
- **Lines**: 311–320 (proof 4 lines)
- **Notes**: `@[simp]` attribute (private simp lemma)

### `def explicitCandidateLaurentEvalThree` (private)
- **Type**: `LaurentSeries ℤ`
- **What**: The integral Laurent series Φ₃^explicit(T, J) obtained by substituting the σ₀-transformed series for X and the width-3 j-series for Y in the explicit polynomial — the object whose coefficient vanishing is to be certified.
- **How**: Nested `Polynomial.eval₂RingHom`: inner variable Y ↦ widthLaurentSeriesThree via HahnSeries.C, outer variable X ↦ sigmaLaurentSeriesThree.
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialThreeExplicit, widthLaurentSeriesThree, sigmaLaurentSeriesThree]
- **Used by**: explicitCandidateClearedLaurentEvalThree, explicitCandidateLaurentEvalThree_coeff_eq_jet, explicitCandidateLaurentEvalThree_observed_coefficients, explicitCandidateLaurentEvalThree_map_complex, explicitCandidateLaurentEvalComplexThree_coeff
- **Visibility**: private
- **Lines**: 322–326 (def, 5 lines)
- **Notes**: none

### `theorem explicitCandidateClearedLaurentEvalThree` (private)
- **Type**: `single 36 1 * explicitCandidateLaurentEvalThree = (explicitCandidateClearedPowerSeriesThree : LaurentSeries ℤ)`
- **What**: Pole clearing at the level of the full evaluation: q³⁶ times the Laurent evaluation of the explicit polynomial is exactly the cleared power series (coerced to Laurent).
- **How**: Switch to the tabular form via `modularPolynomialThreeExplicit_eq_table`, push eval₂ through the double sum with `Polynomial.eval₂_X/eval₂_C`, distribute `Finset.mul_sum`, and close each monomial with `explicitCandidateClearedLaurentTermThree` (using the simp lemma `bivariateLaurentEval_intCastThree` for the constants).
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateLaurentEvalThree, modularPolynomialThreeExplicit_eq_table, modularPolynomialThreeTable, explicitCandidateClearedPowerSeriesThree, BivariatePolynomial.varX, BivariatePolynomial.varY, bivariateLaurentEval_intCastThree, explicitCandidateClearedLaurentTermThree]
- **Used by**: explicitCandidateLaurentEvalThree_coeff_eq_jet
- **Visibility**: private
- **Lines**: 328–347 (proof 19 lines)
- **Notes**: none

### `theorem explicitCandidateClearedJetThree_zero` (private)
- **Type**: `explicitCandidateClearedJetThree 0 = 0`
- **What**: The cleared jet vanishes at n = 0 (Laurent coefficient at q⁻³⁶ of the candidate evaluation is 0).
- **How**: Kernel-reduction `decide +kernel` on the closed integer computation.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetThree]
- **Used by**: explicitCandidateLaurentEvalThree_observed_coefficients
- **Visibility**: private
- **Lines**: 349–350 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetThree_three` (private)
- **Type**: `explicitCandidateClearedJetThree 3 = 0`
- **What**: The cleared jet vanishes at n = 3 (coefficient at q⁻³³).
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetThree]
- **Used by**: explicitCandidateLaurentEvalThree_observed_coefficients
- **Visibility**: private
- **Lines**: 352–353 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetThree_six` (private)
- **Type**: `explicitCandidateClearedJetThree 6 = 0`
- **What**: The cleared jet vanishes at n = 6 (coefficient at q⁻³⁰).
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetThree]
- **Used by**: explicitCandidateLaurentEvalThree_observed_coefficients
- **Visibility**: private
- **Lines**: 355–356 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetThree_nine` (private)
- **Type**: `explicitCandidateClearedJetThree 9 = 0`
- **What**: The cleared jet vanishes at n = 9 (coefficient at q⁻²⁷).
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetThree]
- **Used by**: explicitCandidateLaurentEvalThree_observed_coefficients
- **Visibility**: private
- **Lines**: 358–359 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetThree_twelve` (private)
- **Type**: `explicitCandidateClearedJetThree 12 = 0`
- **What**: The cleared jet vanishes at n = 12 (coefficient at q⁻²⁴).
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetThree]
- **Used by**: explicitCandidateLaurentEvalThree_observed_coefficients
- **Visibility**: private
- **Lines**: 361–362 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetRowThree_fifteen` (private)
- **Type**: `(i : Fin 5) : explicitCandidateClearedJetRowThree i 15 = [0, 0, 12756069900288, -12756069900288, 0].getD i 0`
- **What**: Row values of the cleared jet at n = 15: rows 2 and 3 contribute ±12756069900288 (cancelling), the rest 0 — splitting the n=15 computation row-by-row to keep each kernel reduction small.
- **How**: `fin_cases i` then per-row `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetRowThree]
- **Used by**: explicitCandidateClearedJetThree_fifteen
- **Visibility**: private
- **Lines**: 364–367 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetThree_fifteen` (private)
- **Type**: `explicitCandidateClearedJetThree 15 = 0`
- **What**: The cleared jet vanishes at n = 15 (coefficient at q⁻²¹): the two nonzero row contributions cancel.
- **How**: Expand the Fin 5 sum with `Fin.sum_univ_succ` and substitute the row values from `explicitCandidateClearedJetRowThree_fifteen`; the sum telescopes to 0 by simp arithmetic.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetThree, explicitCandidateClearedJetRowThree_fifteen]
- **Used by**: explicitCandidateLaurentEvalThree_observed_coefficients
- **Visibility**: private
- **Lines**: 369–372 (proof 3 lines)
- **Notes**: none

### `theorem explicitCandidateClearedJetRowThree_eighteen_zero` (private)
- **Type**: `explicitCandidateClearedJetRowThree 0 18 = 0`
- **What**: Row 0 of the cleared jet at n = 18 vanishes.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetRowThree]
- **Used by**: explicitCandidateClearedJetThree_eighteen
- **Visibility**: private
- **Lines**: 374–375 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetRowThree_eighteen_one` (private)
- **Type**: `explicitCandidateClearedJetRowThree 1 18 = -1069956`
- **What**: Row 1 of the cleared jet at n = 18 equals −1069956.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetRowThree]
- **Used by**: explicitCandidateClearedJetThree_eighteen
- **Visibility**: private
- **Lines**: 377–378 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetTermThree_eighteen_two_zero` (private)
- **Type**: `explicitCandidateClearedJetTermThree 2 0 18 = 452984832000000`
- **What**: The (i,d) = (2,0) term of the cleared jet at n = 18 — one summand of row 2, isolated because full-row kernel reduction would be too heavy here.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetTermThree]
- **Used by**: explicitCandidateClearedJetRowThree_eighteen_two
- **Visibility**: private
- **Lines**: 380–381 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetTermThree_eighteen_two_one` (private)
- **Type**: `explicitCandidateClearedJetTermThree 2 1 18 = 6621765894144000`
- **What**: The (2,1) term of the cleared jet at n = 18.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetTermThree]
- **Used by**: explicitCandidateClearedJetRowThree_eighteen_two
- **Visibility**: private
- **Lines**: 383–384 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetTermThree_eighteen_two_two` (private)
- **Type**: `explicitCandidateClearedJetTermThree 2 2 18 = 2451545154540144`
- **What**: The (2,2) term of the cleared jet at n = 18.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetTermThree]
- **Used by**: explicitCandidateClearedJetRowThree_eighteen_two
- **Visibility**: private
- **Lines**: 386–387 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetTermThree_eighteen_two_three` (private)
- **Type**: `explicitCandidateClearedJetTermThree 2 3 18 = 3024814720896`
- **What**: The (2,3) term of the cleared jet at n = 18.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetTermThree]
- **Used by**: explicitCandidateClearedJetRowThree_eighteen_two
- **Visibility**: private
- **Lines**: 389–390 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetTermThree_eighteen_two_four` (private)
- **Type**: `explicitCandidateClearedJetTermThree 2 4 18 = 0`
- **What**: The (2,4) term of the cleared jet at n = 18 vanishes.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetTermThree]
- **Used by**: explicitCandidateClearedJetRowThree_eighteen_two
- **Visibility**: private
- **Lines**: 392–393 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetRowThree_eighteen_two` (private)
- **Type**: `explicitCandidateClearedJetRowThree 2 18 = 9529320695405040`
- **What**: Row 2 of the cleared jet at n = 18, assembled from its five term values.
- **How**: Expand the Fin 5 sum (`Fin.sum_univ_succ`) and substitute the five kernel-certified term lemmas; simp does the integer addition.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetRowThree, explicitCandidateClearedJetTermThree_eighteen_two_zero, explicitCandidateClearedJetTermThree_eighteen_two_one, explicitCandidateClearedJetTermThree_eighteen_two_two, explicitCandidateClearedJetTermThree_eighteen_two_three, explicitCandidateClearedJetTermThree_eighteen_two_four]
- **Used by**: explicitCandidateClearedJetThree_eighteen
- **Visibility**: private
- **Lines**: 395–402 (proof 7 lines)
- **Notes**: none

### `theorem explicitCandidateClearedJetTermThree_eighteen_three_zero` (private)
- **Type**: `explicitCandidateClearedJetTermThree 3 0 18 = 82280448000`
- **What**: The (3,0) term of the cleared jet at n = 18.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetTermThree]
- **Used by**: explicitCandidateClearedJetRowThree_eighteen_three
- **Visibility**: private
- **Lines**: 404–405 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetTermThree_eighteen_three_one` (private)
- **Type**: `explicitCandidateClearedJetTermThree 3 1 18 = -926539716194568`
- **What**: The (3,1) term of the cleared jet at n = 18.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetTermThree]
- **Used by**: explicitCandidateClearedJetRowThree_eighteen_three
- **Visibility**: private
- **Lines**: 407–408 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetTermThree_eighteen_three_two` (private)
- **Type**: `explicitCandidateClearedJetTermThree 3 2 18 = 21856278202594560`
- **What**: The (3,2) term of the cleared jet at n = 18.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetTermThree]
- **Used by**: explicitCandidateClearedJetRowThree_eighteen_three
- **Visibility**: private
- **Lines**: 410–411 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateThreeThreeCore_left_lower` (private)
- **Type**: `(∑ k ∈ Finset.range 5, jetPow sigmaJetThree 3 k * jetPow widthJetThree 3 (18 - k)) = 30456116651640888`
- **What**: Partial Cauchy sum (indices 0–4) of the cube-times-cube convolution appearing in the (3,3) term at n = 18 — the heaviest single computation, split into three ranges so each kernel reduction stays tractable.
- **How**: `decide +kernel` on the closed sum.
- **Hypotheses**: none.
- **Uses from project**: [jetPow, sigmaJetThree, widthJetThree]
- **Used by**: explicitCandidateThreeThreeCore_left
- **Visibility**: private
- **Lines**: 413–416 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateThreeThreeCore_left_upper` (private)
- **Type**: `(∑ k ∈ Finset.Ico 5 10, jetPow sigmaJetThree 3 k * jetPow widthJetThree 3 (18 - k)) = 3024811399680`
- **What**: Partial Cauchy sum (indices 5–9) of the (3,3) convolution at n = 18.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [jetPow, sigmaJetThree, widthJetThree]
- **Used by**: explicitCandidateThreeThreeCore_left
- **Visibility**: private
- **Lines**: 418–421 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateThreeThreeCore_left` (private)
- **Type**: `(∑ k ∈ Finset.range 10, …) = 30459141463040568`
- **What**: Combined partial sum (indices 0–9) of the (3,3) convolution at n = 18.
- **How**: Split range 10 at 5 via `Finset.sum_range_add_sum_Ico` and add the two kernel-certified halves with `norm_num`.
- **Hypotheses**: none.
- **Uses from project**: [jetPow, sigmaJetThree, widthJetThree, explicitCandidateThreeThreeCore_left_lower, explicitCandidateThreeThreeCore_left_upper]
- **Used by**: explicitCandidateClearedJetTermThree_eighteen_three_three
- **Visibility**: private
- **Lines**: 423–430 (proof 7 lines)
- **Notes**: none

### `theorem explicitCandidateThreeThreeCore_right` (private)
- **Type**: `(∑ k ∈ Finset.Ico 10 19, jetPow sigmaJetThree 3 k * jetPow widthJetThree 3 (18 - k)) = 2251260`
- **What**: Tail (indices 10–18) of the (3,3) convolution at n = 18.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [jetPow, sigmaJetThree, widthJetThree]
- **Used by**: explicitCandidateClearedJetTermThree_eighteen_three_three
- **Visibility**: private
- **Lines**: 432–435 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetTermThree_eighteen_three_three` (private)
- **Type**: `explicitCandidateClearedJetTermThree 3 3 18 = -30459141465291828`
- **What**: The (3,3) term of the cleared jet at n = 18: coefficient −1 times the full Cauchy convolution of the two cubes (the value is −(30459141463040568 + 2251260)).
- **How**: Unfold the term to a jetMul convolution over range 19 (`norm_num` on explicitCoeffThree and jetShift, since 36−(27+9)=0), split the sum at 10 with `Finset.sum_range_add_sum_Ico`, and substitute `explicitCandidateThreeThreeCore_left` and `explicitCandidateThreeThreeCore_right`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetTermThree, explicitCoeffThree, jetShift, jetMul, explicitCandidateThreeThreeCore_left, explicitCandidateThreeThreeCore_right]
- **Used by**: explicitCandidateClearedJetRowThree_eighteen_three
- **Visibility**: private
- **Lines**: 437–443 (proof 6 lines)
- **Notes**: none

### `theorem explicitCandidateClearedJetTermThree_eighteen_three_four` (private)
- **Type**: `explicitCandidateClearedJetTermThree 3 4 18 = 0`
- **What**: The (3,4) term of the cleared jet at n = 18 vanishes (coefficient c₃,₄ = 0).
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetTermThree]
- **Used by**: explicitCandidateClearedJetRowThree_eighteen_three
- **Visibility**: private
- **Lines**: 445–446 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetRowThree_eighteen_three` (private)
- **Type**: `explicitCandidateClearedJetRowThree 3 18 = -9529320698443836`
- **What**: Row 3 of the cleared jet at n = 18, assembled from its five term values (nearly cancels row 2's +9529320695405040).
- **How**: Expand with `Fin.sum_univ_succ` and substitute the five term lemmas including the split-computation `…_eighteen_three_three`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetRowThree, explicitCandidateClearedJetTermThree_eighteen_three_zero, explicitCandidateClearedJetTermThree_eighteen_three_one, explicitCandidateClearedJetTermThree_eighteen_three_two, explicitCandidateClearedJetTermThree_eighteen_three_three, explicitCandidateClearedJetTermThree_eighteen_three_four]
- **Used by**: explicitCandidateClearedJetThree_eighteen
- **Visibility**: private
- **Lines**: 448–455 (proof 7 lines)
- **Notes**: none

### `theorem explicitCandidateClearedJetRowThree_eighteen_four` (private)
- **Type**: `explicitCandidateClearedJetRowThree 4 18 = 4108752`
- **What**: Row 4 of the cleared jet at n = 18.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetRowThree]
- **Used by**: explicitCandidateClearedJetThree_eighteen
- **Visibility**: private
- **Lines**: 457–458 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetThree_eighteen` (private)
- **Type**: `explicitCandidateClearedJetThree 18 = 0`
- **What**: The cleared jet vanishes at n = 18 (coefficient at q⁻¹⁸): 0 − 1069956 + 9529320695405040 − 9529320698443836 + 4108752 = 0.
- **How**: Expand the outer Fin 5 sum and substitute the five row lemmas; simp arithmetic verifies the cancellation.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetThree, explicitCandidateClearedJetRowThree_eighteen_zero, explicitCandidateClearedJetRowThree_eighteen_one, explicitCandidateClearedJetRowThree_eighteen_two, explicitCandidateClearedJetRowThree_eighteen_three, explicitCandidateClearedJetRowThree_eighteen_four]
- **Used by**: explicitCandidateLaurentEvalThree_observed_coefficients
- **Visibility**: private
- **Lines**: 460–467 (proof 7 lines)
- **Notes**: none

### `theorem explicitCandidateClearedJetThree_twenty_four` (private)
- **Type**: `explicitCandidateClearedJetThree 24 = 0`
- **What**: The cleared jet vanishes at n = 24 (coefficient at q⁻¹²).
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetThree]
- **Used by**: explicitCandidateLaurentEvalThree_observed_coefficients
- **Visibility**: private
- **Lines**: 469–470 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetThree_twenty_seven` (private)
- **Type**: `explicitCandidateClearedJetThree 27 = 0`
- **What**: The cleared jet vanishes at n = 27 (coefficient at q⁻⁹).
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetThree]
- **Used by**: explicitCandidateLaurentEvalThree_observed_coefficients
- **Visibility**: private
- **Lines**: 472–473 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetRowThree_thirty_six_zero` (private)
- **Type**: `explicitCandidateClearedJetRowThree 0 36 = 1380866012976278427391080`
- **What**: Row 0 of the cleared jet at n = 36 (constant Laurent coefficient), a 25-digit integer certified by the kernel.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetRowThree]
- **Used by**: explicitCandidateClearedJetThree_thirty_six
- **Visibility**: private
- **Lines**: 475–477 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetRowThree_thirty_six_one` (private)
- **Type**: `explicitCandidateClearedJetRowThree 1 36 = -578180419613894699719321392`
- **What**: Row 1 of the cleared jet at n = 36.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetRowThree]
- **Used by**: explicitCandidateClearedJetThree_thirty_six
- **Visibility**: private
- **Lines**: 479–481 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetRowThree_thirty_six_two` (private)
- **Type**: `explicitCandidateClearedJetRowThree 2 36 = 4714247207166783486045878412`
- **What**: Row 2 of the cleared jet at n = 36.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetRowThree]
- **Used by**: explicitCandidateClearedJetThree_thirty_six
- **Visibility**: private
- **Lines**: 483–485 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetRowThree_thirty_six_three` (private)
- **Type**: `explicitCandidateClearedJetRowThree 3 36 = -4137447653565867106877979180`
- **What**: Row 3 of the cleared jet at n = 36.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetRowThree]
- **Used by**: explicitCandidateClearedJetThree_thirty_six
- **Visibility**: private
- **Lines**: 487–489 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetRowThree_thirty_six_four` (private)
- **Type**: `explicitCandidateClearedJetRowThree 4 36 = 2042124031080`
- **What**: Row 4 of the cleared jet at n = 36.
- **How**: `decide +kernel`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetRowThree]
- **Used by**: explicitCandidateClearedJetThree_thirty_six
- **Visibility**: private
- **Lines**: 491–493 (proof 1 line)
- **Notes**: `decide +kernel`

### `theorem explicitCandidateClearedJetThree_thirty_six` (private)
- **Type**: `explicitCandidateClearedJetThree 36 = 0`
- **What**: The cleared jet vanishes at n = 36, i.e. the constant Laurent coefficient (coeff 0) of Φ₃^explicit(T,J) is zero — the five huge row contributions cancel exactly.
- **How**: Expand with `Fin.sum_univ_succ` and substitute the five kernel-certified row values at n = 36.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateClearedJetThree, explicitCandidateClearedJetRowThree_thirty_six_zero, explicitCandidateClearedJetRowThree_thirty_six_one, explicitCandidateClearedJetRowThree_thirty_six_two, explicitCandidateClearedJetRowThree_thirty_six_three, explicitCandidateClearedJetRowThree_thirty_six_four]
- **Used by**: explicitCandidateLaurentEvalThree_observed_coefficients
- **Visibility**: private
- **Lines**: 495–502 (proof 7 lines)
- **Notes**: none

### `theorem explicitCandidateLaurentEvalThree_coeff_eq_jet` (private)
- **Type**: `(n : ℕ) (hn : n < 37) : explicitCandidateLaurentEvalThree.coeff ((n : ℤ) - 36) = explicitCandidateClearedJetThree n`
- **What**: Coefficient bridge: the Laurent coefficient of the candidate evaluation at degree n − 36 equals the computable cleared jet at n, for n < 37 (i.e. all Laurent degrees from −36 to 0).
- **How**: Apply coeff at n to `explicitCandidateClearedLaurentEvalThree`; `HahnSeries.coeff_single_mul` shifts the index by 36 and `LaurentSeries.coeff_coe_powerSeries` plus `explicitCandidateClearedPowerSeriesThree_coeff_eq_jet` identifies the right side.
- **Hypotheses**: n < 37.
- **Uses from project**: [explicitCandidateLaurentEvalThree, explicitCandidateClearedJetThree, explicitCandidateClearedLaurentEvalThree, explicitCandidateClearedPowerSeriesThree, explicitCandidateClearedPowerSeriesThree_coeff_eq_jet]
- **Used by**: explicitCandidateLaurentEvalThree_observed_coefficients
- **Visibility**: private
- **Lines**: 504–516 (proof 12 lines)
- **Notes**: none

### `theorem explicitCandidateLaurentEvalThree_observed_coefficients` (private)
- **Type**: 10-fold conjunction: `explicitCandidateLaurentEvalThree.coeff k = 0` for k ∈ {0, −9, −12, −18, −21, −24, −27, −30, −33, −36}
- **What**: The ten observed Laurent coefficients of the integral candidate evaluation all vanish — exactly the coefficient positions the symmetric-cubic vanishing criterion requires.
- **How**: Each conjunct is `explicitCandidateLaurentEvalThree_coeff_eq_jet` at n = 36, 27, 24, 18, 15, 12, 9, 6, 3, 0 chained (`.trans`) with the corresponding kernel-certified jet-vanishing lemma (e.g. `explicitCandidateClearedJetThree_thirty_six`).
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateLaurentEvalThree, explicitCandidateLaurentEvalThree_coeff_eq_jet, explicitCandidateClearedJetThree_zero, explicitCandidateClearedJetThree_three, explicitCandidateClearedJetThree_six, explicitCandidateClearedJetThree_nine, explicitCandidateClearedJetThree_twelve, explicitCandidateClearedJetThree_fifteen, explicitCandidateClearedJetThree_eighteen, explicitCandidateClearedJetThree_twenty_four, explicitCandidateClearedJetThree_twenty_seven, explicitCandidateClearedJetThree_thirty_six]
- **Used by**: explicitCandidateLaurentEvalComplexThree_observed_coefficients
- **Visibility**: private
- **Lines**: 518–557 (proof 39 lines)
- **Notes**: proof >30 lines (mechanical 10-conjunct assembly)

### `theorem int_dvd_iff_dvd_add_natAbs` (private)
- **Type**: `(d : ℕ) (k : ℤ) : (d : ℤ) ∣ k ↔ d ∣ (k + d).natAbs`
- **What**: An integer k is divisible by d iff the natural number |k + d| is — a helper to convert integer divisibility (Laurent index) to natural-number divisibility (natAbs index) after shifting past the pole.
- **How**: Via `Int.natCast_dvd`; both directions add/subtract the trivially divisible d (`Dvd.dvd.add`, `Dvd.dvd.sub` with `dvd_refl`).
- **Hypotheses**: none (though only useful when k ≥ −d so the natAbs is faithful).
- **Uses from project**: []
- **Used by**: three_dvd_iff_dvd_shift_natAbs, nine_dvd_iff_dvd_shift_natAbs
- **Visibility**: private
- **Lines**: 559–567 (proof 7 lines)
- **Notes**: none

### `theorem three_dvd_iff_dvd_shift_natAbs` (private)
- **Type**: `(k : ℤ) : (3 : ℤ) ∣ k ↔ 3 ∣ (k + 3).natAbs`
- **What**: Specialisation of the divisibility-shift lemma to d = 3 (width-3 series indices).
- **How**: `simpa` from `int_dvd_iff_dvd_add_natAbs 3 k`.
- **Hypotheses**: none.
- **Uses from project**: [int_dvd_iff_dvd_add_natAbs]
- **Used by**: widthLaurentSeriesThree_eq_integral
- **Visibility**: private
- **Lines**: 569–571 (proof 1 line)
- **Notes**: none

### `theorem nine_dvd_iff_dvd_shift_natAbs` (private)
- **Type**: `(k : ℤ) : (9 : ℤ) ∣ k ↔ 9 ∣ (k + 9).natAbs`
- **What**: Specialisation of the divisibility-shift lemma to d = 9 (σ₀-series indices).
- **How**: `simpa` from `int_dvd_iff_dvd_add_natAbs 9 k`.
- **Hypotheses**: none.
- **Uses from project**: [int_dvd_iff_dvd_add_natAbs]
- **Used by**: sigmaLaurentSeriesThree_map_complex
- **Visibility**: private
- **Lines**: 573–575 (proof 1 line)
- **Notes**: none

### `theorem widthLaurentSeriesThree_eq_integral` (private)
- **Type**: `widthLaurentSeriesThree = jIntegralLaurentSeriesWidth (3 : ℕ+)`
- **What**: The locally constructed integral width-3 Laurent series (q⁻³ times the 3-expanded q·j power series) coincides with the project's canonical integral width-m Laurent series of j at m = 3.
- **How**: Coefficient-wise extension (`ext k`): unfold both sides with `HahnSeries.coeff_single_mul`, `jIntegralLaurentSeriesWidth_coeff`, and `PowerSeries.coeff_expand`; case-split on k ≥ −3 and 3 ∣ k, converting divisibility via `three_dvd_iff_dvd_shift_natAbs` and matching indices with `Int.natCast_div`, `Int.mul_ediv_cancel_left`.
- **Hypotheses**: none.
- **Uses from project**: [widthLaurentSeriesThree, jIntegralLaurentSeriesWidth, jIntegralLaurentSeriesWidth_coeff, widthPowerSeriesThree, qjIntegralPowerSeriesThree, jIntCoeff, three_dvd_iff_dvd_shift_natAbs]
- **Used by**: widthLaurentSeriesThree_map_complex
- **Visibility**: private
- **Lines**: 577–600 (proof 23 lines)
- **Notes**: none

### `theorem widthLaurentSeriesThree_map_complex` (private)
- **Type**: `widthLaurentSeriesThree.map (Int.castRingHom ℂ) = laurentqExpansion 3 j`
- **What**: The integral width-3 series, base-changed to ℂ, is the genuine analytic Laurent q-expansion of j at width 3 — the analytic meaning of the Y-substitution.
- **How**: Rewrite via `widthLaurentSeriesThree_eq_integral` and apply the project's integrality theorem `jIntegralLaurentSeriesWidth_map_complex` at m = 3.
- **Hypotheses**: none.
- **Uses from project**: [widthLaurentSeriesThree, widthLaurentSeriesThree_eq_integral, jIntegralLaurentSeriesWidth_map_complex, laurentqExpansion, j]
- **Used by**: explicitCandidateLaurentEvalThree_map_complex
- **Visibility**: private
- **Lines**: 602–607 (proof 4 lines)
- **Notes**: none

### `theorem sigmaLaurentSeriesThree_map_complex` (private)
- **Type**: `sigmaLaurentSeriesThree.map (Int.castRingHom ℂ) = transformedJSeries (zeta 3) (sigmaZero 3)`
- **What**: The integral σ-series, base-changed to ℂ, equals the analytic transformed j-series at the Cox matrix σ₀ for level 3 (whose q-expansion is j(q⁹) with pole order 9) — the analytic meaning of the X-substitution.
- **How**: Coefficient-wise: unfold `transformedJSeries_coeff` and the local definition; case split on k ≥ −9 and 9 ∣ k, converting divisibility via `nine_dvd_iff_dvd_shift_natAbs` and matching the shifted quotient indices (`Int.natCast_div`, `abs_of_nonneg`, `Int.mul_ediv_cancel_left`); off-support coefficients vanish on both sides.
- **Hypotheses**: none.
- **Uses from project**: [sigmaLaurentSeriesThree, transformedJSeries, transformedJSeries_coeff, zeta, sigmaZero, sigmaPowerSeriesThree, qjIntegralPowerSeriesThree, jIntCoeff, nine_dvd_iff_dvd_shift_natAbs]
- **Used by**: explicitCandidateLaurentEvalThree_map_complex
- **Visibility**: private
- **Lines**: 609–636 (proof 27 lines)
- **Notes**: none

### `theorem bivariateLaurentEval_map` (private)
- **Type**: `{R S} [CommRing R] [CommRing S] (f : R →+* S) (T J : LaurentSeries R) (T' J' : LaurentSeries S) (hT : laurentSeriesMapRingHom f T = T') (hJ : …) (P : BivariatePolynomial R) : laurentSeriesMapRingHom f (P.eval₂ (eval₂RingHom C J) T) = (BivariatePolynomial.map f P).eval₂ (eval₂RingHom C J') T'`
- **What**: General base-change compatibility: mapping a bivariate-polynomial Laurent evaluation along a ring hom f equals evaluating the f-mapped polynomial at the f-mapped series. Used with f = Int.castRingHom ℂ to transfer the integral certificate to ℂ.
- **How**: Two applications of mathlib's `Polynomial.hom_eval₂` (one per polynomial level) plus `Polynomial.eval₂_map`, after establishing that the Laurent map ring hom commutes with `HahnSeries.C` (`HahnSeries.map_C`).
- **Hypotheses**: f a ring hom between commutative rings; T, J map to T', J' under the coefficientwise Laurent map.
- **Uses from project**: [laurentSeriesMapRingHom, BivariatePolynomial, BivariatePolynomial.map]
- **Used by**: explicitCandidateLaurentEvalThree_map_complex
- **Visibility**: private
- **Lines**: 638–674 (proof 36 lines)
- **Notes**: proof >30 lines; fully generic — a candidate for extraction to the LaurentPolynomialEvaluation module

### `def explicitCandidateLaurentEvalComplexThree` (private)
- **Type**: `LaurentSeries ℂ`
- **What**: The complex Laurent series Φ₃^explicit,ℂ(T, J): the complexified explicit polynomial evaluated at the analytic transformed j-series (X) and the analytic width-3 q-expansion of j (Y).
- **How**: Nested `eval₂RingHom` over ℂ applied to the mapped polynomial.
- **Hypotheses**: none.
- **Uses from project**: [BivariatePolynomial.map, modularPolynomialThreeExplicit, laurentqExpansion, j, transformedJSeries, zeta, sigmaZero]
- **Used by**: explicitCandidateLaurentEvalThree_map_complex, explicitCandidateLaurentEvalComplexThree_coeff, explicitCandidateLaurentEvalComplexThree_observed_coefficients, modularPolynomialThreeDifferenceLaurentEval_eq
- **Visibility**: private
- **Lines**: 676–679 (def, 4 lines)
- **Notes**: none

### `theorem explicitCandidateLaurentEvalThree_map_complex` (private)
- **Type**: `laurentSeriesMapRingHom (Int.castRingHom ℂ) explicitCandidateLaurentEvalThree = explicitCandidateLaurentEvalComplexThree`
- **What**: The complex candidate evaluation is the base change of the integral one — so integer coefficient identities transfer to ℂ.
- **How**: Instance of `bivariateLaurentEval_map` with the two series identifications `sigmaLaurentSeriesThree_map_complex` and `widthLaurentSeriesThree_map_complex`.
- **Hypotheses**: none.
- **Uses from project**: [laurentSeriesMapRingHom, explicitCandidateLaurentEvalThree, explicitCandidateLaurentEvalComplexThree, bivariateLaurentEval_map, sigmaLaurentSeriesThree_map_complex, widthLaurentSeriesThree_map_complex]
- **Used by**: explicitCandidateLaurentEvalComplexThree_coeff
- **Visibility**: private
- **Lines**: 681–687 (proof 4 lines)
- **Notes**: none

### `theorem explicitCandidateLaurentEvalComplexThree_coeff` (private)
- **Type**: `(k : ℤ) : explicitCandidateLaurentEvalComplexThree.coeff k = (explicitCandidateLaurentEvalThree.coeff k : ℂ)`
- **What**: Coefficientwise form of the base-change identity: every complex coefficient of the candidate is the cast of the corresponding integer coefficient.
- **How**: Rewrite backwards along `explicitCandidateLaurentEvalThree_map_complex`; the mapped coefficient is definitionally the cast (`rfl`).
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateLaurentEvalComplexThree, explicitCandidateLaurentEvalThree, explicitCandidateLaurentEvalThree_map_complex]
- **Used by**: explicitCandidateLaurentEvalComplexThree_observed_coefficients
- **Visibility**: private
- **Lines**: 689–693 (proof 3 lines)
- **Notes**: none

### `theorem explicitCandidateLaurentEvalComplexThree_observed_coefficients` (private)
- **Type**: 10-fold conjunction: `explicitCandidateLaurentEvalComplexThree.coeff k = 0` for k ∈ {0, −9, −12, −18, −21, −24, −27, −30, −33, −36}
- **What**: The ten observed coefficients of the complex candidate evaluation vanish — the complex transfer of the kernel-certified integer vanishing.
- **How**: `simpa` with `explicitCandidateLaurentEvalComplexThree_coeff` and `Int.cast_eq_zero` from the integral version `explicitCandidateLaurentEvalThree_observed_coefficients`.
- **Hypotheses**: none.
- **Uses from project**: [explicitCandidateLaurentEvalComplexThree, explicitCandidateLaurentEvalComplexThree_coeff, explicitCandidateLaurentEvalThree_observed_coefficients]
- **Used by**: modularPolynomialThreeDifference_observed_coefficients
- **Visibility**: private
- **Lines**: 695–707 (proof 3 lines)
- **Notes**: none

### `theorem modularPolynomialC_three_laurent_root` (private)
- **Type**: `(modularPolynomialC 3).eval₂ (eval₂RingHom C (laurentqExpansion 3 j)) (transformedJSeries (zeta 3) (sigmaZero 3)) = 0`
- **What**: The transformed j-series at σ₀ is a root of the complex modular polynomial Φ₃^ℂ(·, J): the defining product formula of Φ₃ has the σ₀-factor vanish identically.
- **How**: Rewrite via the project identity `formalCoxPolynomial_eq_modularPolynomialC_map_j` (Φ₃^ℂ mapped along J equals the formal Cox product ∏_σ (X − transformedJSeries σ)), then `Polynomial.eval_prod` and `Finset.prod_eq_zero` at the factor σ = σ₀, which evaluates to T − T = 0.
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialC, laurentqExpansion, j, transformedJSeries, zeta, sigmaZero, formalCoxPolynomial, formalCoxPolynomial_eq_modularPolynomialC_map_j]
- **Used by**: modularPolynomialThreeDifferenceLaurentEval_eq
- **Visibility**: private
- **Lines**: 709–720 (proof 11 lines)
- **Notes**: none

### `theorem transformedJSeries_three_sigmaZero_order` (private)
- **Type**: `(transformedJSeries (zeta 3) (sigmaZero 3)).order = -9`
- **What**: The transformed j-series at the level-3 σ₀ matrix has a pole of order 9 (its q-expansion is essentially j(q⁹)).
- **How**: Project lemma `transformedJSeries_order` (order = −(a² / m) style formula) with ζ₃ ≠ 0 from `zeta_isPrimitiveRoot`, then `norm_num` on the σ₀ entries.
- **Hypotheses**: none.
- **Uses from project**: [transformedJSeries, zeta, sigmaZero, transformedJSeries_order, zeta_isPrimitiveRoot]
- **Used by**: modularPolynomialThreeDifference_eq_zero
- **Visibility**: private
- **Lines**: 722–726 (proof 4 lines)
- **Notes**: none

### `theorem transformedJSeries_three_sigmaZero_leadingCoeff` (private)
- **Type**: `(transformedJSeries (zeta 3) (sigmaZero 3)).leadingCoeff = 1`
- **What**: The transformed j-series at σ₀ has leading coefficient 1 (the root-of-unity factor is trivial for σ₀ since b = 0).
- **How**: Project lemma `transformedJSeries_leadingCoeff` with ζ₃ ≠ 0, then `norm_num` on σ₀.
- **Hypotheses**: none.
- **Uses from project**: [transformedJSeries, zeta, sigmaZero, transformedJSeries_leadingCoeff, zeta_isPrimitiveRoot]
- **Used by**: modularPolynomialThreeDifference_eq_zero
- **Visibility**: private
- **Lines**: 728–733 (proof 4 lines)
- **Notes**: none

### `theorem laurentqExpansion_j_order_three` (private)
- **Type**: `(laurentqExpansion 3 j).order = -3`
- **What**: The width-3 Laurent q-expansion of j has order −3 (simple pole in q^{1/3}, i.e. pole of order 3 in the width-3 variable).
- **How**: Specialise the project lemma `laurentqExpansion_j_order_widthM` to m = 3 and normalise the cast.
- **Hypotheses**: none.
- **Uses from project**: [laurentqExpansion, j, laurentqExpansion_j_order_widthM]
- **Used by**: modularPolynomialThreeDifference_eq_zero
- **Visibility**: private
- **Lines**: 735–739 (proof 4 lines)
- **Notes**: none

### `theorem laurentqExpansion_j_leadingCoeff_three` (private)
- **Type**: `(laurentqExpansion 3 j).leadingCoeff = 1`
- **What**: The width-3 Laurent q-expansion of j has leading coefficient 1.
- **How**: Specialise `laurentqExpansion_j_leadingCoeff_widthM` to m = 3.
- **Hypotheses**: none.
- **Uses from project**: [laurentqExpansion, j, laurentqExpansion_j_leadingCoeff_widthM]
- **Used by**: modularPolynomialThreeDifference_eq_zero
- **Visibility**: private
- **Lines**: 741–745 (proof 4 lines)
- **Notes**: none

### `def modularPolynomialThreeComplexExplicit` (private)
- **Type**: `BivariatePolynomial ℂ`
- **What**: The complexification of Cox's explicit polynomial: modularPolynomialThreeExplicit with coefficients cast into ℂ.
- **How**: `BivariatePolynomial.map (Int.castRingHom ℂ)`.
- **Hypotheses**: none.
- **Uses from project**: [BivariatePolynomial.map, modularPolynomialThreeExplicit]
- **Used by**: modularPolynomialThreeDifference, modularPolynomialThreeComplexExplicit_monic, modularPolynomialThreeComplexExplicit_natDegree, modularPolynomialThreeComplexExplicit_swap, modularPolynomialC_three_eq_explicit
- **Visibility**: private
- **Lines**: 747–748 (def, 2 lines)
- **Notes**: none

### `def modularPolynomialThreeDifference` (private)
- **Type**: `BivariatePolynomial ℂ`
- **What**: The defect Δ := Φ₃^ℂ − Φ₃^explicit,ℂ, the difference between the abstractly constructed complex modular polynomial and Cox's explicit formula; the goal is Δ = 0.
- **How**: Subtraction of the two bivariate polynomials.
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialC, modularPolynomialThreeComplexExplicit]
- **Used by**: modularPolynomialThreeDifference_swap, modularPolynomialThreeDifference_natDegree_le, modularPolynomialThreeDifference_inner_natDegree_le, modularPolynomialThreeDifferenceLaurentEval, modularPolynomialThreeDifferenceLaurentEval_eq, modularPolynomialThreeDifference_eq_zero, modularPolynomialC_three_eq_explicit
- **Visibility**: private
- **Lines**: 750–751 (def, 2 lines)
- **Notes**: none

### `theorem modularPolynomialC_three_natDegree` (private)
- **Type**: `(modularPolynomialC 3).natDegree = 4`
- **What**: The complex level-3 modular polynomial has X-degree 4, since there are exactly 4 Cox matrices of prime determinant 3 (1 + p for p = 3).
- **How**: Project formula `modularPolynomialC_natDegree` (degree = number of Cox matrices) plus the cardinality computation via `primeCoxMatrixEquiv` (CoxMatrix p ≃ Fin (p+1)).
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialC, modularPolynomialC_natDegree, primeCoxMatrixEquiv]
- **Used by**: modularPolynomialThreeDifference_natDegree_le
- **Visibility**: private
- **Lines**: 753–758 (proof 5 lines)
- **Notes**: none

### `theorem modularPolynomialThreeComplexExplicit_monic` (private)
- **Type**: `modularPolynomialThreeComplexExplicit.Monic`
- **What**: The complexified explicit polynomial is monic in X.
- **How**: Monicity is preserved by the coefficient ring hom map (`Polynomial.Monic.map` applied to `modularPolynomialThreeExplicit_monic`).
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialThreeComplexExplicit, BivariatePolynomial.map, modularPolynomialThreeExplicit_monic]
- **Used by**: modularPolynomialThreeDifference_natDegree_le
- **Visibility**: private
- **Lines**: 760–764 (proof 4 lines)
- **Notes**: none

### `theorem modularPolynomialThreeComplexExplicit_natDegree` (private)
- **Type**: `modularPolynomialThreeComplexExplicit.natDegree = 4`
- **What**: The complexified explicit polynomial has X-degree 4.
- **How**: `Monic.natDegree_map` preserves the degree under the map, combined with the integral degree computation `modularPolynomialThreeExplicit_natDegree`.
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialThreeComplexExplicit, BivariatePolynomial.map, modularPolynomialThreeExplicit_monic, modularPolynomialThreeExplicit_natDegree]
- **Used by**: modularPolynomialThreeDifference_natDegree_le
- **Visibility**: private
- **Lines**: 766–771 (proof 5 lines)
- **Notes**: none

### `theorem modularPolynomialThreeComplexExplicit_swap` (private)
- **Type**: `Polynomial.Bivariate.swap modularPolynomialThreeComplexExplicit = modularPolynomialThreeComplexExplicit`
- **What**: The complexified explicit polynomial is X↔Y symmetric.
- **How**: Swap commutes with coefficient maps (`BivariatePolynomial.map_swap`) and the integral polynomial is symmetric (`modularPolynomialThreeExplicit_swap`).
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialThreeComplexExplicit, BivariatePolynomial.map_swap, modularPolynomialThreeExplicit_swap]
- **Used by**: modularPolynomialThreeDifference_swap
- **Visibility**: private
- **Lines**: 773–777 (proof 3 lines)
- **Notes**: none

### `theorem modularPolynomialThreeDifference_swap` (private)
- **Type**: `(hsymm : swap (modularPolynomialC 3) = modularPolynomialC 3) : swap modularPolynomialThreeDifference = modularPolynomialThreeDifference`
- **What**: Assuming the complex modular polynomial is symmetric, the defect Δ is symmetric (difference of two symmetric polynomials).
- **How**: `map_sub` for swap plus the two symmetry facts.
- **Hypotheses**: the complex level-3 modular polynomial is X↔Y symmetric (the file's standing hypothesis).
- **Uses from project**: [modularPolynomialThreeDifference, modularPolynomialC, modularPolynomialThreeComplexExplicit_swap]
- **Used by**: modularPolynomialThreeDifference_inner_natDegree_le, modularPolynomialThreeDifference_eq_zero
- **Visibility**: private
- **Lines**: 779–785 (proof 3 lines)
- **Notes**: none

### `theorem modularPolynomialThreeDifference_natDegree_le` (private)
- **Type**: `modularPolynomialThreeDifference.natDegree ≤ 3`
- **What**: The defect Δ has X-degree at most 3: the difference of two monic degree-4 polynomials loses the leading term.
- **How**: mathlib's `Polynomial.IsMonicOfDegree.natDegree_sub_lt` applied to the two IsMonicOfDegree-4 facts (from `modularPolynomialC_three_natDegree`/`modularPolynomialC_monic` and the explicit analogues).
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialThreeDifference, modularPolynomialC_three_natDegree, modularPolynomialC_monic, modularPolynomialThreeComplexExplicit_natDegree, modularPolynomialThreeComplexExplicit_monic]
- **Used by**: modularPolynomialThreeDifference_inner_natDegree_le, modularPolynomialThreeDifference_eq_zero
- **Visibility**: private
- **Lines**: 787–794 (proof 7 lines)
- **Notes**: none

### `theorem modularPolynomialThreeDifference_inner_natDegree_le` (private)
- **Type**: `(hsymm : swap (modularPolynomialC 3) = modularPolynomialC 3) (i : ℕ) : (modularPolynomialThreeDifference.coeff i).natDegree ≤ 3`
- **What**: Each X-coefficient of Δ has Y-degree at most 3: the symmetry of Δ transports the outer degree bound to the inner variable, so Δ has bidegree ≤ (3,3).
- **How**: For n > 3, express the (i,n) coefficient via `BivariatePolynomial.coeff_coeff_swap` and the symmetry `modularPolynomialThreeDifference_swap`, then kill it with `Polynomial.coeff_eq_zero_of_natDegree_lt` from the outer bound `modularPolynomialThreeDifference_natDegree_le`.
- **Hypotheses**: symmetry of the complex level-3 modular polynomial.
- **Uses from project**: [modularPolynomialThreeDifference, modularPolynomialC, BivariatePolynomial.coeff_coeff_swap, modularPolynomialThreeDifference_swap, modularPolynomialThreeDifference_natDegree_le]
- **Used by**: modularPolynomialThreeDifference_eq_zero
- **Visibility**: private
- **Lines**: 796–811 (proof 14 lines)
- **Notes**: none

### `def modularPolynomialThreeDifferenceLaurentEval` (private)
- **Type**: `LaurentSeries ℂ`
- **What**: The defect Δ evaluated at the pair of Laurent series (T, J) = (transformed j-series at σ₀, width-3 expansion of j).
- **How**: Nested `eval₂RingHom` as for the candidate.
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialThreeDifference, laurentqExpansion, j, transformedJSeries, zeta, sigmaZero]
- **Used by**: modularPolynomialThreeDifferenceLaurentEval_eq, modularPolynomialThreeDifference_observed_coefficients, modularPolynomialThreeDifference_eq_zero
- **Visibility**: private
- **Lines**: 813–816 (def, 4 lines)
- **Notes**: none

### `theorem modularPolynomialThreeDifferenceLaurentEval_eq` (private)
- **Type**: `modularPolynomialThreeDifferenceLaurentEval = -explicitCandidateLaurentEvalComplexThree`
- **What**: Since the transformed j-series is a root of Φ₃^ℂ, the evaluation of Δ = Φ₃^ℂ − explicit reduces to minus the evaluation of the explicit candidate.
- **How**: `Polynomial.eval₂_sub` and `modularPolynomialC_three_laurent_root` give 0 − candidate.
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialThreeDifferenceLaurentEval, modularPolynomialThreeDifference, modularPolynomialC_three_laurent_root, explicitCandidateLaurentEvalComplexThree]
- **Used by**: modularPolynomialThreeDifference_observed_coefficients
- **Visibility**: private
- **Lines**: 818–824 (proof 6 lines)
- **Notes**: none

### `theorem modularPolynomialThreeDifference_observed_coefficients` (private)
- **Type**: 10-fold conjunction: `modularPolynomialThreeDifferenceLaurentEval.coeff k = 0` for k ∈ {0, −9, −12, −18, −21, −24, −27, −30, −33, −36}
- **What**: The ten observed Laurent coefficients of the evaluated defect Δ(T,J) vanish — precisely the input the symmetric-cubic vanishing criterion needs.
- **How**: Negate the complex candidate vanishing (`explicitCandidateLaurentEvalComplexThree_observed_coefficients`) through `modularPolynomialThreeDifferenceLaurentEval_eq` using `HahnSeries.coeff_neg`, `neg_eq_zero`.
- **Hypotheses**: none.
- **Uses from project**: [modularPolynomialThreeDifferenceLaurentEval, modularPolynomialThreeDifferenceLaurentEval_eq, explicitCandidateLaurentEvalComplexThree_observed_coefficients]
- **Used by**: modularPolynomialThreeDifference_eq_zero
- **Visibility**: private
- **Lines**: 826–839 (proof 4 lines)
- **Notes**: none

### `theorem modularPolynomialThreeDifference_eq_zero` (private)
- **Type**: `(hsymm : swap (modularPolynomialC 3) = modularPolynomialC 3) : modularPolynomialThreeDifference = 0`
- **What**: The heart of the argument: a symmetric bivariate polynomial of bidegree ≤ (3,3) whose Laurent evaluation at (T, J) — with orders (−9, −3) and unit leading coefficients — has the ten observed coefficients zero must itself be zero; hence Δ = 0.
- **How**: Apply the imported criterion `symmetric_bidegree_three_eq_zero_of_laurent_coeff` (from SymmetricCubicLaurent) with the eight side conditions: orders (`transformedJSeries_three_sigmaZero_order`, `laurentqExpansion_j_order_three`), leading coefficients, the two degree bounds, symmetry, and the observed coefficient vanishing.
- **Hypotheses**: symmetry of the complex level-3 modular polynomial.
- **Uses from project**: [modularPolynomialThreeDifference, modularPolynomialC, symmetric_bidegree_three_eq_zero_of_laurent_coeff, transformedJSeries, zeta, sigmaZero, laurentqExpansion, j, transformedJSeries_three_sigmaZero_order, laurentqExpansion_j_order_three, transformedJSeries_three_sigmaZero_leadingCoeff, laurentqExpansion_j_leadingCoeff_three, modularPolynomialThreeDifference_natDegree_le, modularPolynomialThreeDifference_inner_natDegree_le, modularPolynomialThreeDifference_swap, modularPolynomialThreeDifferenceLaurentEval, modularPolynomialThreeDifference_observed_coefficients]
- **Used by**: modularPolynomialC_three_eq_explicit
- **Visibility**: private
- **Lines**: 841–856 (proof 15 lines)
- **Notes**: none

### `theorem modularPolynomialC_three_eq_explicit` (private)
- **Type**: `(hsymm : swap (modularPolynomialC 3) = modularPolynomialC 3) : modularPolynomialC 3 = modularPolynomialThreeComplexExplicit`
- **What**: The complex level-3 modular polynomial equals the complexified Cox explicit polynomial (assuming symmetry).
- **How**: `sub_eq_zero` applied to `modularPolynomialThreeDifference_eq_zero`.
- **Hypotheses**: symmetry of the complex level-3 modular polynomial.
- **Uses from project**: [modularPolynomialC, modularPolynomialThreeComplexExplicit, modularPolynomialThreeDifference, modularPolynomialThreeDifference_eq_zero]
- **Used by**: modularPolynomial_three_of_complex_swap
- **Visibility**: private
- **Lines**: 858–863 (proof 3 lines)
- **Notes**: none

### `theorem modularPolynomial_three_of_complex_swap`
- **Type**: `(hsymm : Polynomial.Bivariate.swap (modularPolynomialC (3 : ℕ+)) = modularPolynomialC (3 : ℕ+)) : modularPolynomial (3 : ℕ+) = modularPolynomialThreeExplicit`
- **What**: Main public result: if the complex level-three modular polynomial is X↔Y symmetric, then the integral level-three modular polynomial equals Cox's explicit polynomial (eq. (11.22)).
- **How**: The complexification of the integral modular polynomial is Φ₃^ℂ (`modularPolynomial_map_complex`), which by `modularPolynomialC_three_eq_explicit` equals the complexified explicit polynomial; conclude by injectivity of the coefficient cast ℤ → ℂ at both polynomial levels (`Polynomial.map_injective` with `Int.cast_injective`, twice).
- **Hypotheses**: symmetry of the complex level-3 modular polynomial (expected to be discharged elsewhere in the project).
- **Uses from project**: [modularPolynomial, modularPolynomialC, modularPolynomialThreeExplicit, BivariatePolynomial.map, modularPolynomial_map_complex, modularPolynomialC_three_eq_explicit]
- **Used by**: unused in file (public entry point)
- **Visibility**: public
- **Lines**: 865–876 (proof 11 lines)
- **Notes**: one of only two public declarations; has docstring

### File Summary
- Total declarations: 108 (24 defs, 84 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): modularPolynomialThreeExplicit, qjCoeffTableThree, explicitCoeffThree, jetMul, jetPow, jetShift, jetExpand, sigmaJetThree, widthJetThree, explicitCandidateClearedJetTermThree, explicitCandidateClearedJetRowThree, explicitCandidateClearedJetThree, qjIntegralPowerSeriesThree, sigmaPowerSeriesThree, widthPowerSeriesThree, sigmaLaurentSeriesThree, widthLaurentSeriesThree, explicitCandidateClearedPowerSeriesThree, explicitCandidateLaurentEvalThree, explicitCandidateLaurentEvalComplexThree, modularPolynomialThreeComplexExplicit, modularPolynomialThreeDifference, modularPolynomialThreeDifferenceLaurentEval
- Unused declarations (not used by anything in this file): modularPolynomial_three_of_complex_swap (public entry point)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: explicitCandidateLaurentEvalThree_observed_coefficients (39 lines), bivariateLaurentEval_map (36 lines)

Additional file-level notes:
- Heavy use of `decide +kernel` (30 declarations): all numerical certificates are kernel-reduced, no `native_decide`; the n = 18 and n = 15 coefficients are split into per-row / per-term / split-range sub-lemmas to keep each kernel reduction tractable.
- The file's main theorem is conditional on the symmetry hypothesis `swap (modularPolynomialC 3) = modularPolynomialC 3`, threaded through 5 declarations.
- `bivariateLaurentEval_map` is fully generic over ring homs and could be moved next to `laurentSeriesMapRingHom` in XYin/PhD/Cox/LaurentPolynomialEvaluation.lean.
- The jet infrastructure (jetMul/jetPow/jetShift/jetExpand plus the three soundness lemmas hard-coded to the window n < 37) duplicates a pattern likely needed for other levels; candidates for generalisation and extraction.
