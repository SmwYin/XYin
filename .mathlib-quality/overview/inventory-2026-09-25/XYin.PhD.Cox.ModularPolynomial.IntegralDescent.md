# Inventory: XYin/PhD/Cox/ModularPolynomial/IntegralDescent.lean  (305 lines)

Proves Cox Theorem 11.18(i): the complex modular polynomial `Φ_m` has integer coefficients. Ingredients: the elementary Hasse `q`-expansion principle (a polynomial `P` with `P(j)` having integral Laurent coefficients lies in `ℤ[X]`), the identification of the width-`m` Laurent expansion of each `coxPhiFunction` coefficient with the corresponding coefficient of the formal Cox product (Cox (11.13)), the Galois-descent integrality of those formal coefficients (`formalCoxPolynomial_coeff_isInteger`), and a lift through `Polynomial.lifts`. Defines `modularPolynomial m : ℤ[X][Y]`.

## Declarations

### `private lemma Cox.laurentqExpansion_j_pow_aux`
- **Type**: `(n : ℕ) : laurentqExpansion 1 (fun τ ↦ j τ ^ n) = (laurentqExpansion 1 j) ^ n`
- **What**: The width-1 Laurent expansion of `j^n` is the `n`-th power of that of `j`.
- **How**: `laurentqExpansion_finset_prod` over `Finset.range n` with the constant family `fun _ ↦ j` (cusp meromorphy from `j_cuspFunction_meromorphicAt`), then `Finset.prod_const`.
- **Hypotheses**: none.
- **Uses from project**: `laurentqExpansion`, `j`, `laurentqExpansion_finset_prod`, `j_cuspFunction_meromorphicAt`
- **Used by**: `laurentqExpansion_polynomialIn_j_aux`
- **Visibility**: private
- **Lines**: 25–29, proof body ≈ 3 lines
- **Notes**: DUPLICATE of `DiagonalLaurent.laurentqExpansion_j_pow_widthM` (DiagonalLaurent.lean:152–157) with width `1` instead of `m`. A general `laurentqExpansion_pow` is missing from LaurentQExpansion/Algebra.lean (which has `_add/_mul/_neg/_const/_zero/_one/_finset_sum/_finset_prod`, Algebra.lean:163–283, but no `_pow`/`_sub`).

### `private lemma Cox.polynomialIn_cuspMeromorphicAt_aux`
- **Type**: `(P : Polynomial ℂ) : MeromorphicAt (cuspFunction 1 (polynomialIn P j)) 0`
- **What**: Any polynomial in `j` is meromorphic at the width-1 cusp.
- **How**: Third component of `CuspData.polynomialIn` applied to `j_levelOneCuspData`, at `γ = 1`.
- **Hypotheses**: none.
- **Uses from project**: `polynomialIn`, `j`, `j_levelOneCuspData`, `CuspData.polynomialIn`
- **Used by**: `laurentqExpansion_polynomialIn_j_aux`
- **Visibility**: private
- **Lines**: 31–33, proof body ≈ 1 line
- **Notes**: DUPLICATE of `DiagonalLaurent.polynomialIn_widthM_cuspMeromorphicAt` (DiagonalLaurent.lean:159–161).

### `private lemma Cox.laurentqExpansion_polynomialIn_j_aux`
- **Type**: `(P : Polynomial ℂ) : laurentqExpansion 1 (polynomialIn P j) = P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion 1 j)`
- **What**: Laurent expansion commutes with evaluating a polynomial at `j`: the expansion of `P(j)` is `P` evaluated at the expansion of `j`.
- **How**: `Polynomial.induction_on'`; the `add` case uses `laurentqExpansion_add`, the `monomial` case `laurentqExpansion_mul` + `laurentqExpansion_const` + `laurentqExpansion_j_pow_aux`, with cusp meromorphy of each piece from `polynomialIn_cuspMeromorphicAt_aux`.
- **Hypotheses**: none.
- **Uses from project**: `laurentqExpansion`, `polynomialIn`, `j`, `laurentqExpansion_add`, `laurentqExpansion_mul`, `laurentqExpansion_const`, `laurentqExpansion_j_pow_aux`, `polynomialIn_cuspMeromorphicAt_aux`, `j_levelOneCuspData`, `CuspData.polynomialIn`
- **Used by**: `leadingCoeff_eq_int_of_integer_laurent_aux`, `eraseLead_integer_laurent_aux`
- **Visibility**: private
- **Lines**: 35–52, proof body ≈ 15 lines
- **Notes**: VERBATIM DUPLICATE (width `1` ↔ `m`) of `DiagonalLaurent.laurentqExpansion_polynomialIn_j_widthM` (DiagonalLaurent.lean:164–185). Single replacement for both (and for L25–33 / DiagonalLaurent.lean:152–161): `theorem laurentqExpansion_polynomialIn {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) (P : Polynomial ℂ) : laurentqExpansion h (polynomialIn P f) = P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion h f)` in LaurentQExpansion/Algebra.lean (its proof is this one with `j`, `1` generalized; the needed closure `MeromorphicAt (cuspFunction h (polynomialIn P f)) 0` follows from `meromorphicAt_cuspFunction_finset_sum/_mul/_const`). Better still: bundle `laurentqExpansion h` as a `RingHom` on a `cuspMeromorphicSubring h` and use mathlib `Polynomial.hom_eval₂`.

### `private lemma Cox.laurentqExpansion_j_order_aux`
- **Type**: `(laurentqExpansion 1 j).order = -1`
- **What**: The Laurent expansion of `j` has order `-1` (simple pole at the cusp).
- **How**: `laurentqExpansion.poleOrder_to_order` with `j_poleOrder = 1`; `omega`.
- **Hypotheses**: none.
- **Uses from project**: `laurentqExpansion`, `j`, `laurentqExpansion.poleOrder_to_order`, `j_cuspFunction_meromorphicAt`, `j_poleOrder`
- **Used by**: `laurentqExpansion_j_leadingCoeff_aux`, `eval₂_laurentqExpansion_j_coeff_neg_natDegree_aux`
- **Visibility**: private
- **Lines**: 54–59, proof body ≈ 4 lines
- **Notes**: DUPLICATE of `DiagonalLaurent.laurentqExpansion_j_order_widthM` (DiagonalLaurent.lean:31–40, public) at `m = 1`.

### `private lemma Cox.laurentqExpansion_j_leadingCoeff_aux`
- **Type**: `(laurentqExpansion 1 j).leadingCoeff = 1`
- **What**: The leading Laurent coefficient of `j` (at `q^{-1}`) is `1`.
- **How**: `HahnSeries.leadingCoeff_eq` (Mathlib/RingTheory/HahnSeries/Basic.lean:416) + the order lemma + `jIntCoeff_spec (-1)` and `jIntCoeff_neg_one`.
- **Hypotheses**: none.
- **Uses from project**: `laurentqExpansion`, `j`, `laurentqExpansion_j_order_aux`, `jIntCoeff_neg_one`, `jIntCoeff_spec`
- **Used by**: `eval₂_laurentqExpansion_j_coeff_neg_natDegree_aux`
- **Visibility**: private
- **Lines**: 61–64, proof body ≈ 2 lines
- **Notes**: DUPLICATE of `DiagonalLaurent.laurentqExpansion_j_leadingCoeff_widthM` (DiagonalLaurent.lean:43–55) at `m = 1`; also `jFunction/qexp_coeffs.lean:144 j_laurentQExpansion_coeff_neg_one : (laurentqExpansion 1 j).coeff (-1) = 1` states the coefficient directly.

### `private lemma Cox.eval₂_laurentqExpansion_j_coeff_neg_natDegree_aux`
- **Type**: `(P : Polynomial ℂ) : (P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion 1 j)).coeff (-(P.natDegree : ℤ)) = P.leadingCoeff`
- **What**: The coefficient of `q^{-deg P}` in `P(J)` is the leading coefficient of `P` (since `J = q^{-1} + …`).
- **How**: `polynomial_eval₂_laurentSeries_coeff` (LaurentPolynomialEvaluation.lean:113) with `w = 1`, using the order and leading-coefficient lemmas.
- **Hypotheses**: none.
- **Uses from project**: `laurentqExpansion`, `j`, `polynomial_eval₂_laurentSeries_coeff`, `laurentqExpansion_j_order_aux`, `laurentqExpansion_j_leadingCoeff_aux`
- **Used by**: `leadingCoeff_eq_int_of_integer_laurent_aux`
- **Visibility**: private
- **Lines**: 66–70, proof body ≈ 2 lines
- **Notes**: DUPLICATE of `DiagonalLaurent.eval₂_laurentqExpansion_j_coeff_widthM` (DiagonalLaurent.lean:219–224) at `m = 1`.

### `private def Cox.integerCoeffLaurentSeries`
- **Type**: `Subring (LaurentSeries ℂ)` with carrier `{F | ∀ n, F.coeff n ∈ (Int.castRingHom ℂ).range}`
- **What**: The subring of complex Laurent series all of whose coefficients are (images of) integers.
- **How**: Closure under `0, 1, +, -, *` from `HahnSeries.coeff_add/_neg/_mul/_one` and `Subring.sum_mem`/`mul_mem` in the range subring.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: `laurentqExpansion_j_mem_integerCoeffLaurentSeries`, `intCast_C_mem_integerCoeffLaurentSeries`, `eraseLead_integer_laurent_aux`
- **Visibility**: private
- **Lines**: 72–94, proof body ≈ 21 lines
- **Notes**: Hand-rolled. No mathlib analogue found (searched RingTheory/HahnSeries for `Subring`, `mapRingHom`, coefficients-in-subring; only `HahnSeries.cardSuppLTSubring` (Cardinal.lean:190) and the unbundled `HahnSeries.map` (Basic.lean:143) with `HahnSeries.map_add/map_mul/map_one` (Addition.lean:128, Multiplication.lean:406/103)). Generalizes to `HahnSeries.coeffSubring (S : Subring R) : Subring (HahnSeries Γ R)`; equivalently the range of `HahnSeries.map (S.subtype)`. PR candidate.

### `private lemma Cox.laurentqExpansion_j_mem_integerCoeffLaurentSeries`
- **Type**: `laurentqExpansion 1 j ∈ integerCoeffLaurentSeries`
- **What**: The `q`-expansion of `j` has integer coefficients.
- **How**: `j_laurentQExpansion_isIntegral` coefficientwise.
- **Hypotheses**: none.
- **Uses from project**: `laurentqExpansion`, `j`, `integerCoeffLaurentSeries`, `j_laurentQExpansion_isIntegral`
- **Used by**: `eraseLead_integer_laurent_aux`
- **Visibility**: private
- **Lines**: 96–100, proof body ≈ 3 lines
- **Notes**: —

### `private lemma Cox.intCast_C_mem_integerCoeffLaurentSeries`
- **Type**: `(z : ℤ) : HahnSeries.C (z : ℂ) ∈ integerCoeffLaurentSeries`
- **What**: Integer constants lie in the integral subring.
- **How**: `map_intCast` + `intCast_mem` (any subring contains the integers).
- **Hypotheses**: none.
- **Uses from project**: `integerCoeffLaurentSeries`
- **Used by**: `eraseLead_integer_laurent_aux`
- **Visibility**: private
- **Lines**: 102–104, proof body ≈ 1 line
- **Notes**: —

### `private lemma Cox.leadingCoeff_eq_int_of_integer_laurent_aux`
- **Type**: `{P : Polynomial ℂ} (hint : ∀ n : ℤ, ∃ k : ℤ, (laurentqExpansion 1 (polynomialIn P j)).coeff n = (k : ℂ)) : ∃ k : ℤ, P.leadingCoeff = (k : ℂ)`
- **What**: If `P(j)` has an integral `q`-expansion then the leading coefficient of `P` is an integer.
- **How**: Read off the coefficient at `q^{-deg P}` using `laurentqExpansion_polynomialIn_j_aux` and `eval₂_laurentqExpansion_j_coeff_neg_natDegree_aux`.
- **Hypotheses**: integrality of all Laurent coefficients of `P(j)`.
- **Uses from project**: `laurentqExpansion`, `polynomialIn`, `j`, `laurentqExpansion_polynomialIn_j_aux`, `eval₂_laurentqExpansion_j_coeff_neg_natDegree_aux`
- **Used by**: `hasse_qExpansion_principle`
- **Visibility**: private
- **Lines**: 106–114, proof body ≈ 5 lines
- **Notes**: —

### `private lemma Cox.eraseLead_integer_laurent_aux`
- **Type**: `{P : Polynomial ℂ} {k : ℤ} (hint : ∀ n : ℤ, ∃ z : ℤ, (laurentqExpansion 1 (polynomialIn P j)).coeff n = (z : ℂ)) (hleading : P.leadingCoeff = (k : ℂ)) (n : ℤ) : ∃ z : ℤ, (laurentqExpansion 1 (polynomialIn P.eraseLead j)).coeff n = (z : ℂ)`
- **What**: Removing the (integral) leading term of `P` preserves integrality of the `q`-expansion of `P(j)`.
- **How**: In the subring `integerCoeffLaurentSeries`: `P(J)` is a member (by `hint`), the leading term `C k · J^{deg P}` is a member (`intCast_C_mem`, `pow_mem` of `laurentqExpansion_j_mem`), and `P.eraseLead(J) = P(J) - C k · J^{deg}` by `Polynomial.self_sub_monomial_natDegree_leadingCoeff` (Mathlib/Algebra/Polynomial/EraseLead.lean:71), `eval₂_sub`, `eval₂_monomial`.
- **Hypotheses**: as stated.
- **Uses from project**: `laurentqExpansion`, `polynomialIn`, `j`, `integerCoeffLaurentSeries`, `laurentqExpansion_polynomialIn_j_aux`, `intCast_C_mem_integerCoeffLaurentSeries`, `laurentqExpansion_j_mem_integerCoeffLaurentSeries`
- **Used by**: `hasse_qExpansion_principle`
- **Visibility**: private
- **Lines**: 116–142, proof body ≈ 22 lines
- **Notes**: The three `∃ z, coeff = z` ↔ `∈ integerCoeffLaurentSeries` conversions (L124–127, L139–142, and L98–100) show the hypothesis `hint` should simply be stated as membership.

### `theorem Cox.hasse_qExpansion_principle`
- **Type**: `{P : Polynomial ℂ} (hint : ∀ n : ℤ, ∃ k : ℤ, (laurentqExpansion 1 (polynomialIn P j)).coeff n = (k : ℂ)) : ∃ Q : Polynomial ℤ, P = Q.map (Int.castRingHom ℂ)`
- **What**: Hasse's `q`-expansion principle (elementary form): a polynomial in `j` with integral `q`-expansion has integer coefficients.
- **How**: Strong induction on `natDegree P` (`Nat.strong_induction_on`): degree 0 via `Polynomial.eq_C_of_natDegree_eq_zero`; otherwise the leading coefficient is an integer (`leadingCoeff_eq_int_of_integer_laurent_aux`), `P.eraseLead` has smaller degree (`Polynomial.eraseLead_natDegree_le`) and integral expansion (`eraseLead_integer_laurent_aux`), and `Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff` (EraseLead.lean:61) reassembles `P`.
- **Hypotheses**: integrality of all Laurent coefficients of `P(j)`.
- **Uses from project**: `laurentqExpansion`, `polynomialIn`, `j`, `leadingCoeff_eq_int_of_integer_laurent_aux`, `eraseLead_integer_laurent_aux`
- **Used by**: `exists_modularPolynomialZ`
- **Visibility**: public
- **Lines**: 144–169, proof body ≈ 21 lines
- **Notes**: No external users. The conclusion is `P ∈ Polynomial.lifts (Int.castRingHom ℂ)` (`Polynomial.mem_lifts`, Lifts.lean:63); phrasing it so lets the induction use `Subsemiring.add_mem` and `Polynomial.monomial_mem_lifts` (Lifts.lean:120). mathlib's `Polynomial.induction_with_natDegree_le` (EraseLead.lean:319) is the packaged induction principle used here by hand.

### `private def Cox.coxNegativeRoot`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : ℍ → ℂ := -(fun τ ↦ j (σ.act τ))`
- **What**: The negated Cox root `-j(σ·τ)` (so that `X - j∘σ = X + C (coxNegativeRoot)` for Vieta).
- **How**: Pointwise negation.
- **Hypotheses**: none.
- **Uses from project**: `CoxMatrix`, `CoxMatrix.act`, `j`
- **Used by**: `coxNegativeRoot_cuspMeromorphicAt_aux`, `coxNegativeRoot_laurentqExpansion_aux`, `coxPhiFunction_coeff_laurentqExpansion_widthM`
- **Visibility**: private
- **Lines**: 171–172, proof body ≈ 0 lines
- **Notes**: Scaffolding for `Finset.prod_X_add_C_coeff`.

### `private def Cox.coxNegativeRootSeries`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : LaurentSeries ℂ := -transformedJSeries (zeta m) σ`
- **What**: The negated formal root series from Cox (11.13).
- **How**: Negation of `transformedJSeries`.
- **Hypotheses**: none.
- **Uses from project**: `CoxMatrix`, `transformedJSeries`, `zeta`
- **Used by**: `coxNegativeRoot_laurentqExpansion_aux`, `coxPhiFunction_coeff_laurentqExpansion_widthM`
- **Visibility**: private
- **Lines**: 174–175, proof body ≈ 0 lines
- **Notes**: —

### `private theorem Cox.coxNegativeRoot_cuspMeromorphicAt_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (coxNegativeRoot m σ)) 0`
- **What**: The negated root is width-`m` cusp-meromorphic.
- **How**: `meromorphicAt_cuspFunction_mul` with the constant `-1` and `coxRoot_cuspMeromorphicAt`.
- **Hypotheses**: none.
- **Uses from project**: `coxNegativeRoot`, `meromorphicAt_cuspFunction_mul`, `meromorphicAt_cuspFunction_const`, `coxRoot_cuspMeromorphicAt`, `CoxMatrix`
- **Used by**: `coxNegativeRoot_laurentqExpansion_aux`, `coxPhiFunction_coeff_laurentqExpansion_widthM`
- **Visibility**: private
- **Lines**: 177–183, proof body ≈ 4 lines
- **Notes**: Same `mul (const (-1))` negation trick as AnalyticSupport.lean:48–50; `meromorphicAt_cuspFunction_neg` is missing.

### `private theorem Cox.coxNegativeRoot_laurentqExpansion_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : laurentqExpansion ((m : ℕ) : ℝ) (coxNegativeRoot m σ) = coxNegativeRootSeries m σ`
- **What**: The width-`m` Laurent expansion of `-j(σ·τ)` is the negated formal root series.
- **How**: `laurentqExpansion_neg` and `laurentqExpansion_coxAction` (expansion of `j∘σ` is `transformedJSeries (zeta m) σ`).
- **Hypotheses**: none.
- **Uses from project**: `laurentqExpansion`, `coxNegativeRoot`, `coxNegativeRootSeries`, `laurentqExpansion_neg`, `coxRoot_cuspMeromorphicAt`, `laurentqExpansion_coxAction`, `CoxMatrix`
- **Used by**: `coxPhiFunction_coeff_laurentqExpansion_widthM`
- **Visibility**: private
- **Lines**: 185–191, proof body ≈ 4 lines
- **Notes**: —

### `theorem Cox.coxPhiFunction_coeff_laurentqExpansion_widthM`
- **Type**: `(m : ℕ+) (n : ℕ) : laurentqExpansion ((m : ℕ) : ℝ) ((coxPhiFunction m).coeff n) = (formalCoxPolynomial m (zeta m)).coeff n`
- **What**: Cox (11.13) coefficientwise: the width-`m` expansion of the `n`-th coefficient of `∏(X - j∘σ)` is the `n`-th coefficient of the formal product `∏(X - transformedJSeries)`.
- **How**: For `n ≤ |C(m)|`, Vieta (`Finset.prod_X_add_C_coeff`, Vieta.lean:67) on both sides expresses the coefficient as the elementary symmetric sum over `powersetCard (|C(m)| - n)` of products of negated roots; `laurentqExpansion_finset_sum` and `laurentqExpansion_finset_prod` distribute the expansion, and `coxNegativeRoot_laurentqExpansion_aux` matches factors. For `n > |C(m)|` both sides are `0` (`coeff_eq_zero_of_natDegree_lt`, `laurentqExpansion_zero`).
- **Hypotheses**: none.
- **Uses from project**: `laurentqExpansion`, `coxPhiFunction`, `formalCoxPolynomial`, `zeta`, `CoxMatrix`, `coxNegativeRoot`, `coxNegativeRootSeries`, `coxNegativeRoot_laurentqExpansion_aux`, `coxNegativeRoot_cuspMeromorphicAt_aux`, `laurentqExpansion_finset_sum`, `laurentqExpansion_finset_prod`, `meromorphicAt_cuspFunction_finset_prod`, `laurentqExpansion_zero`
- **Used by**: `coxPhiFunction_coeff_integerLaurent`
- **Visibility**: public
- **Lines**: 193–230, proof body ≈ 33 lines
- **Notes**: PROOF >30 LINES. `classical`. External user: DiagonalLaurent.lean:196 (`formalCoxPolynomial_eq_modularPolynomialC_map_j`). The Vieta expansion `hfunction` (L201–206) is verbatim Construction.lean:222–230. Cleaner: with `laurentqExpansion m` bundled as a ring hom `L` on the cusp-meromorphic subring, the whole statement is `Polynomial.map L (coxPhiFunction m) = formalCoxPolynomial m (zeta m)` by `Polynomial.map_prod`/`map_sub`, and the coefficient identity is `Polynomial.coeff_map`; or a direct lemma `laurentqExpansion_prod_X_sub_C_coeff (hf : ∀ i, MeromorphicAt (cuspFunction h (f i)) 0) : laurentqExpansion h ((∏ i, (X - C (f i))).coeff n) = (∏ i, (X - C (laurentqExpansion h (f i)))).coeff n`.

### `theorem Cox.coxPhiFunction_coeff_integerLaurent`
- **Type**: `(m : ℕ+) (n : ℕ) (k : ℤ) : ∃ z : ℤ, (laurentqExpansion 1 ((coxPhiFunction m).coeff n)).coeff k = (z : ℂ)`
- **What**: Every width-1 Laurent coefficient of every elementary symmetric function of the Cox roots is an integer (Galois descent from (11.13)).
- **How**: `laurentqExpansion_nat_mul_coeff` (Algebra.lean:384) identifies the width-1 coefficient `k` with the width-`m` coefficient `m·k` (needs width-1 cusp meromorphy and 1-periodicity); then `coxPhiFunction_coeff_laurentqExpansion_widthM` and `formalCoxPolynomial_coeff_isInteger`.
- **Hypotheses**: none.
- **Uses from project**: `laurentqExpansion`, `coxPhiFunction`, `formalCoxPolynomial_coeff_isInteger`, `laurentqExpansion_nat_mul_coeff`, `coxPhiFunction_coeff_widthOne_cuspMeromorphicAt`, `periodic_comp_of_slashInvariant_one`, `coxPhiFunction_coeff_slashInvariant`, `coxPhiFunction_coeff_laurentqExpansion_widthM`, `formalCoxPolynomial`, `zeta`
- **Used by**: `exists_modularPolynomialZ`
- **Visibility**: public
- **Lines**: 232–252, proof body ≈ 16 lines
- **Notes**: No external users.

### `private theorem Cox.bivariate_exists_of_coeff_lifts`
- **Type**: `(F : BivariatePolynomial ℂ) (hcoeff : ∀ n : ℕ, ∃ Q : Polynomial ℤ, F.coeff n = Q.map (Int.castRingHom ℂ)) : ∃ G : BivariatePolynomial ℤ, BivariatePolynomial.map (Int.castRingHom ℂ) G = F`
- **What**: A bivariate polynomial whose coefficient polynomials all lift to `ℤ[Y]` lifts to `ℤ[X][Y]`.
- **How**: `Polynomial.mem_lifts` + `Polynomial.lifts_iff_coeff_lifts` (Mathlib/Algebra/Polynomial/Lifts.lean:63,72) for `f := mapRingHom (Int.castRingHom ℂ)`.
- **Hypotheses**: as stated.
- **Uses from project**: `BivariatePolynomial`, `BivariatePolynomial.map`
- **Used by**: `exists_modularPolynomialZ`
- **Visibility**: private
- **Lines**: 254–261, proof body ≈ 3 lines
- **Notes**: One-line mathlib composition; fine as a private helper.

### `theorem Cox.modularPolynomialC_coeff_polynomialIn`
- **Type**: `(m : ℕ+) (n : ℕ) : polynomialIn ((modularPolynomialC m).coeff n) j = (coxPhiFunction m).coeff n`
- **What**: The `n`-th coefficient polynomial of `Φ_m`, evaluated at `j`, is the `n`-th function coefficient of the Cox product.
- **How**: Coefficient `n` of `modularPolynomialC_specializeY` plus `coxPhiFunction_coeff_apply` and `Polynomial.coeff_map`.
- **Hypotheses**: none.
- **Uses from project**: `polynomialIn`, `modularPolynomialC`, `j`, `coxPhiFunction`, `modularPolynomialC_specializeY`, `coxPhiFunction_coeff_apply`, `BivariatePolynomial.specializeY`
- **Used by**: `exists_modularPolynomialZ`
- **Visibility**: public
- **Lines**: 263–273, proof body ≈ 6 lines
- **Notes**: External user: DiagonalLaurent.lean:197. Uses only Construction.lean API and restates `Construction.coxCoefficientPolynomialAux_eval` canonically; belongs in Construction.lean.

### `theorem Cox.exists_modularPolynomialZ`
- **Type**: `(m : ℕ+) : ∃ Φ : BivariatePolynomial ℤ, BivariatePolynomial.map (Int.castRingHom ℂ) Φ = modularPolynomialC m`
- **What**: Cox Theorem 11.18(i): `Φ_m` descends to `ℤ[X, Y]`.
- **How**: `bivariate_exists_of_coeff_lifts`; each coefficient polynomial lifts by `hasse_qExpansion_principle`, whose hypothesis is `coxPhiFunction_coeff_integerLaurent` after rewriting with `modularPolynomialC_coeff_polynomialIn`.
- **Hypotheses**: none.
- **Uses from project**: `BivariatePolynomial`, `BivariatePolynomial.map`, `modularPolynomialC`, `bivariate_exists_of_coeff_lifts`, `hasse_qExpansion_principle`, `modularPolynomialC_coeff_polynomialIn`, `coxPhiFunction_coeff_integerLaurent`
- **Used by**: `modularPolynomial`, `modularPolynomial_map_complex`
- **Visibility**: public
- **Lines**: 275–284, proof body ≈ 5 lines
- **Notes**: No external users (consumed via `modularPolynomial`).

### `def Cox.modularPolynomial`
- **Type**: `(m : ℕ+) : BivariatePolynomial ℤ := (exists_modularPolynomialZ m).choose`
- **What**: The integral modular polynomial `Φ_m ∈ ℤ[X][Y]`.
- **How**: Choice.
- **Hypotheses**: none.
- **Uses from project**: `BivariatePolynomial`, `exists_modularPolynomialZ`
- **Used by**: `modularPolynomial_map_complex`, `modularPolynomial_monic`
- **Visibility**: public
- **Lines**: 286–288, proof body ≈ 0 lines
- **Notes**: Redundant `noncomputable`. Central downstream object: Arithmetic (18), Kronecker (6), LevelThree, KroneckerFrobenius, SingularModuli, Classification. Being `choose`-defined it is opaque; it is uniquely determined (injectivity of `Int.cast` coefficientwise), so a `modularPolynomial_unique` lemma or a definition via `Polynomial.lifts`' `Classical.choose` would be equivalent.

### `theorem Cox.modularPolynomial_map_complex`
- **Type**: `(m : ℕ+) : BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m) = modularPolynomialC m`
- **What**: The integral polynomial maps to the complex one.
- **How**: `choose_spec`.
- **Hypotheses**: none.
- **Uses from project**: `BivariatePolynomial.map`, `modularPolynomial`, `modularPolynomialC`, `exists_modularPolynomialZ`
- **Used by**: `modularPolynomial_monic`
- **Visibility**: public
- **Lines**: 290–293, proof body ≈ 1 line
- **Notes**: External: Arithmetic (9), SingularModuli, LevelThree, Kronecker, Classification.

### `theorem Cox.modularPolynomial_monic`
- **Type**: `(m : ℕ+) : (modularPolynomial m).Monic`
- **What**: The integral modular polynomial is monic in `X`.
- **How**: `Polynomial.monic_of_injective` (Mathlib/Algebra/Polynomial/Monic.lean:408) for the injective coefficient map `mapRingHom (Int.castRingHom ℂ)` (`Polynomial.map_injective`, Eval/Coeff.lean:103, + `Int.cast_injective`), using `modularPolynomialC_monic`.
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomial`, `BivariatePolynomial.map`, `modularPolynomial_map_complex`, `modularPolynomialC_monic`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 295–303, proof body ≈ 7 lines
- **Notes**: External: Arithmetic (1). mathlib `Polynomial.lifts_and_natDegree_eq_and_monic` (Lifts.lean:192) is the related "monic lift" statement.

## File Summary
- Total declarations: 24 (4 defs incl. 1 `Subring`, 20 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `integerCoeffLaurentSeries` (3), `coxNegativeRoot` (3), `laurentqExpansion_polynomialIn_j_aux` (2), `coxNegativeRoot_cuspMeromorphicAt_aux` (2)
- Unused declarations (not used by anything in this file): `modularPolynomial_monic` (used by Arithmetic.lean)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `coxPhiFunction_coeff_laurentqExpansion_widthM` (33 lines)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `bivariate_exists_of_coeff_lifts` (L254–261) = `Polynomial.mem_lifts` + `Polynomial.lifts_iff_coeff_lifts` (`Mathlib/Algebra/Polynomial/Lifts.lean:63,72`).
- `hasse_qExpansion_principle` (L145–169): the hand-rolled `eraseLead` strong induction is `Polynomial.induction_with_natDegree_le` (`Mathlib/Algebra/Polynomial/EraseLead.lean:319`); the conclusion is membership in `Polynomial.lifts (Int.castRingHom ℂ)` (Lifts.lean:60), a `Subsemiring`, so the inductive step is `Subsemiring.add_mem _ ih (Polynomial.monomial_mem_lifts _ ⟨k, rfl⟩)` (Lifts.lean:120).
- `modularPolynomial_monic` (L296–303): `Polynomial.monic_of_injective` (`Mathlib/Algebra/Polynomial/Monic.lean:408`) + `Polynomial.map_injective` (`Mathlib/Algebra/Polynomial/Eval/Coeff.lean:103`) — already used; fine.
- `integerCoeffLaurentSeries` (L72–94): no mathlib analogue (searched `Mathlib/RingTheory/HahnSeries/*` and `LaurentSeries.lean` for `Subring`, `mapRingHom`, `coeff … ∈`); only the unbundled `HahnSeries.map` (`HahnSeries/Basic.lean:143`) with `HahnSeries.map_add/_neg/_sub` (Addition.lean:128,384,403), `map_one/map_mul` (Multiplication.lean:103,406) exists. A general `HahnSeries.coeffSubring (S : Subring R) : Subring R⟦Γ⟧` (carrier `{x | ∀ g, x.coeff g ∈ S}`) is a natural PR and would replace L72–94 with `HahnSeries.coeffSubring (Int.castRingHom ℂ).range`.
- `laurentqExpansion_polynomialIn_j_aux` (L35–52): if `laurentqExpansion h` were a `RingHom` on a cusp-meromorphic subring, this is mathlib `Polynomial.hom_eval₂` / `Polynomial.eval₂_hom` (`Mathlib/Algebra/Polynomial/Eval/Coeff.lean:172,187`) with `polynomialIn P f = P.eval₂ (Pi.constRingHom …) f`-style rewriting.
### Missing API / repeated patterns
- DUPLICATION WITH DiagonalLaurent.lean STILL PRESENT (Sep 25): L25–29 ≡ DiagonalLaurent.lean:152–157 (`_j_pow`), L31–33 ≡ :159–161 (`polynomialIn_…cuspMeromorphicAt`), L35–52 ≡ :164–185 (`laurentqExpansion_polynomialIn_j_…`), L54–59 ≡ :31–40 (`_j_order_…`), L61–64 ≡ :43–55 (`_j_leadingCoeff_…`), L66–70 ≡ :219–224 (`eval₂_laurentqExpansion_j_coeff_…`); the only difference is the width (`1` vs `(m : ℕ) : ℝ`). DiagonalLaurent.lean imports `XYin.PhD.Cox.ModularPolynomial` (DiagonalLaurent.lean:12), so it could reuse public width-general versions placed here or, better, in LaurentQExpansion/Algebra.lean. The single lemma replacing L25–52 and DiagonalLaurent.lean:152–185: `theorem laurentqExpansion_polynomialIn {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) (P : Polynomial ℂ) : laurentqExpansion h (polynomialIn P f) = P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion h f)`, together with `laurentqExpansion_pow (hh) (hf) (n) : laurentqExpansion h (fun τ ↦ f τ ^ n) = laurentqExpansion h f ^ n` and `meromorphicAt_cuspFunction_polynomialIn (hf) (P) : MeromorphicAt (cuspFunction h (polynomialIn P f)) 0` in Algebra.lean. The order/leadingCoeff pair (L54–64) is `DiagonalLaurent.laurentqExpansion_j_order_widthM/_leadingCoeff_widthM` at `m = 1` (already public there; move them upstream to CoxMatrices/LaurentExpansion.lean or jFunction, where `jIntCoeff_spec` lives).
- Vieta `powersetCard` expansion of `coxPhiFunction` coefficients: L200–206 ≡ Construction.lean:222–230.
- `∃ z : ℤ, coeff = (z : ℂ)` ↔ subring membership conversions at L98–100, L124–127, L139–142, L237–239: state integrality as membership (or as `∈ (Int.castRingHom ℂ).range`) throughout, including `formalCoxPolynomial_coeff_isInteger` and `j_laurentQExpansion_isIntegral`.
- Missing: `laurentqExpansion_pow`, `laurentqExpansion_sub`, `meromorphicAt_cuspFunction_neg/_sub/_pow`.
### Junk candidates
- `laurentqExpansion_j_order_aux`, `laurentqExpansion_j_leadingCoeff_aux` (L54–64): subsumed by public DiagonalLaurent.lean:31–55 at `m = 1` (module order permitting) and by `qexp_coeffs.lean:144`.
- `coxNegativeRoot`/`coxNegativeRootSeries` (L171–175): Vieta scaffolding that disappears with a ring-hom/`Polynomial.map` formulation.
- No dead code, `#check`s, or commented blocks.
### Moral duplicates within this batch
- `modularPolynomialC_coeff_polynomialIn` (L265–273) ≡ `Construction.coxCoefficientPolynomialAux_eval` (Construction.lean:294–299) for the canonical `Φ_m`.
- `coxNegativeRoot_cuspMeromorphicAt_aux` (L177–183) ≡ the `n = 0` branch of `AnalyticSupport.coxLinearFactor_coeff_cuspMeromorphicAt` (AnalyticSupport.lean:47–50).
- All the DiagonalLaurent pairs listed above.
### Generalization notes
- L25–70 are all stated for `j` at width `1` but the proofs use only: cusp meromorphy of the function, `order = -w`, `leadingCoeff = 1`; they hold for any `f` with `MeromorphicAt (cuspFunction h f) 0` (and, for L54–70, `poleOrder h f = w`, leading coefficient `1`).
- `integerCoeffLaurentSeries` generalizes to any `Subring R` inside `HahnSeries Γ R` for any ordered `Γ`; `hasse_qExpansion_principle` generalizes to any `J : LaurentSeries K` with `J.order = -w < 0`, `J.leadingCoeff` a unit of a subring `S`, and all `J`-coefficients in `S`: `P(J) ∈ S⟦q⟧ ⇒ P ∈ S[X]` (this is the abstract Hasse principle; nothing about `j` is used beyond L96–100).
