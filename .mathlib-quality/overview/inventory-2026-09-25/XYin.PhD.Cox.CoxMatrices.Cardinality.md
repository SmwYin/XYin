# Inventory: XYin/PhD/Cox/CoxMatrices/Cardinality.lean  (278 lines)

Proves Cox's count `|C(m)| = m ∏_{p∣m}(1 + 1/p)` (the Dedekind ψ-function) by fibering `C(m)` over
the divisor `d`, counting each fiber as `(d/g)·φ(g)` with `g = gcd(m/d, d)`, packaging the divisor
sum as a multiplicative `ArithmeticFunction`, and evaluating it on prime powers. Everything except
the final theorem is private.

## Declarations

### `private theorem Cox.card_filter_range_coprime_mul_aux`
- **Type**: `(g k : ℕ) : ((Finset.range (k * g)).filter (g.Coprime ·)).card = k * g.totient`
- **What**: In `k` consecutive periods of length `g` there are `k·φ(g)` integers coprime to `g`.
- **How**: Induction on `k` with `Nat.count_eq_card_filter_range`, `Nat.count_add'`, periodicity `Nat.coprime_add_self_right`, base `Nat.totient_eq_card_coprime`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `card_coxFiber_aux`
- **Visibility**: private
- **Lines**: 23–31, proof ≈ 7 lines
- **Notes**: mathlib has the one-period version `Nat.filter_coprime_Ico_eq_totient` (Data/Nat/Totient.lean:79) via `Nat.filter_Ico_card_eq_of_periodic` (Data/Nat/Periodic.lean:61); no `k`-fold version found (searched `count_mul`, `filter_range_mul`, `periodic`). Mathlib-shaped as `Nat.card_filter_range_mul_of_periodic`.

### `private def Cox.coxFiberAux`
- **Type**: `(m : ℕ+) (d : ℕ) : Type` := `{b : Fin d // (Nat.gcd (m / d) d).Coprime b}`
- **What**: The fiber of `C(m) → divisors m`, `σ ↦ σ.d`: residues `b < d` with `gcd(gcd(m/d, d), b) = 1`.
- **How**: subtype of `Fin d`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `instance Fintype`, `card_coxFiber_aux`, `coxMatrixToFiberSigmaAux`, `fiberSigmaToCoxMatrixAux`, `coxMatrixEquivFiberSigmaAux`
- **Visibility**: private
- **Lines**: 33–34
- **Notes**: —

### `private instance Cox.instFintypeCoxFiberAux`
- **Type**: `(m) (d) : Fintype (coxFiberAux m d)`
- **What**: The fiber is finite.
- **How**: `inferInstanceAs` on the subtype.
- **Hypotheses**: none.
- **Uses from project**: [`coxFiberAux`]
- **Used by**: `card_coxFiber_aux`, `card_coxMatrix_eq_divisorSum_aux` (via `Fintype.card_sigma`)
- **Visibility**: private
- **Lines**: 36–38
- **Notes**: Would be found automatically if `coxFiberAux` were an `abbrev`.

### `private theorem Cox.card_coxFiber_aux`
- **Type**: `Fintype.card (coxFiberAux m d) = (d / Nat.gcd (m/d) d) * (Nat.gcd (m/d) d).totient`
- **What**: The fiber over `d` has `(d/g)·φ(g)` elements.
- **How**: `Fintype.card_subtype`, `Fin.sum_univ_eq_sum_range`, then `card_filter_range_coprime_mul_aux g (d/g)` with `d/g * g = d`.
- **Hypotheses**: none.
- **Uses from project**: [`coxFiberAux`, `card_filter_range_coprime_mul_aux`]
- **Used by**: `card_coxMatrix_eq_divisorSum_aux`
- **Visibility**: private
- **Lines**: 40–52, proof ≈ 9 lines
- **Notes**: Lines 49–51 convert `card_subtype` to `sum_filter` and back — pure `Fin`/`range` bookkeeping (a `Fintype.card_subtype_fin_eq_card_filter_range` helper would remove it).

### `private def Cox.coxMatrixToFiberSigmaAux`
- **Type**: `(σ : CoxMatrix m) : Σ d : {d // d ∈ m.divisors}, coxFiberAux m d`
- **What**: Sends `σ` to `(σ.d, σ.b)` in the fiber.
- **How**: `σ.d ∣ m`, `m / σ.d = σ.a` (`Nat.mul_div_left`), primitivity by gcd reassociation.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix` (fields `determinant`, `d_pos`, `b_lt`, `primitive`), `coxFiberAux`]
- **Used by**: `coxMatrixEquivFiberSigmaAux`
- **Visibility**: private
- **Lines**: 54–64
- **Notes**: Re-derives `σ.d ∣ m` and `m / σ.d = σ.a` (56–59) — missing `CoxMatrix.d_dvd`/`div_d`.

### `private def Cox.fiberSigmaToCoxMatrixAux`
- **Type**: `(x : Σ d : {d // d ∈ m.divisors}, coxFiberAux m d) : CoxMatrix m`
- **What**: Inverse: `(d, b) ↦ [[m/d, b],[0, d]]`.
- **How**: `Nat.div_mul_cancel`, `Nat.div_pos`, gcd reassociation.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix`, `coxFiberAux`]
- **Used by**: `coxMatrixEquivFiberSigmaAux`
- **Visibility**: private
- **Lines**: 66–83
- **Notes**: —

### `private def Cox.coxMatrixEquivFiberSigmaAux`
- **Type**: `(m) : CoxMatrix m ≃ Σ d : {d // d ∈ m.divisors}, coxFiberAux m d`
- **What**: `C(m)` is the disjoint union of its fibers over the divisors of `m`.
- **How**: `left_inv` via `CoxMatrix.toFin_injective` + `simp [hquot]`; `right_inv` by `rfl` after destructuring.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix`, `CoxMatrix.toFin`, `CoxMatrix.toFin_injective`, `coxMatrixToFiberSigmaAux`, `fiberSigmaToCoxMatrixAux`, `coxFiberAux`]
- **Used by**: `card_coxMatrix_eq_divisorSum_aux`
- **Visibility**: private
- **Lines**: 85–100
- **Notes**: Uses `toFin_injective` as ext (91); `hquot` (93–94) re-derived.

### `private theorem Cox.card_coxMatrix_eq_divisorSum_aux`
- **Type**: `Fintype.card (CoxMatrix m) = ∑ d ∈ m.divisors, (d / Nat.gcd (m/d) d) * (Nat.gcd (m/d) d).totient`
- **What**: `|C(m)| = Σ_{d∣m} (d/g)φ(g)`.
- **How**: `Fintype.card_congr`, `Fintype.card_sigma`, `Finset.sum_subtype`, `card_coxFiber_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix`, `coxMatrixEquivFiberSigmaAux`, `card_coxFiber_aux`]
- **Used by**: `card_coxMatrix`
- **Visibility**: private
- **Lines**: 102–111, proof ≈ 5 lines
- **Notes**: ℕ-valued exact formula, private; worth exposing.

### `private def Cox.coxDivisorTermAux`
- **Type**: `(n d : ℕ) : ℕ` := `(d / Nat.gcd (n/d) d) * (Nat.gcd (n/d) d).totient`
- **What**: The summand `T(n,d)`.
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `coxDivisorTerm_mul_of_coprime_aux`, `coxDivisorSumAux`, `coxDivisorTerm_prime_pow_of_lt_aux`, `coxDivisorTerm_prime_pow_self_aux`, `coxDivisorSumArithmeticFunction_mult_aux`
- **Visibility**: private
- **Lines**: 113–114
- **Notes**: —

### `private theorem Cox.coxDivisorTerm_mul_of_coprime_aux`
- **Type**: `(hmn : m.Coprime n) (hd : d ∣ m) (he : e ∣ n) : coxDivisorTermAux (m*n) (d*e) = coxDivisorTermAux m d * coxDivisorTermAux n e`
- **What**: The summand is multiplicative in coprime factorizations.
- **How**: `Nat.Coprime.gcd_mul`, `gcd_mul_right_cancel`, `gcd_mul_left_cancel`, `Nat.div_mul_div_comm`, `Nat.totient_mul`.
- **Hypotheses**: `m ⊥ n`, `d ∣ m`, `e ∣ n`.
- **Uses from project**: [`coxDivisorTermAux`]
- **Used by**: `coxDivisorSum_mul_of_coprime_aux`
- **Visibility**: private
- **Lines**: 116–138, proof ≈ 21 lines
- **Notes**: —

### `private def Cox.coxDivisorSumAux`
- **Type**: `(n : ℕ) : ℕ` := `∑ d ∈ n.divisors, coxDivisorTermAux n d`
- **What**: The divisor sum `Σ_{d∣n} T(n,d)` (= ψ(n)).
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: [`coxDivisorTermAux`]
- **Used by**: `coxDivisorSum_mul_of_coprime_aux`, `coxDivisorSum_prime_pow_aux`, `coxDivisorSumArithmeticFunctionAux`, `coxDivisorSumAF_apply_aux`, `coxDivisorSumArithmeticFunction_mult_aux`, `coxDivisorSum_eq_factorizationProd_aux`, `cast_coxDivisorSum_eq_eulerProduct_aux`, `card_coxMatrix`
- **Visibility**: private
- **Lines**: 140–141
- **Notes**: —

### `private theorem Cox.coxDivisorSum_mul_of_coprime_aux`
- **Type**: `(hmn : m.Coprime n) : coxDivisorSumAux (m*n) = coxDivisorSumAux m * coxDivisorSumAux n`
- **What**: The divisor sum is multiplicative.
- **How**: `Nat.Coprime.divisors_mul` (Finset.map over `attach` of a product), `Finset.sum_map`, `Finset.sum_attach`, `Finset.sum_product`, `Finset.sum_mul_sum`, then `coxDivisorTerm_mul_of_coprime_aux`.
- **Hypotheses**: `m ⊥ n`.
- **Uses from project**: [`coxDivisorSumAux`, `coxDivisorTerm_mul_of_coprime_aux`]
- **Used by**: `coxDivisorSumArithmeticFunction_mult_aux`
- **Visibility**: private
- **Lines**: 143–158, proof ≈ 14 lines
- **Notes**: Lines 148–152 fight the `attach.map` form of `Nat.Coprime.divisors_mul` (Data/Finset/NatDivisors.lean:65) with a `change`; a `Finset.sum_divisors_mul_of_coprime : ∑ d ∈ (m*n).divisors, f d = ∑ d ∈ m.divisors, ∑ e ∈ n.divisors, f (d*e)` helper would remove it (this is essentially mathlib's `ArithmeticFunction.IsMultiplicative.mul` unfolded, but the summand is not a Dirichlet convolution of one-variable functions).

### `private theorem Cox.coxDivisorTerm_prime_pow_of_lt_aux`
- **Type**: `(hp : p.Prime) (hie : i < e) : coxDivisorTermAux (p^e) (p^i) = (p^i).totient`
- **What**: For a proper prime-power divisor, `T(p^e, p^i) = φ(p^i)`.
- **How**: `Nat.pow_div`; case split `e - i ≤ i` (gcd is `p^(e-i)`, `Nat.totient_prime_pow` twice, exponent arithmetic by `omega`) vs `i ≤ e - i` (gcd is `p^i`).
- **Hypotheses**: `p` prime, `i < e`.
- **Uses from project**: [`coxDivisorTermAux`]
- **Used by**: `coxDivisorSum_prime_pow_aux`
- **Visibility**: private
- **Lines**: 160–179, proof ≈ 17 lines
- **Notes**: —

### `private theorem Cox.coxDivisorTerm_prime_pow_self_aux`
- **Type**: `(hp : p.Prime) : coxDivisorTermAux (p^e) (p^e) = p^e`
- **What**: `T(p^e, p^e) = p^e`.
- **How**: `Nat.div_self`, `simp`.
- **Hypotheses**: `p` prime.
- **Uses from project**: [`coxDivisorTermAux`]
- **Used by**: `coxDivisorSum_prime_pow_aux`
- **Visibility**: private
- **Lines**: 181–184, proof ≈ 2 lines
- **Notes**: —

### `private theorem Cox.coxDivisorSum_prime_pow_aux`
- **Type**: `(hp : p.Prime) (he : 0 < e) : coxDivisorSumAux (p^e) = p^e + p^(e-1)`
- **What**: `ψ(p^e) = p^e + p^{e-1}`.
- **How**: `Nat.sum_divisors_prime_pow` (NumberTheory/Divisors.lean:537), `Finset.sum_range_succ`; the proper part is `Σ_{i<e} φ(p^i) = Σ_{d ∣ p^{e-1}} φ(d) = p^{e-1}` by `Nat.sum_totient`.
- **Hypotheses**: `p` prime, `e > 0`.
- **Uses from project**: [`coxDivisorSumAux`, `coxDivisorTerm_prime_pow_of_lt_aux`, `coxDivisorTerm_prime_pow_self_aux`]
- **Used by**: `coxDivisorSum_eq_factorizationProd_aux`
- **Visibility**: private
- **Lines**: 186–203, proof ≈ 16 lines
- **Notes**: Neat use of `Nat.sum_totient` (Data/Nat/Totient.lean:163).

### `private def Cox.coxDivisorSumArithmeticFunctionAux`
- **Type**: `ArithmeticFunction ℕ` := `⟨coxDivisorSumAux, _⟩`
- **What**: ψ as an arithmetic function.
- **How**: `map_zero` by `simp`.
- **Hypotheses**: none.
- **Uses from project**: [`coxDivisorSumAux`]
- **Used by**: `coxDivisorSumAF_apply_aux`, `coxDivisorSumArithmeticFunction_mult_aux`, `coxDivisorSum_eq_factorizationProd_aux`
- **Visibility**: private
- **Lines**: 205–206
- **Notes**: Mathlib has no Dedekind ψ (searched `dedekind`, `psi` in NumberTheory). ψ = (μ·μ) ⋆ id in mathlib terms (`ArithmeticFunction.pmul` Zeta.lean:195, `IsMultiplicative.mul` Defs.lean:503, `isMultiplicative_moebius` Moebius.lean:128, `isMultiplicative_id` Misc.lean:112) — an alternative route to multiplicativity that avoids `coxDivisorTerm_mul_of_coprime_aux`, but would need its own identification with the fiber count.

### `private theorem Cox.coxDivisorSumAF_apply_aux`
- **Type**: `coxDivisorSumArithmeticFunctionAux n = coxDivisorSumAux n`
- **What**: unfolding lemma.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`coxDivisorSumArithmeticFunctionAux`, `coxDivisorSumAux`]
- **Used by**: `coxDivisorSumArithmeticFunction_mult_aux`, `coxDivisorSum_eq_factorizationProd_aux`
- **Visibility**: private
- **Lines**: 208–209
- **Notes**: `@[simp]` on private.

### `private theorem Cox.coxDivisorSumArithmeticFunction_mult_aux`
- **Type**: `coxDivisorSumArithmeticFunctionAux.IsMultiplicative`
- **What**: ψ is multiplicative with ψ(1) = 1.
- **How**: `constructor`; value at 1 by `simp`; coprime case by `coxDivisorSum_mul_of_coprime_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`coxDivisorSumArithmeticFunctionAux`, `coxDivisorSumAF_apply_aux`, `coxDivisorSum_mul_of_coprime_aux`, `coxDivisorSumAux`, `coxDivisorTermAux`]
- **Used by**: `coxDivisorSum_eq_factorizationProd_aux`
- **Visibility**: private
- **Lines**: 211–217, proof ≈ 5 lines
- **Notes**: —

### `private theorem Cox.coxDivisorSum_eq_factorizationProd_aux`
- **Type**: `(hn : n ≠ 0) : coxDivisorSumAux n = n.factorization.prod fun p e ↦ p^e + p^(e-1)`
- **What**: ψ(n) = ∏_{p^e ∥ n} (p^e + p^{e-1}).
- **How**: `ArithmeticFunction.IsMultiplicative.multiplicative_factorization` (Defs.lean:561) + `coxDivisorSum_prime_pow_aux`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: [`coxDivisorSumAux`, `coxDivisorSumAF_apply_aux`, `coxDivisorSumArithmeticFunction_mult_aux`, `coxDivisorSum_prime_pow_aux`, `coxDivisorSumArithmeticFunctionAux`]
- **Used by**: `cast_coxDivisorSum_eq_eulerProduct_aux`
- **Visibility**: private
- **Lines**: 219–231, proof ≈ 10 lines
- **Notes**: The `Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)` / `Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)` pair (227–230) is repeated verbatim at 253–256.

### `private theorem Cox.cast_prime_pow_add_aux`
- **Type**: `(hp : p.Prime) (he : 0 < e) : ((p^e + p^(e-1) : ℕ) : ℚ) = (p : ℚ)^e * (1 + 1/p)`
- **What**: `p^e + p^{e-1} = p^e(1 + 1/p)` in ℚ.
- **How**: `push_cast`, `eq_div_iff`, `pow_sub_one_mul`.
- **Hypotheses**: `p` prime (only `p ≠ 0` used), `e > 0`.
- **Uses from project**: []
- **Used by**: `cast_coxDivisorSum_eq_eulerProduct_aux`
- **Visibility**: private
- **Lines**: 233–241, proof ≈ 6 lines
- **Notes**: Only `p ≠ 0` is used; `hp : p.Prime` is stronger than needed.

### `private theorem Cox.cast_coxDivisorSum_eq_eulerProduct_aux`
- **Type**: `(hn : n ≠ 0) : (coxDivisorSumAux n : ℚ) = n * ∏ p ∈ n.primeFactors, (1 + 1/(p : ℚ))`
- **What**: The Euler-product form of ψ over ℚ.
- **How**: `coxDivisorSum_eq_factorizationProd_aux`, `Finsupp.prod_congr` with `cast_prime_pow_add_aux`, `Finsupp.prod_mul`, `Nat.prod_factorization_pow_eq_self` (Data/Nat/Factorization/Defs.lean:97); the last step `n.factorization.prod (fun p _ ↦ …) = ∏ p ∈ n.primeFactors, …` is `rfl` (support of factorization = primeFactors).
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: [`coxDivisorSumAux`, `coxDivisorSum_eq_factorizationProd_aux`, `cast_prime_pow_add_aux`]
- **Used by**: `card_coxMatrix`
- **Visibility**: private
- **Lines**: 243–266, proof ≈ 22 lines
- **Notes**: Mathlib's `ArithmeticFunction.prodPrimeFactors` (Misc.lean:53) + `prodPrimeFactors_apply` (Misc.lean:72) express exactly the RHS factor; not used.

### `theorem Cox.card_coxMatrix`
- **Type**: `(m : ℕ+) : (Fintype.card (CoxMatrix m) : ℚ) = m * ∏ p ∈ (m : ℕ).primeFactors, (1 + 1/(p : ℚ))`
- **What**: Cox's count `|C(m)| = m ∏_{p∣m}(1 + 1/p)`.
- **How**: `card_coxMatrix_eq_divisorSum_aux` cast to ℚ, then `cast_coxDivisorSum_eq_eulerProduct_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix`, `coxDivisorSumAux`, `card_coxMatrix_eq_divisorSum_aux`, `cast_coxDivisorSum_eq_eulerProduct_aux`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 268–276, proof ≈ 5 lines
- **Notes**: Not used anywhere else in the project (`grep -rnw card_coxMatrix XYin` finds only this file). Stated in ℚ "to keep the displayed Euler product literal"; the ℕ forms (102, 219) are private.

## File Summary
- Total declarations: 22 (7 defs, 14 lemmas/theorems, 1 instance, 0 other)
- Key API (used by 3+ others in the file): `coxDivisorTermAux` (5), `coxDivisorSumAux` (8), `coxFiberAux` (5), `coxDivisorSumArithmeticFunctionAux` (3)
- Unused declarations (not used by anything in this file): `card_coxMatrix` (also unused project-wide)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: `cast_coxDivisorSum_eq_eulerProduct_aux` 243–266, 22; `coxDivisorTerm_mul_of_coprime_aux` 116–138, 21)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- The counted quantity is the Dedekind ψ-function; mathlib has NO ψ (searched `Mathlib/NumberTheory` for `dedekind psi`, `psi`). Closest mathlib infrastructure, all grep-verified: `ArithmeticFunction.sigma` (ArithmeticFunction/Misc.lean:143), `IsMultiplicative.multiplicative_factorization` (Defs.lean:561, used at 223), `IsMultiplicative.eq_iff_eq_on_prime_powers` (Defs.lean:579, unused — would let one *define* ψ as `pmul (μ) (μ) * id` and compare on prime powers), `prodPrimeFactors`/`IsMultiplicative.prodPrimeFactors` (Misc.lean:53/72, unused — exactly the `∏_{p∣n}(1+1/p)` factor), `Nat.Coprime.divisors_mul` (Data/Finset/NatDivisors.lean:65, used at 147), `Nat.sum_divisors_prime_pow` (NumberTheory/Divisors.lean:537, used at 189), `Nat.sum_totient` (Data/Nat/Totient.lean:163, used at 202), `Nat.totient_mul` (Totient.lean:131), `Nat.totient_prime_pow` (Totient.lean:209), `Nat.prod_factorization_pow_eq_self` (Factorization/Defs.lean:97).
- What the proof re-implements: (i) CRT-style multiplicativity of a two-variable divisor sum (116–158, 37 lines) — not a Dirichlet convolution, so `IsMultiplicative.mul` does not apply directly; (ii) the `Nat.count`-based `k`-fold coprime count (23–31) — mathlib only has the single window `Nat.filter_coprime_Ico_eq_totient` (Totient.lean:79); (iii) the ℕ→ℚ Euler-product conversion (233–266, 34 lines) which `prodPrimeFactors_apply` + `Finsupp.prod_mul` would shorten.
- No `Gamma0` index formula exists in mathlib (`CongruenceSubgroups.lean` has only `instFiniteIndexGamma0` at line 206); `Subgroup.index` is not mentioned in this file. Mathlib's `FixedDetMatrix.reps`/`repsFintype` (LinearAlgebra/Matrix/FixedDetMatrices.lean:69/159) gives finiteness of the non-primitive representatives but no cardinality — `card_coxMatrix` + Basic.lean's `coxMatrixEquivRightCosets` yield `(Gamma0 m).index = ψ(m)`, a mathlib-worthy corollary not stated anywhere.
### Missing API / repeated patterns
- `CoxMatrix.d_dvd`, `CoxMatrix.div_d` (`σ.d ∣ m`, `m / σ.d = σ.a`) re-derived at 56–59 and 93–94 (also LaurentExpansion.lean:313, 339).
- gcd reassociation `simpa only [Nat.Coprime, Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc] using …` at 63–64 and 82–83 (also Basic.lean:76, 383): a `CoxMatrix.coprime_gcd_b : (Nat.gcd σ.a σ.d).Coprime σ.b` lemma.
- `Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)` + `Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)` duplicated at 227–230 / 253–256 → a `Finsupp.prod_congr`-over-factorization helper taking `p.Prime` and `0 < e` as arguments (mathlib: `Nat.factorization_eq_zero_iff`, `Nat.prime_of_mem_primeFactors`).
- The ℕ-valued statements `Fintype.card (CoxMatrix m) = ∑ d ∈ m.divisors, …` (102) and `= m.factorization.prod (fun p e ↦ p^e + p^(e-1))` (219) are private; exposing them as `card_coxMatrix_eq_sum_divisors` / `card_coxMatrix_eq_prod_factorization` would give downstream users an integer formula.
- `coxFiberAux` as a `def` needs the hand-written `Fintype` instance (36–38); an `abbrev` would not.
### Junk candidates
- `card_coxMatrix` (268) is unused project-wide — a headline result, not junk, but worth knowing that nothing downstream consumes the count (degree of `Φ_m` is presumably taken as `Fintype.card (CoxMatrix m)` directly).
- `coxDivisorSumAF_apply_aux` (208): `@[simp]` `rfl` lemma on a private def; fine.
- Imports `Mathlib.Data.Nat.Totient` and `Mathlib.Data.Finset.NatDivisors` explicitly although `ArithmeticFunction.Misc` transitively supplies them.
### Moral duplicates within this batch
- `coxMatrixToFiberSigmaAux` (54) / `fiberSigmaToCoxMatrixAux` (66) both carry the same `hdvd`/gcd-reassociation blocks as Basic.lean:358–385 (`exists_coxMatrix_of_isColumnHermiteNormalForm_aux`) — three "build a CoxMatrix from (a,b,d) data" sites.
### Generalization notes
- `card_filter_range_coprime_mul_aux` (23) only uses periodicity of `g.Coprime ·` (`Nat.coprime_add_self_right`); it generalises to any `g`-periodic predicate.
- `cast_prime_pow_add_aux` (233) needs only `(p : ℚ) ≠ 0`, not primality; and holds in any `Field`/`DivisionRing` of characteristic zero (or any field where `p ≠ 0`).
- `card_coxMatrix` (268) is stated in ℚ; the underlying identity is in ℕ (219) and the ℚ form holds in any characteristic-zero field.
