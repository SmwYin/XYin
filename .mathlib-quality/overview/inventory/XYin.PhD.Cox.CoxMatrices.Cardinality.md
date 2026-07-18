# Source: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/CoxMatrices/Cardinality.lean — project imports: `XYin.PhD.Cox.CoxMatrices.Basic`

All declarations are in namespace `Cox`.

### `theorem card_filter_range_coprime_mul_aux`
- **Type**: `(g k : ℕ) : ((Finset.range (k * g)).filter (g.Coprime ·)).card = k * g.totient`
- **What**: In an interval of `k` consecutive blocks of length `g`, exactly `k·φ(g)` numbers are coprime to `g` — i.e. the coprime-counting function is periodic with period `g` and density `φ(g)/g`.
- **How**: Induction on `k`, splitting `range (k·g + g)` as `Ico 0 (k·g) ∪ Ico (k·g) (k·g+g)` via `Finset.Ico_union_Ico_eq_Ico`, with disjointness from `Finset.Ico_disjoint_Ico_consecutive`; the new block contributes `φ(g)` by mathlib's `Nat.filter_coprime_Ico_eq_totient`.
- **Hypotheses**: none (holds for all `g, k`, including degenerate `g = 0` cases handled by the same lemmas).
- **Uses from project**: []
- **Used by**: `card_coxFiber_aux`
- **Visibility**: private
- **Lines**: 23–40, proof 16 lines
- **Notes**: none

### `def coxFiberAux`
- **Type**: `(m : ℕ+) (d : ℕ) : Type` (namely `{b : Fin d // (Nat.gcd ((m : ℕ) / d) d).Coprime b}`)
- **What**: The fiber of `C(m)` over a fixed divisor `d` of `m`: residues `b < d` such that `gcd(m/d, d)` is coprime to `b`. This encodes the primitivity condition `gcd(a, b, d) = 1` with `a = m/d` fixed.
- **How**: Direct subtype of `Fin d` cut out by the coprimality predicate.
- **Hypotheses**: none (meaningful when `d ∣ m`; degenerate otherwise).
- **Uses from project**: []
- **Used by**: `instance Fintype (coxFiberAux m d)`, `card_coxFiber_aux`, `coxMatrixToFiberSigmaAux`, `fiberSigmaToCoxMatrixAux`, `coxMatrixEquivFiberSigmaAux`
- **Visibility**: private
- **Lines**: 42–43, definition 2 lines
- **Notes**: none

### `instance : Fintype (coxFiberAux m d)` (anonymous)
- **Type**: `(m : ℕ+) (d : ℕ) : Fintype (coxFiberAux m d)`
- **What**: The fiber is a finite type.
- **How**: `inferInstanceAs` unfolding to the standard `Fintype` instance for a decidable subtype of `Fin d`.
- **Hypotheses**: none
- **Uses from project**: [`coxFiberAux`]
- **Used by**: `card_coxFiber_aux`, `coxMatrixEquivFiberSigmaAux` (implicitly, via `Fintype.card_sigma` in `card_coxMatrix_eq_divisorSum_aux`)
- **Visibility**: private
- **Lines**: 45–47, 3 lines
- **Notes**: none

### `theorem card_coxFiber_aux`
- **Type**: `(m : ℕ+) (d : ℕ) : Fintype.card (coxFiberAux m d) = (d / Nat.gcd ((m : ℕ) / d) d) * (Nat.gcd ((m : ℕ) / d) d).totient`
- **What**: The fiber over divisor `d` has exactly `(d/g)·φ(g)` elements, where `g = gcd(m/d, d)` — the local factor in Cox's divisor sum.
- **How**: Reduces `Fintype.card` of the subtype to a filtered-range count via `Fintype.card_subtype` and `Fin.sum_univ_eq_sum_range`, then applies `card_filter_range_coprime_mul_aux` with `k = d/g`, using `Nat.div_mul_cancel` (`g ∣ d`) to rewrite `d = (d/g)·g`.
- **Hypotheses**: none stated (correct unconditionally since `g ∣ d` always).
- **Uses from project**: [`coxFiberAux`, `card_filter_range_coprime_mul_aux`, the private `Fintype` instance]
- **Used by**: `card_coxMatrix_eq_divisorSum_aux`
- **Visibility**: private
- **Lines**: 49–65, proof 13 lines
- **Notes**: none

### `def coxMatrixToFiberSigmaAux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : Σ d : {d : ℕ // d ∈ (m : ℕ).divisors}, coxFiberAux m d`
- **What**: Sends a Cox matrix `(a, b; 0, d)` to the pair (divisor `d`, fiber element `b`), the forward map of the fibration of `C(m)` over the divisors of `m`.
- **How**: `d ∣ m` from the determinant `a·d = m`; `m/d = a` by `Nat.mul_div_left`; the primitivity `gcd(gcd(a,b),d) = 1` is rearranged to `Coprime (gcd(a,d)) b` using commutativity/associativity of `Nat.gcd` (`Nat.gcd_comm`, `Nat.gcd_left_comm`, `Nat.gcd_assoc`).
- **Hypotheses**: none beyond the `CoxMatrix` structure fields.
- **Uses from project**: [`CoxMatrix` (fields `a`, `b`, `d`, `determinant`, `d_pos`, `b_lt`, `primitive`), `coxFiberAux`]
- **Used by**: `coxMatrixEquivFiberSigmaAux`
- **Visibility**: private
- **Lines**: 67–77, definition 11 lines
- **Notes**: definition built by tactic (`refine`)

### `def fiberSigmaToCoxMatrixAux`
- **Type**: `(m : ℕ+) (x : Σ d : {d : ℕ // d ∈ (m : ℕ).divisors}, coxFiberAux m d) : CoxMatrix m`
- **What**: The inverse map: from a divisor `d ∣ m` and a fiber element `b` it rebuilds the Cox matrix with `a = m/d`.
- **How**: `a·d = m` by `Nat.div_mul_cancel`; positivity of `a` from `Nat.div_pos`; primitivity recovered from the fiber's coprimality by the same `Nat.gcd` commutativity/associativity shuffle as in the forward map.
- **Hypotheses**: none beyond membership `d ∈ divisors m` (which gives `d ∣ m` and `m ≠ 0`).
- **Uses from project**: [`coxFiberAux`, `CoxMatrix`]
- **Used by**: `coxMatrixEquivFiberSigmaAux`
- **Visibility**: private
- **Lines**: 79–96, definition 18 lines
- **Notes**: definition built by tactic (`refine`)

### `def coxMatrixEquivFiberSigmaAux`
- **Type**: `(m : ℕ+) : CoxMatrix m ≃ Σ d : {d : ℕ // d ∈ (m : ℕ).divisors}, coxFiberAux m d`
- **What**: The bijection `C(m) ≃ ⨆_{d ∣ m} {b < d : gcd(gcd(m/d,d), b) = 1}` — the structural heart of the counting argument.
- **How**: `toFun`/`invFun` are the two maps above; `left_inv` is checked componentwise after injecting through `CoxMatrix.toFin_injective` and rewriting `m/d = a`; `right_inv` is definitional (`rfl`) after destructing the sigma.
- **Hypotheses**: none
- **Uses from project**: [`coxMatrixToFiberSigmaAux`, `fiberSigmaToCoxMatrixAux`, `CoxMatrix.toFin_injective`, `CoxMatrix.toFin`, `coxFiberAux`, `CoxMatrix` (field `determinant`, `d_pos`)]
- **Used by**: `card_coxMatrix_eq_divisorSum_aux`
- **Visibility**: private
- **Lines**: 98–113, 16 lines
- **Notes**: none

### `theorem card_coxMatrix_eq_divisorSum_aux`
- **Type**: `(m : ℕ+) : Fintype.card (CoxMatrix m) = ∑ d ∈ (m : ℕ).divisors, (d / Nat.gcd ((m : ℕ) / d) d) * (Nat.gcd ((m : ℕ) / d) d).totient`
- **What**: Cox's cardinality as a divisor sum: `|C(m)| = ∑_{d ∣ m} (d/g)·φ(g)` with `g = gcd(m/d, d)`.
- **How**: Transports the count along `coxMatrixEquivFiberSigmaAux` (`Fintype.card_congr`), sums fibers with `Fintype.card_sigma`, converts the subtype sum to a sum over `divisors m` via `Finset.sum_subtype`, and evaluates each fiber with `card_coxFiber_aux`.
- **Hypotheses**: none
- **Uses from project**: [`coxMatrixEquivFiberSigmaAux`, `card_coxFiber_aux`, `CoxMatrix`, `coxFiberAux`]
- **Used by**: `card_coxMatrix`
- **Visibility**: private
- **Lines**: 115–124, proof 5 lines
- **Notes**: none

### `def coxDivisorTermAux`
- **Type**: `(n d : ℕ) : ℕ`
- **What**: The abstract divisor-sum term `(d/gcd(n/d, d))·φ(gcd(n/d, d))`, detached from `CoxMatrix` so that multiplicativity can be proved purely arithmetically.
- **How**: Direct definition.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `coxDivisorTerm_mul_of_coprime_aux`, `coxDivisorSumAux`, `coxDivisorTerm_prime_pow_of_lt_aux`, `coxDivisorTerm_prime_pow_self_aux`, `coxDivisorSumArithmeticFunction_mult_aux` (in simp)
- **Visibility**: private
- **Lines**: 126–127, 2 lines
- **Notes**: none

### `theorem coxDivisorTerm_mul_of_coprime_aux`
- **Type**: `{m n d e : ℕ} (hmn : m.Coprime n) (hd : d ∣ m) (he : e ∣ n) : coxDivisorTermAux (m * n) (d * e) = coxDivisorTermAux m d * coxDivisorTermAux n e`
- **What**: The divisor term is multiplicative under a coprime splitting `m·n`, `d·e` — the key to reducing the sum to prime powers.
- **How**: With `m ⊥ n`, all cross-gcds are trivial: `gcd((m/d)(n/e), de) = gcd(m/d,d)·gcd(n/e,e)` by `Nat.Coprime.gcd_mul` plus `gcd_mul_right_cancel`/`gcd_mul_left_cancel`, and `φ` is multiplicative on the resulting coprime gcds by `Nat.totient_mul`; quotients split by `Nat.div_mul_div_comm`.
- **Hypotheses**: `m ⊥ n`, `d ∣ m`, `e ∣ n`.
- **Uses from project**: [`coxDivisorTermAux`]
- **Used by**: `coxDivisorSum_mul_of_coprime_aux`
- **Visibility**: private
- **Lines**: 129–151, proof 20 lines
- **Notes**: none

### `def coxDivisorSumAux`
- **Type**: `(n : ℕ) : ℕ`
- **What**: The full divisor sum `∑_{d ∣ n} (d/gcd(n/d,d))·φ(gcd(n/d,d))`, i.e. the arithmetic function whose value at `m` is `|C(m)|`.
- **How**: `Finset.sum` of `coxDivisorTermAux` over `n.divisors`.
- **Hypotheses**: none (`= 0` at `n = 0` since `divisors 0 = ∅`).
- **Uses from project**: [`coxDivisorTermAux`]
- **Used by**: `coxDivisorSum_mul_of_coprime_aux`, `coxDivisorSum_prime_pow_aux`, `coxDivisorSumArithmeticFunctionAux`, `coxDivisorSumAF_apply_aux`, `coxDivisorSumArithmeticFunction_mult_aux`, `coxDivisorSum_eq_factorizationProd_aux`, `cast_coxDivisorSum_eq_eulerProduct_aux`, `card_coxMatrix`
- **Visibility**: private
- **Lines**: 153–154, 2 lines
- **Notes**: none

### `theorem coxDivisorSum_mul_of_coprime_aux`
- **Type**: `{m n : ℕ} (hmn : m.Coprime n) : coxDivisorSumAux (m * n) = coxDivisorSumAux m * coxDivisorSumAux n`
- **What**: The divisor sum is a multiplicative arithmetic function.
- **How**: Divisors of `m·n` factor uniquely as products `d·e` with `d ∣ m`, `e ∣ n` (mathlib's `Nat.Coprime.divisors_mul` map); after `Finset.sum_attach`, `Finset.sum_product` and `Finset.sum_mul_sum` the identity reduces termwise to `coxDivisorTerm_mul_of_coprime_aux`.
- **Hypotheses**: `m ⊥ n`.
- **Uses from project**: [`coxDivisorSumAux`, `coxDivisorTermAux`, `coxDivisorTerm_mul_of_coprime_aux`]
- **Used by**: `coxDivisorSumArithmeticFunction_mult_aux`
- **Visibility**: private
- **Lines**: 156–175, proof 18 lines
- **Notes**: none

### `theorem coxDivisorTerm_prime_pow_of_lt_aux`
- **Type**: `{p e i : ℕ} (hp : p.Prime) (hie : i < e) : coxDivisorTermAux (p ^ e) (p ^ i) = (p ^ i).totient`
- **What**: At a prime power `n = p^e`, the term for a proper divisor `p^i` (`i < e`) collapses to `φ(p^i)`.
- **How**: `gcd(p^{e-i}, p^i) = p^{min(e-i,i)}`; case split on `e-i ≤ i`. In the first case both factors are prime-power totients combined by `Nat.totient_prime_pow` and an exponent bookkeeping identity `i-(e-i) + (e-i-1) = i-1` (omega); in the second the quotient is `1` and the totient factor is exactly `φ(p^i)`.
- **Hypotheses**: `p` prime, `i < e`.
- **Uses from project**: [`coxDivisorTermAux`]
- **Used by**: `coxDivisorSum_prime_pow_aux`
- **Visibility**: private
- **Lines**: 177–196, proof 18 lines
- **Notes**: none

### `theorem coxDivisorTerm_prime_pow_self_aux`
- **Type**: `{p e : ℕ} (hp : p.Prime) : coxDivisorTermAux (p ^ e) (p ^ e) = p ^ e`
- **What**: The top term `d = n = p^e` contributes `p^e` (here `n/d = 1`, `gcd = 1`, `φ(1) = 1`).
- **How**: Rewrite `p^e / p^e = 1` by `Nat.div_self` and simp away `gcd 1 _ = 1`, `φ(1) = 1`.
- **Hypotheses**: `p` prime (only positivity is used).
- **Uses from project**: [`coxDivisorTermAux`]
- **Used by**: `coxDivisorSum_prime_pow_aux`
- **Visibility**: private
- **Lines**: 198–201, proof 3 lines
- **Notes**: none

### `theorem coxDivisorSum_prime_pow_aux`
- **Type**: `{p e : ℕ} (hp : p.Prime) (he : 0 < e) : coxDivisorSumAux (p ^ e) = p ^ e + p ^ (e - 1)`
- **What**: Cox's sum at a prime power: `∑_{d ∣ p^e} term = p^e + p^{e-1}`, the local Euler factor `p^e(1 + 1/p)` in integer form.
- **How**: Enumerates divisors by `Nat.sum_divisors_prime_pow` and splits off the top term with `Finset.sum_range_succ`; the lower terms sum to `∑_{i<e} φ(p^i) = ∑_{d ∣ p^{e-1}} φ(d) = p^{e-1}` by Gauss's identity `Nat.sum_totient`, using `coxDivisorTerm_prime_pow_of_lt_aux` termwise and `coxDivisorTerm_prime_pow_self_aux` for the top.
- **Hypotheses**: `p` prime, `e > 0`.
- **Uses from project**: [`coxDivisorSumAux`, `coxDivisorTermAux`, `coxDivisorTerm_prime_pow_of_lt_aux`, `coxDivisorTerm_prime_pow_self_aux`]
- **Used by**: `coxDivisorSum_eq_factorizationProd_aux`
- **Visibility**: private
- **Lines**: 203–220, proof 16 lines
- **Notes**: none

### `def coxDivisorSumArithmeticFunctionAux`
- **Type**: `ArithmeticFunction ℕ`
- **What**: `coxDivisorSumAux` bundled as a mathlib `ArithmeticFunction` (value `0` at `0`), so that the `IsMultiplicative.multiplicative_factorization` machinery applies.
- **How**: Anonymous constructor; the `map_zero` field is `by simp [coxDivisorSumAux]` (empty divisor sum).
- **Hypotheses**: none
- **Uses from project**: [`coxDivisorSumAux`]
- **Used by**: `coxDivisorSumAF_apply_aux`, `coxDivisorSumArithmeticFunction_mult_aux`, `coxDivisorSum_eq_factorizationProd_aux`
- **Visibility**: private
- **Lines**: 222–223, 2 lines
- **Notes**: none

### `theorem coxDivisorSumAF_apply_aux`
- **Type**: `(n : ℕ) : coxDivisorSumArithmeticFunctionAux n = coxDivisorSumAux n`
- **What**: Evaluation/unfolding lemma for the bundled arithmetic function.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: [`coxDivisorSumArithmeticFunctionAux`, `coxDivisorSumAux`]
- **Used by**: `coxDivisorSumArithmeticFunction_mult_aux`, `coxDivisorSum_eq_factorizationProd_aux`
- **Visibility**: private
- **Lines**: 225–226, proof 1 line
- **Notes**: `@[simp]`

### `theorem coxDivisorSumArithmeticFunction_mult_aux`
- **Type**: `coxDivisorSumArithmeticFunctionAux.IsMultiplicative`
- **What**: The bundled function is multiplicative in the arithmetic-function sense (`f 1 = 1` and `f(mn) = f(m)f(n)` for coprime `m, n`).
- **How**: `f 1 = 1` by direct computation on the single divisor `1`; the coprime case is exactly `coxDivisorSum_mul_of_coprime_aux` transported through the `@[simp]` evaluation lemma.
- **Hypotheses**: none
- **Uses from project**: [`coxDivisorSumArithmeticFunctionAux`, `coxDivisorSumAux`, `coxDivisorTermAux`, `coxDivisorSum_mul_of_coprime_aux`, `coxDivisorSumAF_apply_aux`]
- **Used by**: `coxDivisorSum_eq_factorizationProd_aux`
- **Visibility**: private
- **Lines**: 228–234, proof 6 lines
- **Notes**: none

### `theorem coxDivisorSum_eq_factorizationProd_aux`
- **Type**: `(n : ℕ) (hn : n ≠ 0) : coxDivisorSumAux n = n.factorization.prod fun p e ↦ p ^ e + p ^ (e - 1)`
- **What**: The divisor sum equals the product over the prime factorization of the local values `p^e + p^{e-1}` — the integer form of the Euler product.
- **How**: Mathlib's `ArithmeticFunction.IsMultiplicative.multiplicative_factorization` applied to `coxDivisorSumArithmeticFunction_mult_aux`, then each prime-power factor is evaluated by `coxDivisorSum_prime_pow_aux` (primality from `Nat.prime_of_mem_primeFactors`, positivity of the exponent from `Finsupp.mem_support_iff`).
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: [`coxDivisorSumAux`, `coxDivisorSumAF_apply_aux`, `coxDivisorSumArithmeticFunction_mult_aux`, `coxDivisorSumArithmeticFunctionAux`, `coxDivisorSum_prime_pow_aux`]
- **Used by**: `cast_coxDivisorSum_eq_eulerProduct_aux`
- **Visibility**: private
- **Lines**: 236–248, proof 11 lines
- **Notes**: none

### `theorem cast_prime_pow_add_aux`
- **Type**: `(p e : ℕ) (hp : p.Prime) (he : 0 < e) : ((p ^ e + p ^ (e - 1) : ℕ) : ℚ) = (p : ℚ) ^ e * (1 + 1 / (p : ℚ))`
- **What**: Cast identity turning the integer local factor `p^e + p^{e-1}` into the displayed Euler factor `p^e·(1 + 1/p)` over `ℚ`.
- **How**: `push_cast` then `p^{e-1} = p^e / p` by `pow_sub_one_mul` (needs `p ≠ 0` in `ℚ`, from primality).
- **Hypotheses**: `p` prime (only `p ≠ 0` used), `e > 0`.
- **Uses from project**: []
- **Used by**: `cast_coxDivisorSum_eq_eulerProduct_aux`
- **Visibility**: private
- **Lines**: 250–262, proof 11 lines
- **Notes**: none

### `theorem cast_coxDivisorSum_eq_eulerProduct_aux`
- **Type**: `(n : ℕ) (hn : n ≠ 0) : (coxDivisorSumAux n : ℚ) = (n : ℚ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℚ))`
- **What**: The rational form of the count: the divisor sum equals `n ∏_{p ∣ n} (1 + 1/p)`.
- **How**: Casts the factorization product from `coxDivisorSum_eq_factorizationProd_aux`, rewrites each factor by `cast_prime_pow_add_aux`, splits the product with `Finsupp.prod_mul`, and identifies `∏ p^{v_p(n)} = n` via `Nat.prod_factorization_pow_eq_self`; the remaining `Finsupp.prod` over the factorization support is definitionally the product over `primeFactors` (`rfl`).
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: [`coxDivisorSumAux`, `coxDivisorSum_eq_factorizationProd_aux`, `cast_prime_pow_add_aux`]
- **Used by**: `card_coxMatrix`
- **Visibility**: private
- **Lines**: 264–287, proof 21 lines
- **Notes**: none

### `theorem card_coxMatrix`
- **Type**: `(m : ℕ+) : (Fintype.card (CoxMatrix m) : ℚ) = (m : ℚ) * ∏ p ∈ (m : ℕ).primeFactors, (1 + 1 / (p : ℚ))`
- **What**: Cox's Euler-product formula `|C(m)| = m ∏_{p ∣ m} (1 + 1/p)` for the number of primitive upper-triangular determinant-`m` representatives, stated over `ℚ` so the Euler product is literal. This is the file's main theorem (Cox, §11, count of `C(m)`).
- **How**: Two-step calc: the combinatorial count `card_coxMatrix_eq_divisorSum_aux` (fibration over divisors) cast to `ℚ`, chained with the arithmetic identity `cast_coxDivisorSum_eq_eulerProduct_aux` (multiplicativity + Gauss's `∑ φ = id` at prime powers).
- **Hypotheses**: none (`m : ℕ+` provides `m ≠ 0`).
- **Uses from project**: [`CoxMatrix`, `card_coxMatrix_eq_divisorSum_aux`, `coxDivisorSumAux`, `cast_coxDivisorSum_eq_eulerProduct_aux`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 289–297, proof 4 lines
- **Notes**: docstring present

### File Summary
- Total declarations: 22 (7 defs, 14 lemmas/theorems, 1 instance, 0 tactic/meta decls)
- Key API (used by 3+ others): `coxDivisorTermAux` (5 uses), `coxDivisorSumAux` (8 uses), `coxFiberAux` (5 uses), `coxDivisorSumArithmeticFunctionAux` (3 uses)
- Unused declarations (not used by anything in this file): `card_coxMatrix` (public entry point)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [] (longest: `cast_coxDivisorSum_eq_eulerProduct_aux`, 21 proof lines)
