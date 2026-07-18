# XYin/PhD/Cox/ModularPolynomial/Irreducibility.lean
Project-internal imports: `XYin.PhD.Cox.ModularPolynomial.Construction`, `XYin.PhD.Cox.UpperHalfPlaneFunctionField`
(also imports `Mathlib.FieldTheory.Minpoly.Field`)

All declarations live in `namespace Cox`, section `Irreducibility`, with `open UpperHalfPlaneFunctionField` (so `evalJ`, `FunctionField`, etc. below are `Cox.UpperHalfPlaneFunctionField.*`).

### `private theorem modularPolynomialHolomorphic_eq_product`
- **Type**: `(m : ℕ+) : Polynomial.map evalJ (modularPolynomialC m) = ∏ c : Gamma0RightCosets m, (Polynomial.X - Polynomial.C (rightCosetFunction m c))`
- **What**: Pushing the coefficients of `Φ_m(X,Y)` through `evalJ : ℂ[Y] →+* HolomorphicFunction` (substituting `Y ↦ j`) yields exactly the product `∏_c (X − j_m|_c)` over right cosets, now with coefficients in the subring of holomorphic functions on `ℍ`.
- **How**: Two elements of the subring `HolomorphicFunction` are equal iff they agree at every `τ ∈ ℍ` (checked coefficientwise via `Polynomial.ext`, `Subtype.ext`, `funext`); pointwise, the claim is the coefficient-level content of the specialization identity `modularPolynomialC_rightCosetProduct m τ`, transported through `evalJ_apply` and the evaluation homomorphism `evaluation τ`.
- **Hypotheses**: none beyond `m : ℕ+`.
- **Uses from project**: [`evalJ`, `evalJ_apply`, `evaluation`, `modularPolynomialC`, `modularPolynomialC_rightCosetProduct`, `Gamma0RightCosets`, `rightCosetFunction`, `BivariatePolynomial.specializeY`]
- **Used by**: `modularPolynomialFunctionField_eq_product`
- **Visibility**: private
- **Lines**: 28-44, proof 13 lines
- **Notes**: none

### `private abbrev modularPolynomialRatFunc`
- **Type**: `(m : ℕ+) : Polynomial (RatFunc ℂ)`
- **What**: The modular polynomial `Φ_m` viewed as a polynomial in the root variable `X` with coefficients in the rational function field `ℂ(Y)`, via the canonical map `ℂ[Y] → ℂ(Y)`.
- **How**: Definition: `Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (modularPolynomialC m)`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialC`]
- **Used by**: `modularPolynomialFunctionField`, `modularPolynomialRatFunc_aeval_base`, `modularPolynomialRatFunc_irreducible`, `modularPolynomialC_irreducibleInX` (its statement is this abbrev unfolded)
- **Visibility**: private
- **Lines**: 46-48, definition 3 lines
- **Notes**: none

### `private abbrev modularPolynomialFunctionField`
- **Type**: `(m : ℕ+) : Polynomial FunctionField`
- **What**: `Φ_m` further base-changed to the fraction field of the ring of holomorphic functions on `ℍ` (the "function field" in which the coset roots live), via `ℂ(Y) → FunctionField`.
- **How**: Definition: map of `modularPolynomialRatFunc m` along `algebraMap (RatFunc ℂ) FunctionField`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialRatFunc`, `FunctionField`]
- **Used by**: `modularPolynomialFunctionField_eq_map`, `modularPolynomialFunctionField_eq_product`, `modularPolynomialRatFunc_aeval_base`
- **Visibility**: private
- **Lines**: 50-51, definition 2 lines
- **Notes**: none

### `private theorem modularPolynomialFunctionField_eq_map`
- **Type**: `(m : ℕ+) : modularPolynomialFunctionField m = Polynomial.map (algebraMap HolomorphicFunction FunctionField) (Polynomial.map evalJ (modularPolynomialC m))`
- **What**: The two routes from `ℂ[Y]`-coefficients into the function field agree: going `ℂ[Y] → ℂ(Y) → FunctionField` coefficientwise equals going `ℂ[Y] →(Y↦j) HolomorphicFunction → FunctionField`.
- **How**: A `calc` reducing both sides to `Polynomial.map evalJFracPoly`: the first step is coefficientwise and uses the compatibility lemma `ratFuncEvalJ_algebraMap` (the square `ℂ[Y] → ℂ(Y) → FF` = `ℂ[Y] → Hol → FF` commutes because `j` is transcendental-compatible), the second is `Polynomial.map_map` plus `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialFunctionField`, `modularPolynomialRatFunc`, `evalJFracPoly`, `ratFuncEvalJ_algebraMap`, `HolomorphicFunction`, `FunctionField`, `evalJ`, `modularPolynomialC`]
- **Used by**: `modularPolynomialFunctionField_eq_product`
- **Visibility**: private
- **Lines**: 53-67, proof 11 lines
- **Notes**: none

### `private theorem modularPolynomialFunctionField_eq_product`
- **Type**: `(m : ℕ+) : modularPolynomialFunctionField m = ∏ c : Gamma0RightCosets m, (Polynomial.X - Polynomial.C (rightCosetRoot m c))`
- **What**: Over the function field, `Φ_m(X, j)` splits completely as the product of the linear factors `X − (coset root)`, where `rightCosetRoot m c` is the image of the holomorphic function `j_m|_c` in the fraction field.
- **How**: Chains `modularPolynomialFunctionField_eq_map` with the holomorphic-level factorization `modularPolynomialHolomorphic_eq_product`, then distributes the ring-hom map over the product with `Polynomial.map_prod` and identifies each mapped factor with `rightCosetRoot`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialFunctionField`, `modularPolynomialFunctionField_eq_map`, `modularPolynomialHolomorphic_eq_product`, `Gamma0RightCosets`, `rightCosetRoot`]
- **Used by**: `modularPolynomialRatFunc_aeval_base`
- **Visibility**: private
- **Lines**: 69-76, proof 4 lines
- **Notes**: none

### `private theorem modularPolynomialRatFunc_aeval_base`
- **Type**: `(m : ℕ+) : Polynomial.aeval (rightCosetRoot m (baseRightCoset m)) (modularPolynomialRatFunc m) = 0`
- **What**: The distinguished root: the function `j(mτ)` (the root attached to the base coset, i.e. the identity coset with representative `σ₀`) is a root of `Φ_m(X, j)` in the function field, as an algebra over `ℂ(Y)`.
- **How**: Converts `aeval` to evaluation of the mapped polynomial, rewrites by the complete factorization `modularPolynomialFunctionField_eq_product`, and kills the product with `Finset.prod_eq_zero` at the factor indexed by `baseRightCoset m`, whose evaluation is `x − x = 0`.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetRoot`, `baseRightCoset`, `modularPolynomialRatFunc`, `modularPolynomialFunctionField`, `modularPolynomialFunctionField_eq_product`, `FunctionField`]
- **Used by**: `modularPolynomialRatFunc_irreducible`
- **Visibility**: private
- **Lines**: 78-86, proof 6 lines
- **Notes**: none

### `private theorem minpoly_aeval_rightCosetRoot`
- **Type**: `(m : ℕ+) (c : Gamma0RightCosets m) : Polynomial.aeval (rightCosetRoot m c) (minpoly (RatFunc ℂ) (rightCosetRoot m (baseRightCoset m))) = 0`
- **What**: Every coset root is a conjugate of the base root: each `rightCosetRoot m c` is annihilated by the minimal polynomial over `ℂ(Y)` of the base root `j(mτ)`. This is the Galois-action step of the classical irreducibility proof.
- **How**: Chooses `δ ∈ SL₂(ℤ)` with `δ · (base coset) = c` via `exists_rightCosetMul_baseRightCoset_eq` (transitivity of the `SL₂(ℤ)` action on cosets); the precomposition `τ ↦ δ•τ` is a `ℂ(Y)`-algebra automorphism `precompAlgEquiv δ` of the function field (it fixes `j`), and `minpoly.aeval_algHom` (mathlib) shows algebra maps send roots of the minimal polynomial to roots; `precompAlgEquiv_rightCosetRoot` identifies the image of the base root with `rightCosetRoot m c`.
- **Hypotheses**: `c` any right coset.
- **Uses from project**: [`Gamma0RightCosets`, `rightCosetRoot`, `baseRightCoset`, `exists_rightCosetMul_baseRightCoset_eq`, `precompAlgEquiv`, `precompAlgEquiv_rightCosetRoot`]
- **Used by**: `modularPolynomialRatFunc_irreducible`
- **Visibility**: private
- **Lines**: 88-98, proof 8 lines
- **Notes**: none

### `private lemma card_le_minpoly_natDegree_of_injective_roots`
- **Type**: `{F E iota : Type*} [Field F] [CommRing E] [IsDomain E] [Algebra F E] [Fintype iota] {alpha : E} (halphaIntegral : IsIntegral F alpha) (conjugate : iota → E) (hinjective : Function.Injective conjugate) (hroots : ∀ i, Polynomial.aeval (conjugate i) (minpoly F alpha) = 0) : Fintype.card iota ≤ (minpoly F alpha).natDegree`
- **What**: General counting lemma: if an integral element `α` over a field `F` has a family of pairwise-distinct "conjugates" in a domain `E`, all annihilated by `minpoly F α`, then the size of the family is at most `deg(minpoly F α)`.
- **How**: The mapped polynomial `q = (minpoly F α).map (algebraMap F E)` is monic (hence nonzero); if `deg q <` the number of distinct roots, mathlib's `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero` forces `q = 0`, contradicting `Monic.ne_zero`. Uses `minpoly.monic` and `Monic.natDegree_map` to compare degrees before and after mapping.
- **Hypotheses**: `F` a field, `E` an integral domain and `F`-algebra, `α` integral over `F`, `conjugate` injective with all values roots of `minpoly F α`.
- **Uses from project**: []
- **Used by**: `irreducible_of_card_conjugates`
- **Visibility**: private
- **Lines**: 100-116, proof 11 lines
- **Notes**: fully general (no Cox-specific content); candidate for extraction/upstreaming

### `private lemma irreducible_of_card_conjugates`
- **Type**: `{F E iota : Type*} [Field F] [CommRing E] [IsDomain E] [Algebra F E] [Fintype iota] {p : Polynomial F} (hp : p.Monic) {alpha : E} (halpha : Polynomial.aeval alpha p = 0) (conjugate : iota → E) (hinjective : Function.Injective conjugate) (hroots : ∀ i, Polynomial.aeval (conjugate i) (minpoly F alpha) = 0) (hdegree : p.natDegree ≤ Fintype.card iota) : Irreducible p`
- **What**: General irreducibility criterion: a monic polynomial `p` over a field with a root `α` whose minimal polynomial already has at least `deg p` distinct roots (the conjugates) must equal `minpoly F α`, hence is irreducible.
- **How**: The degree sandwich `deg p ≤ card ι ≤ deg(minpoly F α)` (second inequality by `card_le_minpoly_natDegree_of_injective_roots`) combined with `minpoly.dvd F α halpha` and mathlib's `Polynomial.eq_of_monic_of_dvd_of_natDegree_le` forces `p = minpoly F α`; conclude with `minpoly.irreducible`.
- **Hypotheses**: as in the type: `p` monic with root `α` in a domain `E`, injective family of conjugates that are roots of `minpoly F α`, `deg p ≤ card ι`.
- **Uses from project**: [`card_le_minpoly_natDegree_of_injective_roots`]
- **Used by**: `modularPolynomialRatFunc_irreducible`
- **Visibility**: private
- **Lines**: 118-130, proof 8 lines
- **Notes**: fully general (no Cox-specific content); candidate for extraction/upstreaming

### `private theorem modularPolynomialRatFunc_irreducible`
- **Type**: `(m : ℕ+) : Irreducible (modularPolynomialRatFunc m)`
- **What**: `Φ_m(X, Y)` is irreducible as a polynomial in `X` over `ℂ(Y)`. This is the classical argument: `Φ_m` is monic of degree `|C(m)| = [SL₂(ℤ) : Γ₀(m)]`, it has the root `j(mτ)`, and that root has at least that many distinct conjugates (one per coset), so `Φ_m` is the minimal polynomial of `j(mτ)`.
- **How**: Instantiates `irreducible_of_card_conjugates` with `p = Φ_m` mapped to `ℂ(Y)` (monic by `modularPolynomialC_monic`), root `rightCosetRoot m (baseRightCoset m)` (by `modularPolynomialRatFunc_aeval_base`), and conjugate family `rightCosetRoot m` (injective by `rightCosetRoot_injective`, roots by `minpoly_aeval_rightCosetRoot`); the degree count is `modularPolynomialC_natDegree` composed with `Fintype.card_congr (coxMatrixEquivRightCosets m)`.
- **Hypotheses**: none beyond `m : ℕ+`.
- **Uses from project**: [`modularPolynomialRatFunc`, `irreducible_of_card_conjugates`, `modularPolynomialC_monic`, `modularPolynomialRatFunc_aeval_base`, `rightCosetRoot`, `rightCosetRoot_injective`, `minpoly_aeval_rightCosetRoot`, `modularPolynomialC_natDegree`, `CoxMatrix`, `Gamma0RightCosets`, `coxMatrixEquivRightCosets`, `modularPolynomialC`]
- **Used by**: `modularPolynomialC_irreducibleInX`
- **Visibility**: private
- **Lines**: 132-146, proof 12 lines
- **Notes**: none

### `theorem modularPolynomialC_irreducibleInX`
- **Type**: `(m : ℕ+) : Irreducible (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (modularPolynomialC m))`
- **What**: The public statement of Cox Exercise 11.10 / Theorem 11.18(ii) in function-field form: the complex modular polynomial `Φ_m` is irreducible in its root variable `X` over `ℂ(Y)`.
- **How**: Direct restatement of `modularPolynomialRatFunc_irreducible` with the private abbrev unfolded.
- **Hypotheses**: none beyond `m : ℕ+`.
- **Uses from project**: [`modularPolynomialC`, `modularPolynomialRatFunc_irreducible`]
- **Used by**: unused in file (public API export)
- **Visibility**: public
- **Lines**: 148-153, proof 1 line (term-mode)
- **Notes**: docstring cites Cox Exercise 11.10 / Theorem 11.18(ii)

### File Summary
- Total declarations: 11 (0 defs, 9 lemmas/theorems, 0 instances, 0 tactic/meta decls; 2 abbrevs)
- Key API (used by 3+ others): [`modularPolynomialRatFunc` (4 uses), `modularPolynomialFunctionField` (3 uses)]
- Unused declarations (not used by anything in this file): [`modularPolynomialC_irreducibleInX`] — the file's sole public export
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: []
