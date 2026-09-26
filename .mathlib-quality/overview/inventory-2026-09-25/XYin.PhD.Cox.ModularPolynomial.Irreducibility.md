# Inventory: XYin/PhD/Cox/ModularPolynomial/Irreducibility.lean  (141 lines)

Proves Cox Exercise 11.10 / Theorem 11.18(ii) in function-field form: `Φ_m(X, Y)`, viewed in `ℂ(Y)[X]`, is irreducible. The argument is the classical one: over the function field, `Φ_m(X, j)` splits as `∏_c (X - j_c)` over the right cosets `c ∈ Γ₀(m)\SL₂(ℤ)`; `SL₂(ℤ)` acts transitively on the roots by `ℂ(j)`-algebra automorphisms, so the minimal polynomial of the base root has all `|Γ₀(m)\SL₂(ℤ)|` distinct roots, forcing `deg minpoly ≥ deg Φ_m` and hence `Φ_m = minpoly`. Two fully general "conjugate-counting" lemmas carry the argument.

## Declarations

### `private theorem Cox.modularPolynomialHolomorphic_eq_product`
- **Type**: `(m : ℕ+) : Polynomial.map evalJ (modularPolynomialC m) = ∏ c : Gamma0RightCosets m, (Polynomial.X - Polynomial.C (rightCosetFunction m c))`
- **What**: Substituting the holomorphic function `j` for `Y` in `Φ_m` gives the product of `X - j_c` over right cosets, as a polynomial over the ring of holomorphic functions.
- **How**: `Polynomial.ext` on coefficients, `Subtype.ext`/`funext` to compare holomorphic functions pointwise, `evalJ_apply` to evaluate, then `Polynomial.coeff_map` + `Polynomial.map_prod` to reduce to `modularPolynomialC_rightCosetProduct` at each `τ`.
- **Hypotheses**: none.
- **Uses from project**: `evalJ`, `evalJ_apply`, `evaluation`, `modularPolynomialC`, `modularPolynomialC_rightCosetProduct`, `BivariatePolynomial.specializeY`, `rightCosetFunction`, `Gamma0RightCosets`
- **Used by**: `modularPolynomialFunctionField_eq_product`
- **Visibility**: private
- **Lines**: 28–44, proof body ≈ 12 lines
- **Notes**: `classical`. The `change _ = evaluation tau (…)` step (L40–41) hard-codes the coercion; fragile under API changes.

### `private abbrev Cox.modularPolynomialRatFunc`
- **Type**: `(m : ℕ+) : Polynomial (RatFunc ℂ) := Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (modularPolynomialC m)`
- **What**: `Φ_m` with coefficients pushed from `ℂ[Y]` into `ℂ(Y)`.
- **How**: `Polynomial.map` along `algebraMap`.
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialC`
- **Used by**: `modularPolynomialFunctionField`, `modularPolynomialFunctionField_eq_map`, `modularPolynomialRatFunc_aeval_base`, `modularPolynomialRatFunc_irreducible`, `modularPolynomialC_irreducibleInX`
- **Visibility**: private
- **Lines**: 46–48, proof body ≈ 0 lines
- **Notes**: Being an `abbrev`, the `show … from rfl` at L75–76 is needed to fold it back.

### `private abbrev Cox.modularPolynomialFunctionField`
- **Type**: `(m : ℕ+) : Polynomial FunctionField := Polynomial.map (algebraMap (RatFunc ℂ) FunctionField) (modularPolynomialRatFunc m)`
- **What**: `Φ_m` with coefficients in the meromorphic function field of `ℍ`, via `ℂ(Y) → FunctionField` (`Y ↦ j`).
- **How**: `Polynomial.map` along the `RatFunc ℂ`-algebra structure of `FunctionField` (from UpperHalfPlaneFunctionField.lean).
- **Hypotheses**: none.
- **Uses from project**: `FunctionField`, `modularPolynomialRatFunc`
- **Used by**: `modularPolynomialFunctionField_eq_map`, `modularPolynomialFunctionField_eq_product`, `modularPolynomialRatFunc_aeval_base`
- **Visibility**: private
- **Lines**: 50–51, proof body ≈ 0 lines
- **Notes**: —

### `private theorem Cox.modularPolynomialFunctionField_eq_map`
- **Type**: `(m : ℕ+) : modularPolynomialFunctionField m = Polynomial.map (algebraMap HolomorphicFunction FunctionField) (Polynomial.map evalJ (modularPolynomialC m))`
- **What**: The two routes `ℂ[Y] → ℂ(Y) → FunctionField` and `ℂ[Y] → HolomorphicFunction → FunctionField` agree on `Φ_m`.
- **How**: Coefficientwise (`Polynomial.coeff_map`) and `ratFuncEvalJ_algebraMap` (compatibility of the `RatFunc ℂ`-algebra map with `evalJ`).
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialFunctionField`, `modularPolynomialRatFunc`, `HolomorphicFunction`, `FunctionField`, `evalJ`, `modularPolynomialC`, `ratFuncEvalJ_algebraMap`
- **Used by**: `modularPolynomialFunctionField_eq_product`
- **Visibility**: private
- **Lines**: 53–60, proof body ≈ 4 lines
- **Notes**: —

### `private theorem Cox.modularPolynomialFunctionField_eq_product`
- **Type**: `(m : ℕ+) : modularPolynomialFunctionField m = ∏ c : Gamma0RightCosets m, (Polynomial.X - Polynomial.C (rightCosetRoot m c))`
- **What**: Over the function field, `Φ_m(X, j)` splits completely with roots the coset conjugates `j_c`.
- **How**: `modularPolynomialFunctionField_eq_map`, `modularPolynomialHolomorphic_eq_product`, `Polynomial.map_prod`, unfold `rightCosetRoot`.
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialFunctionField`, `modularPolynomialFunctionField_eq_map`, `modularPolynomialHolomorphic_eq_product`, `rightCosetRoot`, `Gamma0RightCosets`
- **Used by**: `modularPolynomialRatFunc_aeval_base`
- **Visibility**: private
- **Lines**: 62–69, proof body ≈ 3 lines
- **Notes**: `classical`. This is a `Polynomial.Splits` statement; mathlib's `Polynomial.splits_prod`/`natDegree_eq_card_roots` are not needed since the product form is used directly.

### `private theorem Cox.modularPolynomialRatFunc_aeval_base`
- **Type**: `(m : ℕ+) : Polynomial.aeval (rightCosetRoot m (baseRightCoset m)) (modularPolynomialRatFunc m) = 0`
- **What**: The base root `j(mτ)` (as a function-field element) is a root of `Φ_m` over `ℂ(Y)`.
- **How**: `Polynomial.aeval_def`, `eval_map`, the product form, `Polynomial.eval_prod` and `Finset.prod_eq_zero` at the base coset.
- **Hypotheses**: none.
- **Uses from project**: `rightCosetRoot`, `baseRightCoset`, `modularPolynomialRatFunc`, `modularPolynomialFunctionField`, `modularPolynomialFunctionField_eq_product`
- **Used by**: `modularPolynomialRatFunc_irreducible`
- **Visibility**: private
- **Lines**: 71–79, proof body ≈ 5 lines
- **Notes**: Same `eval_prod`/`prod_eq_zero`-at-distinguished-index pattern as Construction.lean:366–369.

### `private theorem Cox.minpoly_aeval_rightCosetRoot`
- **Type**: `(m : ℕ+) (c : Gamma0RightCosets m) : Polynomial.aeval (rightCosetRoot m c) (minpoly (RatFunc ℂ) (rightCosetRoot m (baseRightCoset m))) = 0`
- **What**: Every coset conjugate `j_c` is a root of the minimal polynomial of the base root over `ℂ(Y)`.
- **How**: Transitivity: `exists_rightCosetMul_baseRightCoset_eq` gives `δ ∈ SL₂(ℤ)` moving the base coset to `c`; the precomposition `precompAlgEquiv δ` is a `ℂ(Y)`-algebra automorphism of the function field sending the base root to `j_c` (`precompAlgEquiv_rightCosetRoot`), and `minpoly.aeval_algHom` (Mathlib/FieldTheory/Minpoly/Basic.lean:97) transports the root.
- **Hypotheses**: none.
- **Uses from project**: `Gamma0RightCosets`, `rightCosetRoot`, `baseRightCoset`, `exists_rightCosetMul_baseRightCoset_eq`, `precompAlgEquiv`, `precompAlgEquiv_rightCosetRoot`
- **Used by**: `modularPolynomialRatFunc_irreducible`
- **Visibility**: private
- **Lines**: 81–87, proof body ≈ 4 lines
- **Notes**: —

### `private lemma Cox.card_le_minpoly_natDegree_of_injective_roots`
- **Type**: `{F E iota : Type*} [Field F] [CommRing E] [IsDomain E] [Algebra F E] [Fintype iota] {alpha : E} (halphaIntegral : IsIntegral F alpha) (conjugate : iota → E) (hinjective : Function.Injective conjugate) (hroots : ∀ i, Polynomial.aeval (conjugate i) (minpoly F alpha) = 0) : Fintype.card iota ≤ (minpoly F alpha).natDegree`
- **What**: Conjugate counting: an injective family of `card ι` roots of the minimal polynomial forces its degree to be at least `card ι`.
- **How**: The image `(minpoly F α).map (algebraMap F E)` is monic hence nonzero, has the same `natDegree` (`Monic.natDegree_map`), and vanishes at the injective family; `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero` (Mathlib/Algebra/Polynomial/Roots.lean:713) would make it zero if `natDegree < card ι`.
- **Hypotheses**: `F` a field, `E` an integral domain `F`-algebra, `α` integral over `F`, `ι` finite, `conjugate` injective with values roots of `minpoly F α`.
- **Uses from project**: `[]`
- **Used by**: `irreducible_of_card_conjugates`
- **Visibility**: private
- **Lines**: 89–100, proof body ≈ 6 lines
- **Notes**: FULLY GENERAL (no modular content). PR candidate for `Mathlib/FieldTheory/Minpoly/Field.lean`. Generalizes further: the minimal polynomial plays no role — for any `p : F[X]`, `p ≠ 0`, with `∀ i, aeval (conjugate i) p = 0`, `Fintype.card ι ≤ p.natDegree` (use `Polynomial.natDegree_map_eq_of_injective (algebraMap F E).injective` in place of `Monic.natDegree_map`; `algebraMap` from a field to a nontrivial ring is injective). Not in mathlib (grep: no `card.*≤.*natDegree (minpoly`, no `natDegree_le_of_card_conjugates`; nearest are `card_roots'` :79 and `card_le_degree_of_subset_roots` :136, both about `Multiset.roots` rather than an injective family).

### `private lemma Cox.irreducible_of_card_conjugates`
- **Type**: `{F E iota : Type*} [Field F] [CommRing E] [IsDomain E] [Algebra F E] [Fintype iota] {p : Polynomial F} (hp : p.Monic) {alpha : E} (halpha : Polynomial.aeval alpha p = 0) (conjugate : iota → E) (hinjective : Function.Injective conjugate) (hroots : ∀ i, Polynomial.aeval (conjugate i) (minpoly F alpha) = 0) (hdegree : p.natDegree ≤ Fintype.card iota) : Irreducible p`
- **What**: A monic annihilator `p` of `α` whose degree is at most the number of distinct conjugates of `α` (all roots of `minpoly F α`) is the minimal polynomial, hence irreducible.
- **How**: `α` is integral (`⟨p, hp, halpha⟩`); `card ι ≤ deg minpoly` by the previous lemma so `deg p ≤ deg minpoly`; `minpoly.dvd` (Minpoly/Field.lean:72) plus `Polynomial.eq_of_monic_of_dvd_of_natDegree_le` (Mathlib/Algebra/Polynomial/Div.lean:95) give `p = minpoly F α`; conclude with `minpoly.irreducible` (Minpoly/Basic.lean:265).
- **Hypotheses**: as listed; `p` monic, `α` a root of `p`, injective family of `card ι ≥ deg p` roots of `minpoly F α`.
- **Uses from project**: `card_le_minpoly_natDegree_of_injective_roots`
- **Used by**: `modularPolynomialRatFunc_irreducible`
- **Visibility**: private
- **Lines**: 102–114, proof body ≈ 7 lines
- **Notes**: FULLY GENERAL. PR candidate. Lines 111–113 could be replaced by mathlib `minpoly.unique_of_degree_le_degree_minpoly` (Minpoly/Field.lean:65: monic annihilator with `degree p ≤ degree (minpoly A x)` equals the minpoly) after converting `natDegree` to `degree`. Compare `minpoly.eq_of_irreducible_of_monic` (Field.lean:139), which is the converse direction.

### `private theorem Cox.modularPolynomialRatFunc_irreducible`
- **Type**: `(m : ℕ+) : Irreducible (modularPolynomialRatFunc m)`
- **What**: `Φ_m` is irreducible over `ℂ(Y)`.
- **How**: `irreducible_of_card_conjugates` with `p := Φ_m` (monic by `modularPolynomialC_monic` and `Monic.map`), `α :=` the base root, conjugates `rightCosetRoot m` (injective by `rightCosetRoot_injective`), roots by `minpoly_aeval_rightCosetRoot`, and `deg Φ_m = |C(m)| = |Γ₀(m)\SL₂(ℤ)|` (`modularPolynomialC_natDegree`, `Fintype.card_congr (coxMatrixEquivRightCosets m)`).
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialRatFunc`, `irreducible_of_card_conjugates`, `modularPolynomialC_monic`, `modularPolynomialRatFunc_aeval_base`, `rightCosetRoot`, `rightCosetRoot_injective`, `minpoly_aeval_rightCosetRoot`, `modularPolynomialC`, `modularPolynomialC_natDegree`, `CoxMatrix`, `Gamma0RightCosets`, `coxMatrixEquivRightCosets`
- **Used by**: `modularPolynomialC_irreducibleInX`
- **Visibility**: private
- **Lines**: 116–130, proof body ≈ 12 lines
- **Notes**: —

### `theorem Cox.modularPolynomialC_irreducibleInX`
- **Type**: `(m : ℕ+) : Irreducible (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (modularPolynomialC m))`
- **What**: Cox Exercise 11.10 / Theorem 11.18(ii): `Φ_m(X, Y)` is irreducible as a polynomial in `X` over `ℂ(Y)`.
- **How**: Restatement of `modularPolynomialRatFunc_irreducible` with the abbreviation unfolded.
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialC`, `modularPolynomialRatFunc_irreducible`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 132–137, proof body ≈ 1 line
- **Notes**: External user: Arithmetic.lean (3). Irreducibility in `ℂ[X,Y]` (Gauss) and in `ℤ[X,Y]` are handled downstream (Arithmetic.lean).

## File Summary
- Total declarations: 11 (2 abbrevs, 9 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `modularPolynomialRatFunc` (5), `modularPolynomialFunctionField` (3)
- Unused declarations (not used by anything in this file): `modularPolynomialC_irreducibleInX` (used by Arithmetic.lean)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: `modularPolynomialHolomorphic_eq_product`, 12 lines)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- Conjugate-counting lemmas (L89–114), exact statements recorded above; both are stated for arbitrary `[Field F] [CommRing E] [IsDomain E] [Algebra F E] [Fintype ι]` and use only `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero` (`Mathlib/Algebra/Polynomial/Roots.lean:713`), `Polynomial.Monic.natDegree_map`, `minpoly.dvd` (`Mathlib/FieldTheory/Minpoly/Field.lean:72`), `Polynomial.eq_of_monic_of_dvd_of_natDegree_le` (`Mathlib/Algebra/Polynomial/Div.lean:95`), `minpoly.irreducible` (`Mathlib/FieldTheory/Minpoly/Basic.lean:265`). No mathlib statement of either was found (searched Minpoly/{Basic,Field}.lean, Roots.lean, Splits.lean, IntermediateField/Adjoin for `card`+`minpoly`, `natDegree_le_of_card`, `irreducible_of_card`); `IntermediateField.card_algHom_adjoin_integral` (Adjoin/Basic.lean:605) is the separable-field cousin. Recommended PR names: `minpoly.card_le_natDegree_of_injective_aeval_eq_zero` (generalized to any `p ≠ 0`) and `Polynomial.Monic.irreducible_of_card_conjugates`.
- `irreducible_of_card_conjugates` L111–113 is `minpoly.unique_of_degree_le_degree_minpoly` (`Mathlib/FieldTheory/Minpoly/Field.lean:65`) modulo `natDegree`↔`degree`.
- `modularPolynomialFunctionField_eq_product` (L62–69) is a `Polynomial.Splits`-type fact; if separability is ever needed, `Polynomial.separable_prod_X_sub_C_iff'` (`Mathlib/FieldTheory/Separable.lean:324`) + `rightCosetRoot_injective` gives `Separable (modularPolynomialFunctionField m)` in one line (this is what Interpolation.lean:420–429 proves by hand at the level of holomorphic functions).
### Missing API / repeated patterns
- `Polynomial.map` along a chain of three coefficient rings (`ℂ[Y] → ℂ(Y) → FunctionField` vs `ℂ[Y] → HolomorphicFunction → FunctionField`) is reconciled by hand in L53–60 with `ratFuncEvalJ_algebraMap`; a lemma `Polynomial.map_map` + a `RingHom.ext` statement `(algebraMap (RatFunc ℂ) FunctionField).comp (algebraMap ℂ[X] (RatFunc ℂ)) = (algebraMap HolomorphicFunction FunctionField).comp evalJ` in UpperHalfPlaneFunctionField.lean would make it `rw [Polynomial.map_map, this]`.
- The `evaluation tau` pointwise-comparison idiom (L33–44) for equalities in `Polynomial HolomorphicFunction` recurs (see `evalJ_apply` uses); a `Polynomial.ext`-style lemma `Polynomial.ext_holomorphic : (∀ n τ, evaluation τ (p.coeff n) = evaluation τ (q.coeff n)) → p = q` would shorten it.
### Junk candidates
- `modularPolynomialC_irreducibleInX` (L134–137) is a one-line re-export of the private `modularPolynomialRatFunc_irreducible`; merge (make the latter public under the former's name).
- No dead code, `#check`s, or commented blocks.
### Moral duplicates within this batch
- `modularPolynomialRatFunc_aeval_base` (L71–79) ≡ `Construction.modularPolynomialC_eval_levelJ_j` (Construction.lean:362–369) lifted to the function field (same `prod_eq_zero`-at-base-index proof).
- `modularPolynomialHolomorphic_eq_product` (L28–44) restates `Construction.modularPolynomialC_rightCosetProduct` (Construction.lean:355–359) inside `Polynomial HolomorphicFunction`.
### Generalization notes
- L89–114: already general; the first lemma does not need `IsIntegral`/`minpoly` at all (any nonzero `p` works), and `[CommRing E] [IsDomain E]` can be weakened to `[Ring E] [IsDomain E]` only if `eq_zero_of_natDegree_lt_card_of_eval_eq_zero` is (it currently requires `CommRing`).
- The modular-specific part (L28–87, 116–130) is a template "monic polynomial over `F` whose roots are permuted transitively by `F`-automorphisms of `E` is irreducible"; a reusable lemma `irreducible_of_transitive_algEquiv (G : Subgroup (E ≃ₐ[F] E)) …` would make the file 30 lines.
