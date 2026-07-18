# XYin/PhD/Cox/ModularPolynomial/Construction.lean
Project-internal imports: `XYin.PhD.Cox.FormalCoxProduct`, `XYin.PhD.Cox.ModularPolynomial.AnalyticSupport`

All declarations live in `namespace Cox` (bivariate API in sub-namespace `Cox.BivariatePolynomial`). Note: no identifier from `FormalCoxProduct` (`formalCoxPolynomial`, `formalCoxPolynomial_coeff_isInteger`) is used in this file; that import supplies dependencies transitively / for downstream files.

### `abbrev BivariatePolynomial`
- **Type**: `(R : Type*) [Semiring R] : Type _` (:= `Polynomial (Polynomial R)`)
- **What**: Bivariate polynomials `R[Y][X]` with the outer variable read as Cox's root variable `X` and the inner variable as Cox's parameter variable `Y`.
- **How**: Abbreviation for the iterated polynomial ring `Polynomial (Polynomial R)`.
- **Hypotheses**: `R` a semiring.
- **Uses from project**: []
- **Used by**: `varX`, `varY`, `eval`, `specializeY`, `map`, `diagonal`, all `BivariatePolynomial.*` theorems, `modularPolynomialCandidateAux`, `existsUnique_modularPolynomialC`, `modularPolynomialC`
- **Visibility**: public
- **Lines**: 23-25
- **Notes**: none

### `def BivariatePolynomial.varX`
- **Type**: `[Semiring R] : BivariatePolynomial R`
- **What**: Cox's first/root variable `X`, i.e. the outer polynomial variable.
- **How**: Definition: `Polynomial.X` of the outer ring.
- **Hypotheses**: `R` a semiring.
- **Uses from project**: [`BivariatePolynomial`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 31-32
- **Notes**: none

### `def BivariatePolynomial.varY`
- **Type**: `[Semiring R] : BivariatePolynomial R`
- **What**: Cox's second/parameter variable `Y`, i.e. the inner coefficient variable embedded as a constant outer polynomial.
- **How**: Definition: `Polynomial.C Polynomial.X`.
- **Hypotheses**: `R` a semiring.
- **Uses from project**: [`BivariatePolynomial`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 34-35
- **Notes**: none

### `def BivariatePolynomial.eval`
- **Type**: `[Semiring R] (Φ : BivariatePolynomial R) (x y : R) : R`
- **What**: Semantic bivariate evaluation `Φ(x, y)` with argument order (root value, parameter value), compensating for mathlib's inner-first `Polynomial.evalEval` convention.
- **How**: Definition: `Φ.evalEval y x` (arguments swapped relative to mathlib).
- **Hypotheses**: `R` a semiring.
- **Uses from project**: [`BivariatePolynomial`]
- **Used by**: `specializeY_eval`, `eval_swap`, `diagonal_eval`, `modularPolynomialC_eval_levelJ_j`
- **Visibility**: public
- **Lines**: 37-40
- **Notes**: none

### `def BivariatePolynomial.specializeY`
- **Type**: `[CommSemiring R] (y : R) (Φ : BivariatePolynomial R) : Polynomial R`
- **What**: Substitution of a value for the parameter variable `Y`, producing the one-variable polynomial `Φ(X, y)` in the root variable.
- **How**: Definition: coefficientwise map along the evaluation ring homomorphism `Polynomial.evalRingHom y`.
- **Hypotheses**: `R` a commutative semiring.
- **Uses from project**: [`BivariatePolynomial`]
- **Used by**: `specializeY_eval`, `specializeY_ext`, `modularPolynomialCandidateAux_specializeY`, `existsUnique_modularPolynomialC`, `modularPolynomialC_specializeY`, `modularPolynomialC_rightCosetProduct`, `modularPolynomialC_eval_levelJ_j`, `modularPolynomialC_natDegree` (also used by Irreducibility.lean)
- **Visibility**: public
- **Lines**: 42-44
- **Notes**: none

### `def BivariatePolynomial.map`
- **Type**: `[Semiring R] [Semiring S] (f : R →+* S) (Φ : BivariatePolynomial R) : BivariatePolynomial S`
- **What**: Coefficientwise application of a ring homomorphism to a bivariate polynomial (in both variables' coefficients).
- **How**: Definition: outer `Polynomial.map` along the inner `Polynomial.mapRingHom f`.
- **Hypotheses**: `R`, `S` semirings.
- **Uses from project**: [`BivariatePolynomial`]
- **Used by**: `map_swap`, `diagonal_map`
- **Visibility**: public
- **Lines**: 46-49
- **Notes**: none

### `def BivariatePolynomial.diagonal`
- **Type**: `[CommSemiring R] (Φ : BivariatePolynomial R) : Polynomial R`
- **What**: The diagonal specialization `Φ(X, X)`, the single-variable polynomial obtained by identifying the two variables (used downstream for `Φ_m(X, X)` in the singular-moduli theory).
- **How**: Definition: evaluate the outer variable at the inner `Polynomial.X`, i.e. `Polynomial.eval Polynomial.X Φ`.
- **Hypotheses**: `R` a commutative semiring.
- **Uses from project**: [`BivariatePolynomial`]
- **Used by**: `diagonal_eval`, `diagonal_map`, `diagonal_eval₂`, `diagonal_swap`
- **Visibility**: public
- **Lines**: 51-53
- **Notes**: none

### `def coxPhiAtJ`
- **Type**: `(m : ℕ+) (τ : ℍ) : Polynomial ℂ`
- **What**: Cox's equation (11.15) after specializing `Y = j(τ)`: the complex polynomial `∏_{σ ∈ C(m)} (X − j(σ·τ))` whose roots are the `j`-values of the cyclic `m`-sublattice points.
- **How**: Definition: finite product of linear factors `X − C (j (σ.act τ))` over all Cox matrices `σ ∈ C(m)`.
- **Hypotheses**: `m : ℕ+`, `τ ∈ ℍ`.
- **Uses from project**: [`CoxMatrix`, `CoxMatrix.act`, `j`]
- **Used by**: `coxPhiAtJ_monic`, `coxPhiAtJ_natDegree`, `coxPhiFunction_map_eval`, `coxPhiFunction_coeff_apply`, `coxPhiAtJ_eq_rightCosetProduct`, `coxPhiAtJ_sl2_smul`, `modularPolynomialCandidateAux_specializeY`, `existsUnique_modularPolynomialC`, `modularPolynomialC_specializeY`, `modularPolynomialC_eval_levelJ_j`, `modularPolynomialC_natDegree`
- **Visibility**: public
- **Lines**: 57-59
- **Notes**: `noncomputable`

### `def coxPhiFunction`
- **Type**: `(m : ℕ+) : Polynomial (ℍ → ℂ)`
- **What**: The Cox product before evaluating `τ`: the same product `∏_{σ ∈ C(m)} (X − j(σ·—))` but with coefficients in the ring of functions `ℍ → ℂ`, so that each coefficient is itself a function of `τ`.
- **How**: Definition: finite product of `Polynomial.X − Polynomial.C (fun τ ↦ j (σ.act τ))` over `σ ∈ C(m)`.
- **Hypotheses**: `m : ℕ+`.
- **Uses from project**: [`CoxMatrix`, `CoxMatrix.act`, `j`]
- **Used by**: `coxPhiFunction_map_eval`, `coxPhiFunction_coeff_apply`, `coxPhiFunction_coeff_slashInvariant`, `coxPhiFunction_coeff_mdifferentiable`, `coxPhiFunction_coeff_widthM_cuspMeromorphicAt`, `coxPhiFunction_coeff_widthOne_cuspMeromorphicAt`, `coxPhiFunction_coeff_meromorphicOnH`, `coxPhiFunction_coeff_isLevelOne`, `coxPhiFunction_coeff_polynomialInJ`, `coxCoefficientPolynomialAux_eval`
- **Visibility**: public
- **Lines**: 61-64
- **Notes**: `noncomputable`

### `theorem BivariatePolynomial.specializeY_eval`
- **Type**: `{R : Type*} [CommSemiring R] (Φ : BivariatePolynomial R) (x y : R) : (specializeY y Φ).eval x = eval Φ x y`
- **What**: Evaluating the `Y`-specialization at `x` agrees with full bivariate evaluation `Φ(x, y)` — the two-step and one-step substitutions coincide.
- **How**: Direct application of mathlib's `Polynomial.map_evalRingHom_eval`.
- **Hypotheses**: `R` a commutative semiring.
- **Uses from project**: [`BivariatePolynomial`, `BivariatePolynomial.specializeY`, `BivariatePolynomial.eval`]
- **Used by**: `modularPolynomialC_eval_levelJ_j`
- **Visibility**: public
- **Lines**: 68-71, proof 1 line (term-mode)
- **Notes**: none

### `theorem BivariatePolynomial.specializeY_ext`
- **Type**: `{R : Type*} [CommRing R] [IsDomain R] [Infinite R] {Φ Ψ : BivariatePolynomial R} (h : ∀ y : R, Φ.specializeY y = Ψ.specializeY y) : Φ = Ψ`
- **What**: Over an infinite integral domain, a bivariate polynomial is determined by all of its `Y`-specializations. This is the uniqueness engine for the modular polynomial.
- **How**: Reduces coefficientwise (`Polynomial.ext`): for fixed outer index `n` the inner coefficients are polynomials agreeing at every `y ∈ R`, so mathlib's `Polynomial.funext` (polynomials over an infinite domain are determined by their values) gives equality.
- **Hypotheses**: `R` an infinite integral domain; all specializations agree.
- **Uses from project**: [`BivariatePolynomial`, `BivariatePolynomial.specializeY`]
- **Used by**: `existsUnique_modularPolynomialC`
- **Visibility**: public
- **Lines**: 73-82, proof 8 lines
- **Notes**: none

### `theorem BivariatePolynomial.eval_swap`
- **Type**: `{R : Type*} [CommSemiring R] (Φ : BivariatePolynomial R) (x y : R) : eval (Polynomial.Bivariate.swap Φ) x y = eval Φ y x`
- **What**: Swapping the two variables of a bivariate polynomial exchanges the two semantic evaluation arguments: `(swap Φ)(x, y) = Φ(y, x)`.
- **How**: Converts both `evalEval`s to `aevalAeval` via mathlib's `Polynomial.coe_aevalAeval_eq_evalEval` and applies `Polynomial.Bivariate.aevalAeval_swap`.
- **Hypotheses**: `R` a commutative semiring.
- **Uses from project**: [`BivariatePolynomial`, `BivariatePolynomial.eval`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 86-95, proof 5 lines
- **Notes**: none

### `theorem BivariatePolynomial.coeff_coeff_swap`
- **Type**: `{R : Type*} [CommSemiring R] (Φ : BivariatePolynomial R) (i j : ℕ) : ((Polynomial.Bivariate.swap Φ).coeff i).coeff j = (Φ.coeff j).coeff i`
- **What**: The doubly-indexed coefficient of the variable-swapped polynomial at `(i, j)` is the original coefficient at `(j, i)` — swap transposes the coefficient matrix.
- **How**: Induction on `Φ` by monomials (`Polynomial.induction_on'`); the monomial case unfolds mathlib's `Polynomial.Bivariate.swap_monomial` and computes both sides with `Polynomial.coeff_monomial` and a case split on `j = n`.
- **Hypotheses**: `R` a commutative semiring.
- **Uses from project**: [`BivariatePolynomial`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 97-107, proof 6 lines
- **Notes**: none

### `theorem BivariatePolynomial.map_swap`
- **Type**: `{R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (Φ : BivariatePolynomial R) : map f (Polynomial.Bivariate.swap Φ) = Polynomial.Bivariate.swap (map f Φ)`
- **What**: Coefficientwise ring-homomorphism transport commutes with swapping the two variables.
- **How**: Induction by monomials (`Polynomial.induction_on'`); the monomial case pushes `map` through `Polynomial.Bivariate.swap_monomial` and reconciles the two orders of `Polynomial.map` via an auxiliary commutation `map ((mapRingHom f).comp C) P = map C (mapRingHom f P)` proved coefficientwise, plus `mapRingHom f (X^n) = X^n`.
- **Hypotheses**: `R`, `S` commutative semirings.
- **Uses from project**: [`BivariatePolynomial`, `BivariatePolynomial.map`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 109-132, proof 19 lines
- **Notes**: none

### `theorem BivariatePolynomial.diagonal_eval`
- **Type**: `{R : Type*} [CommSemiring R] (Φ : BivariatePolynomial R) (x : R) : (diagonal Φ).eval x = eval Φ x x`
- **What**: Evaluating the diagonal specialization `Φ(X, X)` at `x` equals bivariate evaluation at `(x, x)`.
- **How**: Rewrites both sides through `Polynomial.eval₂_evalRingHom` and uses mathlib's homomorphism-evaluation compatibility `Polynomial.hom_eval₂` to commute the outer evaluation at `X` past the inner evaluation at `x`.
- **Hypotheses**: `R` a commutative semiring.
- **Uses from project**: [`BivariatePolynomial`, `BivariatePolynomial.diagonal`, `BivariatePolynomial.eval`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 134-142, proof 5 lines
- **Notes**: none

### `theorem BivariatePolynomial.diagonal_map`
- **Type**: `{R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (Φ : BivariatePolynomial R) : diagonal (map f Φ) = (diagonal Φ).map f`
- **What**: Coefficientwise maps commute with the diagonal specialization: `(f·Φ)(X, X) = f·(Φ(X, X))`.
- **How**: Direct application of mathlib's `Polynomial.map_mapRingHom_eval_map` at the evaluation point `Polynomial.X` (which is preserved by `Polynomial.map_X`).
- **Hypotheses**: `R`, `S` commutative semirings.
- **Uses from project**: [`BivariatePolynomial`, `BivariatePolynomial.diagonal`, `BivariatePolynomial.map`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 144-150, proof 3 lines
- **Notes**: none

### `theorem BivariatePolynomial.diagonal_eval₂`
- **Type**: `{R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x : S) (Φ : BivariatePolynomial R) : (diagonal Φ).eval₂ f x = Φ.eval₂ (Polynomial.eval₂RingHom f x) x`
- **What**: Evaluating the diagonal via `eval₂` after a coefficient change of rings equals evaluating both variables of `Φ` simultaneously at `x` (inner variable through `eval₂RingHom f x`).
- **How**: Direct application of mathlib's `Polynomial.hom_eval₂` with the outer evaluation at `X` and the composite inner evaluation homomorphism.
- **Hypotheses**: `R`, `S` commutative semirings.
- **Uses from project**: [`BivariatePolynomial`, `BivariatePolynomial.diagonal`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 152-160, proof 4 lines
- **Notes**: none

### `theorem BivariatePolynomial.diagonal_swap`
- **Type**: `{R : Type*} [CommSemiring R] (Φ : BivariatePolynomial R) : diagonal (Polynomial.Bivariate.swap Φ) = diagonal Φ`
- **What**: The diagonal specialization is symmetric: swapping the two variables does not change `Φ(X, X)`. (Downstream this reflects the `X ↔ Y` symmetry of `Φ_m` on the diagonal.)
- **How**: Induction by monomials (`Polynomial.induction_on'`); the additive case unfolds `diagonal` to `Polynomial.eval X` and distributes, and the monomial case computes `swap (C P · X^n)` explicitly via mathlib's `Polynomial.Bivariate.swap_monomial` and `Polynomial.eval_monomial`, both sides giving `P(X)·X^n`.
- **Hypotheses**: `R` a commutative semiring.
- **Uses from project**: [`BivariatePolynomial`, `BivariatePolynomial.diagonal`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 162-180, proof 14 lines
- **Notes**: tagged `@[simp]`

### `theorem coxPhiAtJ_monic`
- **Type**: `(m : ℕ+) (τ : ℍ) : (coxPhiAtJ m τ).Monic`
- **What**: The specialized Cox product `∏_σ (X − j(σ·τ))` is monic in `X`.
- **How**: A product of monic linear factors is monic, by mathlib's `Polynomial.monic_prod_X_sub_C`.
- **Hypotheses**: none beyond `m`, `τ`.
- **Uses from project**: [`coxPhiAtJ`, `CoxMatrix`, `CoxMatrix.act`, `j`]
- **Used by**: `modularPolynomialCandidateAux_specializeY`
- **Visibility**: public
- **Lines**: 182-186, proof 3 lines
- **Notes**: none

### `theorem coxPhiAtJ_natDegree`
- **Type**: `(m : ℕ+) (τ : ℍ) : (coxPhiAtJ m τ).natDegree = Fintype.card (CoxMatrix m)`
- **What**: The degree of the specialized Cox product equals `|C(m)|`, the number of Cox matrices (classically `m·∏_{p|m}(1 + 1/p)`).
- **How**: A product of `|C(m)|` linear factors `X − c` has degree `|C(m)|`; discharged by `simp` unfolding `coxPhiAtJ` (via mathlib's degree-of-product-of-`X - C` simp lemmas).
- **Hypotheses**: none beyond `m`, `τ`.
- **Uses from project**: [`coxPhiAtJ`, `CoxMatrix`]
- **Used by**: `modularPolynomialCandidateAux_specializeY`, `modularPolynomialC_natDegree`
- **Visibility**: public
- **Lines**: 188-192, proof 2 lines
- **Notes**: none

### `theorem coxPhiFunction_map_eval`
- **Type**: `(m : ℕ+) (τ : ℍ) : (coxPhiFunction m).map (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ) = coxPhiAtJ m τ`
- **What**: Evaluating all function-valued coefficients of the Cox product at a point `τ` recovers the specialized complex polynomial `coxPhiAtJ m τ`.
- **How**: `Polynomial.map` is a ring homomorphism, so it distributes over the product (`Polynomial.map_prod`) and sends each factor `X − C(f)` to `X − C(f τ)`.
- **Hypotheses**: none beyond `m`, `τ`.
- **Uses from project**: [`coxPhiFunction`, `coxPhiAtJ`]
- **Used by**: `coxPhiFunction_coeff_apply`
- **Visibility**: public
- **Lines**: 194-198, proof 2 lines
- **Notes**: none

### `theorem coxPhiFunction_coeff_apply`
- **Type**: `(m : ℕ+) (n : ℕ) (τ : ℍ) : (coxPhiFunction m).coeff n τ = (coxPhiAtJ m τ).coeff n`
- **What**: Pointwise value of the `n`-th function-valued coefficient at `τ` equals the `n`-th coefficient of the specialized polynomial — coefficients and evaluation commute.
- **How**: Applies `congrArg (coeff n)` to `coxPhiFunction_map_eval` and simplifies `Polynomial.coeff_map`.
- **Hypotheses**: none beyond `m`, `n`, `τ`.
- **Uses from project**: [`coxPhiFunction`, `coxPhiAtJ`, `coxPhiFunction_map_eval`]
- **Used by**: `coxPhiFunction_coeff_slashInvariant`, `modularPolynomialCandidateAux_specializeY`
- **Visibility**: public
- **Lines**: 200-204, proof 1 line
- **Notes**: none

### `theorem coxPhiAtJ_eq_rightCosetProduct`
- **Type**: `(m : ℕ+) (τ : ℍ) : coxPhiAtJ m τ = ∏ c : Gamma0RightCosets m, (Polynomial.X - Polynomial.C (rightCosetEval m c τ))`
- **What**: Reindexing of equation (11.15): the Cox product over `C(m)` equals the same product indexed by the right cosets of `Γ₀(m)` in `SL₂(ℤ)`, with each root written as a coset evaluation `j_m(γ•τ)`.
- **How**: Each factor's root `j(σ·τ)` equals the evaluation of the corresponding coset under `rightCosetEval_equiv`, and the bijection `coxMatrixEquivRightCosets` reindexes the product via mathlib's `Equiv.prod_comp`.
- **Hypotheses**: none beyond `m`, `τ`.
- **Uses from project**: [`coxPhiAtJ`, `Gamma0RightCosets`, `rightCosetEval`, `rightCosetEval_equiv`, `coxMatrixEquivRightCosets`, `CoxMatrix`, `CoxMatrix.act`, `j`]
- **Used by**: `coxPhiAtJ_sl2_smul`, `modularPolynomialC_rightCosetProduct`
- **Visibility**: public
- **Lines**: 206-225, proof 15 lines
- **Notes**: none

### `theorem coxPhiAtJ_sl2_smul`
- **Type**: `(m : ℕ+) (δ : SL(2, ℤ)) (τ : ℍ) : coxPhiAtJ m (δ • τ) = coxPhiAtJ m τ`
- **What**: The specialized Cox product is invariant under the full modular group: replacing `τ` by `δ•τ` permutes the roots, leaving the polynomial unchanged. This is the key symmetry making the coefficients level-one modular functions.
- **How**: In the coset form (`coxPhiAtJ_eq_rightCosetProduct`), the action of `δ` on `τ` translates each factor by the coset permutation `rightCosetMul m δ` via `rightCosetEval_smul` (`j_m|_c(δ•τ) = j_m|_{δ·c}(τ)`), and mathlib's `Equiv.prod_comp` absorbs the permutation of the index set.
- **Hypotheses**: `δ ∈ SL₂(ℤ)`.
- **Uses from project**: [`coxPhiAtJ`, `coxPhiAtJ_eq_rightCosetProduct`, `Gamma0RightCosets`, `rightCosetEval`, `rightCosetMul`, `rightCosetEval_smul`]
- **Used by**: `coxPhiFunction_coeff_slashInvariant`
- **Visibility**: public
- **Lines**: 227-245, proof 14 lines
- **Notes**: none

### `theorem coxPhiFunction_coeff_slashInvariant`
- **Type**: `(m : ℕ+) (n : ℕ) (δ : SL(2, ℤ)) : ((coxPhiFunction m).coeff n) ∣[(0 : ℤ)] δ = (coxPhiFunction m).coeff n`
- **What**: Every function-valued coefficient of the Cox product is invariant under the weight-0 slash action of `SL₂(ℤ)`.
- **How**: In weight 0 the slash action is just precomposition with `δ` (via mathlib's `ModularForm.SL_slash_apply` and `zpow_zero`), so the claim reduces pointwise, via `coxPhiFunction_coeff_apply`, to the polynomial invariance `coxPhiAtJ_sl2_smul`.
- **Hypotheses**: `δ ∈ SL₂(ℤ)`.
- **Uses from project**: [`coxPhiFunction`, `coxPhiFunction_coeff_apply`, `coxPhiAtJ_sl2_smul`]
- **Used by**: `coxPhiFunction_coeff_widthOne_cuspMeromorphicAt`, `coxPhiFunction_coeff_isLevelOne`
- **Visibility**: public
- **Lines**: 247-254, proof 4 lines
- **Notes**: none

### `theorem coxPhiFunction_coeff_mdifferentiable`
- **Type**: `(m : ℕ+) (n : ℕ) : MDiff ((coxPhiFunction m).coeff n)`
- **What**: Every coefficient of the function-valued Cox product is holomorphic (manifold-differentiable) on the upper half-plane, since it is an elementary symmetric expression in the holomorphic roots `j(σ·τ)`.
- **How**: Each root is holomorphic: `levelJ m` is `MDiff` by `jN_differentiableAt` through `UpperHalfPlane.mdifferentiable_iff`, coset evaluations are compositions with the holomorphic Möbius action (`UpperHalfPlane.mdifferentiable_smul`), and Cox roots reduce to coset evaluations via `rightCosetEval_equiv`. For `n ≤ |C(m)|`, mathlib's Vieta identity `Finset.prod_X_add_C_coeff` writes the coefficient as a finite sum of finite products of negated roots, closed with `MDifferentiable.sum`/`.prod`; for `n > |C(m)|` the coefficient is zero (`Polynomial.coeff_eq_zero_of_natDegree_lt`) hence constant.
- **Hypotheses**: none beyond `m`, `n`.
- **Uses from project**: [`coxPhiFunction`, `levelJ`, `jN_differentiableAt`, `Gamma0RightCosets`, `rightCosetEval`, `rightCosetEval_equiv`, `coxMatrixEquivRightCosets`, `CoxMatrix`, `CoxMatrix.act`, `j`]
- **Used by**: `coxPhiFunction_coeff_meromorphicOnH`, `coxPhiFunction_coeff_polynomialInJ`
- **Visibility**: public
- **Lines**: 256-285, proof 26 lines
- **Notes**: preceded by `open scoped Manifold in`

### `theorem coxPhiFunction_coeff_widthM_cuspMeromorphicAt`
- **Type**: `(m : ℕ+) (n : ℕ) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) ((coxPhiFunction m).coeff n)) 0`
- **What**: Every Cox-product coefficient has a meromorphic q-expansion in the width-`m` cusp parameter `q = e^{2πiτ/m}`.
- **How**: The Cox product is a finite product of linear factors each of whose coefficients is width-`m` cusp-meromorphic (`coxLinearFactor_coeff_cuspMeromorphicAt`); the product-stability lemma `polynomial_prod_coeff_cuspMeromorphicAt` from AnalyticSupport.lean transfers this to every coefficient of the product.
- **Hypotheses**: none beyond `m`, `n`.
- **Uses from project**: [`coxPhiFunction`, `polynomial_prod_coeff_cuspMeromorphicAt`, `coxLinearFactor_coeff_cuspMeromorphicAt`, `CoxMatrix`, `CoxMatrix.act`, `j`]
- **Used by**: `coxPhiFunction_coeff_widthOne_cuspMeromorphicAt`
- **Visibility**: public
- **Lines**: 287-296, proof 5 lines
- **Notes**: none

### `theorem coxPhiFunction_coeff_widthOne_cuspMeromorphicAt`
- **Type**: `(m : ℕ+) (n : ℕ) : MeromorphicAt (cuspFunction 1 ((coxPhiFunction m).coeff n)) 0`
- **What**: Every Cox-product coefficient is meromorphic in the ordinary width-one cusp parameter `q = e^{2πiτ}` — the width-`m` expansion descends to width one because the coefficient is 1-periodic.
- **How**: Applies the project's width-descent lemma `meromorphicAt_cuspFunction_of_nat_mul` (a width-`m·1` cusp-meromorphic, 1-periodic function is width-1 cusp-meromorphic), feeding it the width-`m` result and 1-periodicity obtained from `SL₂(ℤ)`-slash-invariance via `periodic_comp_of_slashInvariant_one`.
- **Hypotheses**: none beyond `m`, `n` (uses `m ≠ 0` from `PNat.ne_zero`).
- **Uses from project**: [`coxPhiFunction`, `meromorphicAt_cuspFunction_of_nat_mul`, `coxPhiFunction_coeff_widthM_cuspMeromorphicAt`, `periodic_comp_of_slashInvariant_one`, `coxPhiFunction_coeff_slashInvariant`]
- **Used by**: `coxPhiFunction_coeff_isLevelOne`
- **Visibility**: public
- **Lines**: 299-306, proof 5 lines
- **Notes**: none

### `theorem coxPhiFunction_coeff_meromorphicOnH`
- **Type**: `(m : ℕ+) (n : ℕ) : ∀ z : ℂ, 0 < z.im → MeromorphicAt (((coxPhiFunction m).coeff n) ∘ UpperHalfPlane.ofComplex) z`
- **What**: Each coefficient, extended to `ℂ` via `ofComplex`, is meromorphic at every point of the open upper half-plane (in fact holomorphic there).
- **How**: Holomorphy on `ℍ` (`coxPhiFunction_coeff_mdifferentiable`) transfers through `UpperHalfPlane.mdifferentiable_iff` to `DifferentiableOn` of the extension; analyticity at each interior point (`DifferentiableOn.analyticAt` on the open set `UpperHalfPlane.isOpen_upperHalfPlaneSet`) implies `MeromorphicAt`.
- **Hypotheses**: `z ∈ ℂ` with `Im z > 0`.
- **Uses from project**: [`coxPhiFunction`, `coxPhiFunction_coeff_mdifferentiable`]
- **Used by**: `coxPhiFunction_coeff_isLevelOne`
- **Visibility**: public
- **Lines**: 308-316, proof 6 lines
- **Notes**: none

### `theorem coxPhiFunction_coeff_isLevelOne`
- **Type**: `(m : ℕ+) (n : ℕ) : IsLevelOneModularFunction ((coxPhiFunction m).coeff n)`
- **What**: Assembles the three preceding facts into the statement that each Cox-product coefficient is a level-one modular function (meromorphic on `ℍ`, weight-0 `SL₂(ℤ)`-invariant, meromorphic at the cusp) — the invariant-coefficient argument immediately preceding Cox's equation (11.14).
- **How**: Provides the three fields of `IsLevelOneModularFunction` directly: `coxPhiFunction_coeff_meromorphicOnH` for meromorphy on `ℍ`, `coxPhiFunction_coeff_slashInvariant` for invariance, and `coxPhiFunction_coeff_widthOne_cuspMeromorphicAt` for cusp meromorphy, rewriting `f(γ•τ) = f(τ)` from the slash identity to align the third field's statement.
- **Hypotheses**: none beyond `m`, `n`.
- **Uses from project**: [`coxPhiFunction`, `IsLevelOneModularFunction`, `coxPhiFunction_coeff_meromorphicOnH`, `coxPhiFunction_coeff_slashInvariant`, `coxPhiFunction_coeff_widthOne_cuspMeromorphicAt`]
- **Used by**: `coxPhiFunction_coeff_polynomialInJ`
- **Visibility**: public
- **Lines**: 318-333, proof 12 lines
- **Notes**: none

### `theorem coxPhiFunction_coeff_polynomialInJ`
- **Type**: `(m : ℕ+) (n : ℕ) : ∃ P : Polynomial ℂ, (coxPhiFunction m).coeff n = polynomialIn P j`
- **What**: Cox Lemma 11.10 applied to the coefficients: each coefficient of the Cox product, being a holomorphic level-one modular function, is a polynomial in the `j`-function.
- **How**: Direct application of the project's structure theorem `levelOne_polynomialInJ_of_holomorphic` (a holomorphic level-one modular function lies in `ℂ[j]`), with hypotheses supplied by `coxPhiFunction_coeff_isLevelOne` and `coxPhiFunction_coeff_mdifferentiable`.
- **Hypotheses**: none beyond `m`, `n`.
- **Uses from project**: [`coxPhiFunction`, `polynomialIn`, `j`, `levelOne_polynomialInJ_of_holomorphic`, `coxPhiFunction_coeff_isLevelOne`, `coxPhiFunction_coeff_mdifferentiable`]
- **Used by**: `coxCoefficientPolynomialAux`, `coxCoefficientPolynomialAux_eval`
- **Visibility**: public
- **Lines**: 335-340, proof 3 lines
- **Notes**: none

### `private def coxCoefficientPolynomialAux`
- **Type**: `(m : ℕ+) (n : ℕ) : Polynomial ℂ`
- **What**: A choice of polynomial `P_n ∈ ℂ[Y]` with `(coxPhiFunction m).coeff n = P_n(j)`, i.e. the `n`-th coefficient of `Φ_m` as a polynomial in the parameter variable.
- **How**: `Classical.choose` applied to the existence statement `coxPhiFunction_coeff_polynomialInJ`.
- **Hypotheses**: none.
- **Uses from project**: [`coxPhiFunction_coeff_polynomialInJ`]
- **Used by**: `coxCoefficientPolynomialAux_eval`, `modularPolynomialCandidateAux`
- **Visibility**: private
- **Lines**: 342-344
- **Notes**: `noncomputable`

### `private theorem coxCoefficientPolynomialAux_eval`
- **Type**: `(m : ℕ+) (n : ℕ) (τ : ℍ) : (coxCoefficientPolynomialAux m n).eval (j τ) = (coxPhiFunction m).coeff n τ`
- **What**: The defining property of the chosen coefficient polynomial: evaluating `P_n` at `j(τ)` recovers the value of the `n`-th Cox-product coefficient at `τ`.
- **How**: Unfolds `choose_spec` of `coxPhiFunction_coeff_polynomialInJ` at `τ`, using the definition of `polynomialIn` (pointwise `P.eval ∘ j`).
- **Hypotheses**: none beyond `m`, `n`, `τ`.
- **Uses from project**: [`coxCoefficientPolynomialAux`, `coxPhiFunction_coeff_polynomialInJ`, `polynomialIn`, `j`, `coxPhiFunction`]
- **Used by**: `modularPolynomialCandidateAux_specializeY`
- **Visibility**: private
- **Lines**: 346-351, proof 2 lines
- **Notes**: none

### `private def modularPolynomialCandidateAux`
- **Type**: `(m : ℕ+) : BivariatePolynomial ℂ`
- **What**: The explicit candidate for `Φ_m(X, Y)`: `X^{|C(m)|} + ∑_{n < |C(m)|} P_n(Y)·X^n`, with `P_n` the chosen coefficient polynomials — the monic bivariate polynomial whose `Y = j(τ)` specialization should be the Cox product.
- **How**: Definition: leading monomial `X^{|C(m)|}` plus the finite sum of monomials `monomial n (coxCoefficientPolynomialAux m n)` over `n ∈ range |C(m)|`.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial`, `CoxMatrix`, `coxCoefficientPolynomialAux`]
- **Used by**: `modularPolynomialCandidateAux_specializeY`, `modularPolynomialCandidateAux_monic`, `existsUnique_modularPolynomialC`
- **Visibility**: private
- **Lines**: 353-357
- **Notes**: `noncomputable`

### `private theorem modularPolynomialCandidateAux_specializeY`
- **Type**: `(m : ℕ+) (τ : ℍ) : (modularPolynomialCandidateAux m).specializeY (j τ) = coxPhiAtJ m τ`
- **What**: The candidate specializes correctly: substituting `Y = j(τ)` in the candidate yields the Cox product `∏_σ (X − j(σ·τ))`.
- **How**: A three-step `calc`: (1) specialization commutes with the sum-of-monomials shape; (2) each evaluated coefficient `P_n(j(τ))` equals `(coxPhiAtJ m τ).coeff n` by `coxCoefficientPolynomialAux_eval` and `coxPhiFunction_coeff_apply`; (3) `X^deg + ∑ coeff·X^n` reassembles to `coxPhiAtJ m τ` by the monic expansion `Monic.as_sum` (from `coxPhiAtJ_monic`) and the degree computation `coxPhiAtJ_natDegree`.
- **Hypotheses**: none beyond `m`, `τ`.
- **Uses from project**: [`modularPolynomialCandidateAux`, `BivariatePolynomial.specializeY`, `coxCoefficientPolynomialAux`, `coxCoefficientPolynomialAux_eval`, `coxPhiFunction_coeff_apply`, `coxPhiAtJ`, `coxPhiAtJ_monic`, `coxPhiAtJ_natDegree`, `CoxMatrix`, `j`]
- **Used by**: `existsUnique_modularPolynomialC`
- **Visibility**: private
- **Lines**: 359-380, proof 19 lines
- **Notes**: none

### `private theorem modularPolynomialCandidateAux_monic`
- **Type**: `(m : ℕ+) : (modularPolynomialCandidateAux m).Monic`
- **What**: The candidate is monic in the root variable `X`: the correction sum has degree strictly below `|C(m)|`.
- **How**: Mathlib's `Polynomial.monic_X_pow_add` reduces to bounding the sum's degree; `Polynomial.degree_sum_le` plus `Finset.sup_lt_iff` and `Polynomial.degree_monomial_le` show each monomial `n < |C(m)|` contributes degree `< |C(m)|`.
- **Hypotheses**: none beyond `m`.
- **Uses from project**: [`modularPolynomialCandidateAux`]
- **Used by**: `existsUnique_modularPolynomialC`
- **Visibility**: private
- **Lines**: 382-391, proof 8 lines
- **Notes**: none

### `theorem existsUnique_modularPolynomialC`
- **Type**: `(m : ℕ+) : ∃! Φ : BivariatePolynomial ℂ, Φ.Monic ∧ ∀ τ : ℍ, Φ.specializeY (j τ) = coxPhiAtJ m τ`
- **What**: Existence and uniqueness of Cox's equation (11.14): there is exactly one monic bivariate polynomial over `ℂ` whose every `Y = j(τ)` specialization equals the Cox product. This pins down `Φ_m` without choices in its characterization.
- **How**: Existence is the candidate with `modularPolynomialCandidateAux_monic` and `modularPolynomialCandidateAux_specializeY`. Uniqueness: any two such polynomials agree on all specializations at points of the image of `j`; since `j` is surjective onto `ℂ` (`j_surjective`), they agree on all specializations, and `BivariatePolynomial.specializeY_ext` (over the infinite domain `ℂ`) forces equality.
- **Hypotheses**: none beyond `m`.
- **Uses from project**: [`BivariatePolynomial`, `BivariatePolynomial.specializeY`, `coxPhiAtJ`, `modularPolynomialCandidateAux`, `modularPolynomialCandidateAux_monic`, `modularPolynomialCandidateAux_specializeY`, `BivariatePolynomial.specializeY_ext`, `j_surjective`, `j`]
- **Used by**: `modularPolynomialC`, `modularPolynomialC_monic`, `modularPolynomialC_specializeY`
- **Visibility**: public
- **Lines**: 394-406, proof 8 lines
- **Notes**: none

### `def modularPolynomialC`
- **Type**: `(m : ℕ+) : BivariatePolynomial ℂ`
- **What**: Cox's complex modular polynomial `Φ_m(X, Y)`, defined as the unique monic bivariate polynomial with `Φ_m(X, j(τ)) = ∏_{σ ∈ C(m)}(X − j(σ·τ))` for all `τ`.
- **How**: `Classical.choose` of `existsUnique_modularPolynomialC`.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial`, `existsUnique_modularPolynomialC`]
- **Used by**: `modularPolynomialC_monic`, `modularPolynomialC_specializeY`, `modularPolynomialC_rightCosetProduct`, `modularPolynomialC_eval_levelJ_j`, `modularPolynomialC_natDegree` (also the central object of Irreducibility.lean and IntegralDescent.lean)
- **Visibility**: public
- **Lines**: 408-410
- **Notes**: `noncomputable`

### `theorem modularPolynomialC_monic`
- **Type**: `(m : ℕ+) : (modularPolynomialC m).Monic`
- **What**: `Φ_m` is monic in the root variable `X`.
- **How**: First component of the `choose_spec` of `existsUnique_modularPolynomialC`.
- **Hypotheses**: none beyond `m`.
- **Uses from project**: [`modularPolynomialC`, `existsUnique_modularPolynomialC`]
- **Used by**: `modularPolynomialC_natDegree` (also Irreducibility.lean)
- **Visibility**: public
- **Lines**: 412-413, proof 1 line
- **Notes**: none

### `theorem modularPolynomialC_specializeY`
- **Type**: `(m : ℕ+) (τ : ℍ) : (modularPolynomialC m).specializeY (j τ) = coxPhiAtJ m τ`
- **What**: Cox's equation (11.15): the specialization `Φ_m(X, j(τ))` equals the Cox product `∏_{σ ∈ C(m)}(X − j(σ·τ))`.
- **How**: Second component of the `choose_spec` of `existsUnique_modularPolynomialC`, applied at `τ`.
- **Hypotheses**: none beyond `m`, `τ`.
- **Uses from project**: [`modularPolynomialC`, `existsUnique_modularPolynomialC`, `BivariatePolynomial.specializeY`, `coxPhiAtJ`, `j`]
- **Used by**: `modularPolynomialC_rightCosetProduct`, `modularPolynomialC_eval_levelJ_j`, `modularPolynomialC_natDegree`
- **Visibility**: public
- **Lines**: 415-418, proof 1 line
- **Notes**: none

### `theorem modularPolynomialC_rightCosetProduct`
- **Type**: `(m : ℕ+) (τ : ℍ) : (modularPolynomialC m).specializeY (j τ) = ∏ c : Gamma0RightCosets m, (Polynomial.X - Polynomial.C (rightCosetEval m c τ))`
- **What**: Cox's equation (11.14): the specialization `Φ_m(X, j(τ))` equals the product of linear factors indexed by right cosets of `Γ₀(m)`.
- **How**: Chains `modularPolynomialC_specializeY` with the reindexing `coxPhiAtJ_eq_rightCosetProduct`.
- **Hypotheses**: none beyond `m`, `τ`.
- **Uses from project**: [`modularPolynomialC`, `modularPolynomialC_specializeY`, `coxPhiAtJ_eq_rightCosetProduct`, `Gamma0RightCosets`, `rightCosetEval`, `BivariatePolynomial.specializeY`, `j`]
- **Used by**: unused in file (consumed by `modularPolynomialHolomorphic_eq_product` in Irreducibility.lean)
- **Visibility**: public
- **Lines**: 420-425, proof 1 line
- **Notes**: none

### `theorem modularPolynomialC_eval_levelJ_j`
- **Type**: `(m : ℕ+) (τ : ℍ) : (modularPolynomialC m).eval (levelJ m τ) (j τ) = 0`
- **What**: The distinguished root relation `Φ_m(j(mτ), j(τ)) = 0`: the level-`m` `j`-function is a root of the modular polynomial specialized at `j(τ)`.
- **How**: Reduces bivariate evaluation to the specialization (`BivariatePolynomial.specializeY_eval`, `modularPolynomialC_specializeY`), then kills the product `coxPhiAtJ` at the factor indexed by the base matrix `σ₀ = (m 0; 0 1)` via `Finset.prod_eq_zero`, using `j_act_sigmaZero` (`j(σ₀·τ) = j(mτ) = levelJ m τ`).
- **Hypotheses**: none beyond `m`, `τ`.
- **Uses from project**: [`modularPolynomialC`, `BivariatePolynomial.eval`, `BivariatePolynomial.specializeY_eval`, `modularPolynomialC_specializeY`, `coxPhiAtJ`, `sigmaZero`, `j_act_sigmaZero`, `levelJ`, `j`]
- **Used by**: unused in file (public API export)
- **Visibility**: public
- **Lines**: 427-435, proof 6 lines
- **Notes**: none

### `theorem modularPolynomialC_natDegree`
- **Type**: `(m : ℕ+) : (modularPolynomialC m).natDegree = Fintype.card (CoxMatrix m)`
- **What**: The degree of `Φ_m` in the root variable `X` is `|C(m)|`, the index-type count of Cox matrices.
- **How**: Since `Φ_m` is monic, its degree is preserved by the specialization map at any point (`Monic.natDegree_map` along `Polynomial.evalRingHom (j i)` at the sample point `τ = i`), and the specialized degree is `coxPhiAtJ_natDegree`.
- **Hypotheses**: none beyond `m`.
- **Uses from project**: [`modularPolynomialC`, `modularPolynomialC_monic`, `modularPolynomialC_specializeY`, `coxPhiAtJ_natDegree`, `BivariatePolynomial.specializeY`, `CoxMatrix`, `j`]
- **Used by**: unused in file (consumed by `modularPolynomialRatFunc_irreducible` in Irreducibility.lean)
- **Visibility**: public
- **Lines**: 437-447, proof 8 lines
- **Notes**: none

### File Summary
- Total declarations: 43 (12 defs/abbrevs, 31 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): [`BivariatePolynomial` (10+ uses), `coxPhiAtJ` (11 uses), `coxPhiFunction` (10 uses), `BivariatePolynomial.specializeY` (8 uses), `BivariatePolynomial.diagonal` (4 uses), `BivariatePolynomial.eval` (4 uses), `modularPolynomialC` (5 uses), `existsUnique_modularPolynomialC` (3 uses), `modularPolynomialC_specializeY` (3 uses), `modularPolynomialCandidateAux` (3 uses)]
- Unused declarations (not used by anything in this file): [`BivariatePolynomial.varX`, `BivariatePolynomial.varY`, `BivariatePolynomial.eval_swap`, `BivariatePolynomial.coeff_coeff_swap`, `BivariatePolynomial.map_swap`, `BivariatePolynomial.diagonal_eval`, `BivariatePolynomial.diagonal_map`, `BivariatePolynomial.diagonal_eval₂`, `BivariatePolynomial.diagonal_swap`, `modularPolynomialC_rightCosetProduct`, `modularPolynomialC_eval_levelJ_j`, `modularPolynomialC_natDegree`] — the last three are exports consumed by Irreducibility.lean/downstream; the swap/diagonal/var API is presumably for IntegralDescent/SingularModuli
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: []
