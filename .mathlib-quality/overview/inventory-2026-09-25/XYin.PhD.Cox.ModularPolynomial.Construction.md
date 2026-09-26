# Inventory: XYin/PhD/Cox/ModularPolynomial/Construction.lean  (379 lines)

Defines the project's bivariate-polynomial API (`BivariatePolynomial R := R[X][Y]` with Cox's convention outer variable = `X` (root), inner = `Y` (parameter)), the specialized Cox product `coxPhiAtJ m τ = ∏_{σ∈C(m)} (X - j(σ·τ))` and its function-valued version `coxPhiFunction m`, proves that every coefficient of `coxPhiFunction m` is a level-one holomorphic modular function hence a polynomial in `j` (Cox Lemma 11.10), and builds the complex modular polynomial `modularPolynomialC m ∈ ℂ[X][Y]` as the unique monic bivariate polynomial with `Φ(X, j(τ)) = coxPhiAtJ m τ` (Cox (11.14)/(11.15)).

## Declarations

### `abbrev Cox.BivariatePolynomial`
- **Type**: `(R : Type*) [Semiring R] : Type* := Polynomial (Polynomial R)`
- **What**: Bivariate polynomials `R[X][Y]`, read with the outer variable as Cox's `X` and the inner as Cox's `Y`.
- **How**: Abbreviation of mathlib's `Polynomial (Polynomial R)` (= scoped notation `R[X][Y]`, Mathlib/Algebra/Polynomial/Bivariate.lean:29).
- **Hypotheses**: `R` a semiring.
- **Uses from project**: `[]`
- **Used by**: everything below that mentions bivariate polynomials (`varX`, `varY`, `eval`, `specializeY`, `map`, `diagonal`, all `BivariatePolynomial.*` lemmas, `modularPolynomialCandidateAux`, `existsUnique_modularPolynomialC`, `modularPolynomialC`)
- **Visibility**: public
- **Lines**: 24–26, proof body ≈ 0 lines
- **Notes**: Heavily used across Arithmetic, LevelThree, SymmetricCubicLaurent, Kronecker, KroneckerFrobenius, DiagonalLaurent. Note the variable-name clash with mathlib: mathlib's `Y` notation is the OUTER variable (`Polynomial.X (R := Polynomial _)`), i.e. Cox's `X`.

### `def Cox.BivariatePolynomial.varX`
- **Type**: `[Semiring R] : BivariatePolynomial R := Polynomial.X`
- **What**: Cox's root variable `X` (the outer polynomial variable).
- **How**: `Polynomial.X` at the outer level — this is mathlib's scoped notation `Y` (Bivariate.lean:26).
- **Hypotheses**: none.
- **Uses from project**: `BivariatePolynomial`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 32–33, proof body ≈ 0 lines
- **Notes**: Used externally in LevelThree.lean (7), KroneckerFrobenius.lean (4), Kronecker.lean (3). No `varX_eq`/simp lemmas here; consumers unfold by `rfl`/`simp [varX]`.

### `def Cox.BivariatePolynomial.varY`
- **Type**: `[Semiring R] : BivariatePolynomial R := Polynomial.C Polynomial.X`
- **What**: Cox's parameter variable `Y` (the inner variable, viewed as a constant of the outer ring).
- **How**: `C X`; mathlib writes this literally as `C X` (see `aevalAeval_X`, Bivariate.lean:243, `Bivariate.swap_X`, :259).
- **Hypotheses**: none.
- **Uses from project**: `BivariatePolynomial`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 35–36, proof body ≈ 0 lines
- **Notes**: Same external users as `varX`. Naming inverts mathlib's (`varX = Y`, `varY = C X`).

### `def Cox.BivariatePolynomial.eval`
- **Type**: `[Semiring R] (Φ : BivariatePolynomial R) (x y : R) : R := Φ.evalEval y x`
- **What**: Semantic evaluation `Φ(x, y)` with `x` substituted for the outer/root variable and `y` for the inner one.
- **How**: Argument-swapped wrapper of mathlib `Polynomial.evalEval x y p = eval x (eval (C y) p)` (Bivariate.lean:44), whose first argument is the INNER variable.
- **Hypotheses**: none.
- **Uses from project**: `BivariatePolynomial`
- **Used by**: `specializeY_eval`, `eval_swap`, `diagonal_eval`, `modularPolynomialC_eval_levelJ_j`
- **Visibility**: public
- **Lines**: 38–41, proof body ≈ 0 lines
- **Notes**: No `eval_add/_mul/_C/_X/_sum` companion lemmas here — consumers unfold to `evalEval` and use mathlib's `evalEval_*` simp set (Bivariate.lean:49–145). Raw `evalEval` is ALSO used directly in this batch (Interpolation.lean:355–393, 398, 436, 446) and in `RationalInTwo` (ModularFunction/CuspData.lean:57–59) and ModularFunctionField.lean:38,91–93: the two conventions coexist, with the same semantics (`P.evalEval (j τ) (levelJ N τ) = BivariatePolynomial.eval P (levelJ N τ) (j τ)`), see Observations.

### `def Cox.BivariatePolynomial.specializeY`
- **Type**: `[CommSemiring R] (y : R) (Φ : BivariatePolynomial R) : Polynomial R := Polynomial.map (Polynomial.evalRingHom y) Φ`
- **What**: Substitute `y` for the inner variable `Y`, leaving a univariate polynomial in `X`.
- **How**: Coefficientwise evaluation `Polynomial.map (evalRingHom y)`; mathlib uses exactly this expression unnamed in `map_evalRingHom_eval` (Bivariate.lean:162).
- **Hypotheses**: `R` commutative.
- **Uses from project**: `BivariatePolynomial`
- **Used by**: `specializeY_eval`, `specializeY_ext`, `modularPolynomialCandidateAux_specializeY`, `existsUnique_modularPolynomialC`, `modularPolynomialC_specializeY`, `modularPolynomialC_rightCosetProduct`, `modularPolynomialC_eval_levelJ_j`, `modularPolynomialC_natDegree`
- **Visibility**: public
- **Lines**: 43–45, proof body ≈ 0 lines
- **Notes**: Used externally only through the `modularPolynomialC_specializeY`/`specializeY_eval` pair (SingularModuli.lean:213–214, CyclicSublattice/Classification.lean:330–331) and Interpolation/Irreducibility. No `specializeY_add/_mul/_C/_X/_coeff` lemmas (the coefficient formula `(specializeY y Φ).coeff n = (Φ.coeff n).eval y` is re-derived inline by `simp [specializeY, coeff_map]` at L83, L311, Irreducibility.lean:43, IntegralDescent.lean:272).

### `def Cox.BivariatePolynomial.map`
- **Type**: `[Semiring R] [Semiring S] (f : R →+* S) (Φ : BivariatePolynomial R) : BivariatePolynomial S := Polynomial.map (Polynomial.mapRingHom f) Φ`
- **What**: Apply a ring homomorphism to every coefficient of a bivariate polynomial.
- **How**: `Polynomial.map (mapRingHom f)`; mathlib uses exactly `p.map (mapRingHom f)` unnamed (Bivariate.lean:172–182).
- **Hypotheses**: none.
- **Uses from project**: `BivariatePolynomial`
- **Used by**: `map_swap`, `diagonal_map`
- **Visibility**: public
- **Lines**: 47–50, proof body ≈ 0 lines
- **Notes**: Heavily used externally (Arithmetic 11, LevelThree 8, Kronecker 6, KroneckerFrobenius 2, SingularModuli, Classification, IntegralDescent). No `map_eval`/`map_specializeY`/`map_coeff` companions here: `Polynomial.map_mapRingHom_evalEval` (Bivariate.lean:179) covers `map`∘`eval`.

### `def Cox.BivariatePolynomial.diagonal`
- **Type**: `[CommSemiring R] (Φ : BivariatePolynomial R) : Polynomial R := Polynomial.eval Polynomial.X Φ`
- **What**: The diagonal specialization `Φ(X, X)`.
- **How**: Evaluate the outer variable at the inner `X`.
- **Hypotheses**: `R` commutative.
- **Uses from project**: `BivariatePolynomial`
- **Used by**: `diagonal_eval`, `diagonal_map`, `diagonal_eval₂`, `diagonal_swap`
- **Visibility**: public
- **Lines**: 52–54, proof body ≈ 0 lines
- **Notes**: Used externally in Arithmetic.lean (11) and DiagonalLaurent.lean (3). No mathlib analogue found (searched Bivariate.lean for `diagonal`, `eval X`, `eval_C_X`).

### `def Cox.coxPhiAtJ`
- **Type**: `(m : ℕ+) (τ : ℍ) : Polynomial ℂ := ∏ σ : CoxMatrix m, (Polynomial.X - Polynomial.C (j (σ.act τ)))`
- **What**: Cox (11.15): the monic polynomial in `X` whose roots are the Cox conjugates `j(σ·τ)`, `σ ∈ C(m)`.
- **How**: Finite product of linear factors over the finite type `CoxMatrix m`.
- **Hypotheses**: none.
- **Uses from project**: `CoxMatrix`, `CoxMatrix.act`, `j`
- **Used by**: `coxPhiAtJ_monic`, `coxPhiAtJ_natDegree`, `coxPhiFunction_map_eval`, `coxPhiFunction_coeff_apply`, `coxPhiAtJ_eq_rightCosetProduct`, `coxPhiAtJ_sl2_smul`, `modularPolynomialCandidateAux_specializeY`, `existsUnique_modularPolynomialC`, `modularPolynomialC_specializeY`, `modularPolynomialC_eval_levelJ_j`, `modularPolynomialC_natDegree`
- **Visibility**: public
- **Lines**: 58–60, proof body ≈ 0 lines
- **Notes**: `noncomputable def` inside a `noncomputable section` (redundant keyword). Definitionally `Lagrange.nodal Finset.univ (fun σ ↦ j (σ.act τ))` (Mathlib/LinearAlgebra/Lagrange.lean:543, `nodal_eq` is `rfl`).

### `def Cox.coxPhiFunction`
- **Type**: `(m : ℕ+) : Polynomial (ℍ → ℂ) := ∏ σ : CoxMatrix m, (Polynomial.X - Polynomial.C (fun τ ↦ j (σ.act τ)))`
- **What**: The same Cox product with function-valued coefficients (before evaluating `τ`), so that coefficients can be studied as functions on `ℍ`.
- **How**: Same product in the polynomial ring over the commutative ring `ℍ → ℂ`.
- **Hypotheses**: none.
- **Uses from project**: `CoxMatrix`, `CoxMatrix.act`, `j`
- **Used by**: `coxPhiFunction_map_eval`, `coxPhiFunction_coeff_apply`, `coxPhiFunction_coeff_slashInvariant`, `coxPhiFunction_coeff_mdifferentiable`, `coxPhiFunction_coeff_widthM_cuspMeromorphicAt`, `coxPhiFunction_coeff_widthOne_cuspMeromorphicAt`, `coxPhiFunction_coeff_modularFunction`, `coe_coxPhiFunction_coeff_modularFunction`, `coxPhiFunction_coeff_polynomialInJ`, `coxCoefficientPolynomialAux_eval`
- **Visibility**: public
- **Lines**: 62–65, proof body ≈ 0 lines
- **Notes**: Definitionally `Lagrange.nodal Finset.univ (fun σ τ ↦ j (σ.act τ))` over `ℍ → ℂ`. Used externally by IntegralDescent.lean only.

### `theorem Cox.BivariatePolynomial.specializeY_eval`
- **Type**: `{R} [CommSemiring R] (Φ : BivariatePolynomial R) (x y : R) : (specializeY y Φ).eval x = eval Φ x y`
- **What**: Evaluating at `x` after substituting `y` for `Y` is the bivariate evaluation `Φ(x,y)`.
- **How**: Exactly mathlib `Polynomial.map_evalRingHom_eval y x Φ` (Bivariate.lean:162).
- **Hypotheses**: `R` commutative.
- **Uses from project**: `BivariatePolynomial`, `specializeY`, `eval`
- **Used by**: `modularPolynomialC_eval_levelJ_j`
- **Visibility**: public
- **Lines**: 69–72, proof body ≈ 1 line
- **Notes**: One-line wrapper of a mathlib lemma; used externally at SingularModuli.lean:213 and Classification.lean:330.

### `theorem Cox.BivariatePolynomial.specializeY_ext`
- **Type**: `{R} [CommRing R] [IsDomain R] [Infinite R] {Φ Ψ : BivariatePolynomial R} (h : ∀ y : R, Φ.specializeY y = Ψ.specializeY y) : Φ = Ψ`
- **What**: Over an infinite domain a bivariate polynomial is determined by all its `Y`-specializations.
- **How**: `Polynomial.ext` on the outer coefficient index `n`, then `Polynomial.funext` (Mathlib/Algebra/Polynomial/Roots.lean:452: a polynomial over an infinite domain is determined by its values) applied to the coefficient polynomials, using `(specializeY y Φ).coeff n = (Φ.coeff n).eval y` (`Polynomial.coeff_map`).
- **Hypotheses**: `R` an infinite integral domain.
- **Uses from project**: `BivariatePolynomial`, `specializeY`
- **Used by**: `existsUnique_modularPolynomialC`
- **Visibility**: public
- **Lines**: 74–83, proof body ≈ 6 lines
- **Notes**: No external users. Could be stated as an `ext`-style lemma on `Polynomial.map (evalRingHom y)`.

### `theorem Cox.BivariatePolynomial.eval_swap`
- **Type**: `{R} [CommSemiring R] (Φ : BivariatePolynomial R) (x y : R) : eval (Polynomial.Bivariate.swap Φ) x y = eval Φ y x`
- **What**: Swapping the two variables exchanges the two evaluation arguments.
- **How**: mathlib `Polynomial.Bivariate.aevalAeval_swap` (Bivariate.lean:286) transported along `coe_aevalAeval_eq_evalEval` (:237).
- **Hypotheses**: `R` commutative.
- **Uses from project**: `BivariatePolynomial`, `eval`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 87–93, proof body ≈ 2 lines
- **Notes**: External user: Arithmetic.lean (1). Essentially mathlib's lemma restated for `evalEval`; a mathlib `evalEval_swap` would make it redundant.

### `theorem Cox.BivariatePolynomial.coeff_coeff_swap`
- **Type**: `{R} [CommSemiring R] (Φ : BivariatePolynomial R) (i j : ℕ) : ((Polynomial.Bivariate.swap Φ).coeff i).coeff j = (Φ.coeff j).coeff i`
- **What**: The `(i,j)` coefficient of the swapped polynomial is the `(j,i)` coefficient of the original.
- **How**: `Polynomial.induction_on'`; the monomial case uses `Bivariate.swap_monomial` (Bivariate.lean:277), `coeff_mul_C`, `coeff_map` and `coeff_monomial`.
- **Hypotheses**: `R` commutative.
- **Uses from project**: `BivariatePolynomial`
- **Used by**: `map_swap`
- **Visibility**: public
- **Lines**: 95–105, proof body ≈ 6 lines
- **Notes**: No mathlib analogue (grep of Bivariate.lean: only `swap_monomial_monomial`, :281). PR candidate (`Polynomial.Bivariate.coeff_coeff_swap`). External users: SymmetricCubicLaurent, LevelThree, Arithmetic.

### `theorem Cox.BivariatePolynomial.map_swap`
- **Type**: `{R S} [CommSemiring R] [CommSemiring S] (f : R →+* S) (Φ : BivariatePolynomial R) : map f (Polynomial.Bivariate.swap Φ) = Polynomial.Bivariate.swap (map f Φ)`
- **What**: Coefficientwise ring maps commute with swapping the variables.
- **How**: Double coefficient `ext` and `coeff_coeff_swap` + `Polynomial.coeff_map`.
- **Hypotheses**: `R`, `S` commutative.
- **Uses from project**: `BivariatePolynomial`, `map`, `coeff_coeff_swap`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 107–113, proof body ≈ 2 lines
- **Notes**: No mathlib analogue (searched `swap_map`, `map_swap`, `mapRingHom` in Bivariate.lean; `Bivariate.aveal_eq_map_swap` :295 is different). PR candidate. External users: Arithmetic (3), LevelThree (1).

### `theorem Cox.BivariatePolynomial.diagonal_eval`
- **Type**: `{R} [CommSemiring R] (Φ : BivariatePolynomial R) (x : R) : (diagonal Φ).eval x = eval Φ x x`
- **What**: Evaluating the diagonal at `x` is the bivariate evaluation at `(x,x)`.
- **How**: mathlib `Polynomial.eval₂_evalRingHom` (Bivariate.lean:159, `eval₂ (evalRingHom x) = evalEval x`) and `Polynomial.hom_eval₂` to push `evalRingHom x` through `eval X Φ`.
- **Hypotheses**: `R` commutative.
- **Uses from project**: `BivariatePolynomial`, `diagonal`, `eval`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 115–123, proof body ≈ 5 lines
- **Notes**: External users: SingularModuli, DiagonalLaurent, Arithmetic.

### `theorem Cox.BivariatePolynomial.diagonal_map`
- **Type**: `{R S} [CommSemiring R] [CommSemiring S] (f : R →+* S) (Φ : BivariatePolynomial R) : diagonal (map f Φ) = (diagonal Φ).map f`
- **What**: Coefficient maps commute with the diagonal specialization.
- **How**: mathlib `Polynomial.map_mapRingHom_eval_map` (Bivariate.lean:172) at `q := X` with `Polynomial.map_X`.
- **Hypotheses**: `R`, `S` commutative.
- **Uses from project**: `BivariatePolynomial`, `diagonal`, `map`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 125–131, proof body ≈ 2 lines
- **Notes**: One-line wrapper of a mathlib lemma. External user: Arithmetic (2).

### `theorem Cox.BivariatePolynomial.diagonal_eval₂`
- **Type**: `{R S} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x : S) (Φ : BivariatePolynomial R) : (diagonal Φ).eval₂ f x = Φ.eval₂ (Polynomial.eval₂RingHom f x) x`
- **What**: Evaluating the diagonal through `f` at `x` is simultaneous `eval₂` of both variables at `x`.
- **How**: `Polynomial.hom_eval₂` with `g := eval₂RingHom f x` applied to `eval X Φ`.
- **Hypotheses**: `R`, `S` commutative.
- **Uses from project**: `BivariatePolynomial`, `diagonal`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 133–141, proof body ≈ 3 lines
- **Notes**: Compare mathlib `Polynomial.eval₂_eval₂RingHom_apply` (Bivariate.lean:194): the RHS equals `(map f Φ).evalEval x x`, so this lemma is `diagonal_map` + `eval_map` + `diagonal_eval`. External users: SingularModuli, DiagonalLaurent.

### `theorem Cox.BivariatePolynomial.diagonal_swap`
- **Type**: `{R} [CommSemiring R] (Φ : BivariatePolynomial R) : diagonal (Polynomial.Bivariate.swap Φ) = diagonal Φ`
- **What**: The diagonal is symmetric under swapping the variables.
- **How**: `Polynomial.induction_on'`; monomial case by `Bivariate.swap_monomial` and `eval_map`/`eval₂_C_X`/`eval_monomial`.
- **Hypotheses**: `R` commutative.
- **Uses from project**: `BivariatePolynomial`, `diagonal`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 143–156, proof body ≈ 8 lines
- **Notes**: `@[simp]`. No mathlib analogue. External user: Arithmetic (1).

### `theorem Cox.coxPhiAtJ_monic`
- **Type**: `(m : ℕ+) (τ : ℍ) : (coxPhiAtJ m τ).Monic`
- **What**: The specialized Cox product is monic in `X`.
- **How**: mathlib `Polynomial.monic_prod_X_sub_C` (Mathlib/Algebra/Polynomial/Roots.lean).
- **Hypotheses**: none.
- **Uses from project**: `coxPhiAtJ`, `CoxMatrix`, `CoxMatrix.act`, `j`
- **Used by**: `modularPolynomialCandidateAux_specializeY`
- **Visibility**: public
- **Lines**: 158–162, proof body ≈ 2 lines
- **Notes**: `classical`. Equals `Lagrange.nodal_monic` (Lagrange.lean:568) since `coxPhiAtJ` is definitionally a `nodal`.

### `theorem Cox.coxPhiAtJ_natDegree`
- **Type**: `(m : ℕ+) (τ : ℍ) : (coxPhiAtJ m τ).natDegree = Fintype.card (CoxMatrix m)`
- **What**: The degree of the Cox product is `|C(m)|`.
- **How**: `simp [coxPhiAtJ]` via the `natDegree_multiset_prod_X_sub_C_eq_card` family (Mathlib/Algebra/Polynomial/BigOperators.lean:328–337) and `Finset.card_univ`.
- **Hypotheses**: none.
- **Uses from project**: `coxPhiAtJ`, `CoxMatrix`
- **Used by**: `modularPolynomialCandidateAux_specializeY`, `modularPolynomialC_natDegree`
- **Visibility**: public
- **Lines**: 164–168, proof body ≈ 2 lines
- **Notes**: Equals `Lagrange.natDegree_nodal` (Lagrange.lean:551).

### `theorem Cox.coxPhiFunction_map_eval`
- **Type**: `(m : ℕ+) (τ : ℍ) : (coxPhiFunction m).map (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ) = coxPhiAtJ m τ`
- **What**: Evaluating all function-valued coefficients at `τ` recovers the specialized product.
- **How**: `Polynomial.map_prod` and `simp` with `map_sub`, `map_X`, `map_C`.
- **Hypotheses**: none.
- **Uses from project**: `coxPhiFunction`, `coxPhiAtJ`
- **Used by**: `coxPhiFunction_coeff_apply`
- **Visibility**: public
- **Lines**: 170–174, proof body ≈ 2 lines
- **Notes**: `classical`. Twin of `Interpolation.interpolationFunction_map_eval_aux` (Interpolation.lean:105–112).

### `theorem Cox.coxPhiFunction_coeff_apply`
- **Type**: `(m : ℕ+) (n : ℕ) (τ : ℍ) : (coxPhiFunction m).coeff n τ = (coxPhiAtJ m τ).coeff n`
- **What**: The `n`-th function coefficient evaluated at `τ` is the `n`-th coefficient of the specialized product.
- **How**: Coefficient `n` of `coxPhiFunction_map_eval` via `Polynomial.coeff_map`.
- **Hypotheses**: none.
- **Uses from project**: `coxPhiFunction`, `coxPhiAtJ`, `coxPhiFunction_map_eval`
- **Used by**: `coxPhiFunction_coeff_slashInvariant`, `modularPolynomialCandidateAux_specializeY`
- **Visibility**: public
- **Lines**: 176–180, proof body ≈ 2 lines
- **Notes**: External user: IntegralDescent.lean:271. Twin of `Interpolation.interpolationFunction_coeff_apply_aux` (Interpolation.lean:114–119).

### `theorem Cox.coxPhiAtJ_eq_rightCosetProduct`
- **Type**: `(m : ℕ+) (τ : ℍ) : coxPhiAtJ m τ = ∏ c : Gamma0RightCosets m, (Polynomial.X - Polynomial.C (rightCosetEval m c τ))`
- **What**: Cox (11.14): the product over `C(m)` equals the product over right cosets `Γ₀(m)\SL₂(ℤ)`.
- **How**: Reindex with `Equiv.prod_comp (coxMatrixEquivRightCosets m)` and `rightCosetEval_equiv`.
- **Hypotheses**: none.
- **Uses from project**: `coxPhiAtJ`, `Gamma0RightCosets`, `rightCosetEval`, `rightCosetEval_equiv`, `coxMatrixEquivRightCosets`
- **Used by**: `coxPhiAtJ_sl2_smul`, `modularPolynomialC_rightCosetProduct`
- **Visibility**: public
- **Lines**: 182–190, proof body ≈ 3 lines
- **Notes**: `classical`. Twin of `Interpolation.interpolationAt_eq_cosets_aux` (Interpolation.lean:40–52).

### `theorem Cox.coxPhiAtJ_sl2_smul`
- **Type**: `(m : ℕ+) (δ : SL(2, ℤ)) (τ : ℍ) : coxPhiAtJ m (δ • τ) = coxPhiAtJ m τ`
- **What**: The specialized Cox product is `SL₂(ℤ)`-invariant in `τ`.
- **How**: Coset form + `rightCosetEval_smul` (right multiplication by `δ` permutes cosets) + reindexing by the bijection `rightCosetMul m δ` (`Equiv.prod_comp`).
- **Hypotheses**: none.
- **Uses from project**: `coxPhiAtJ`, `coxPhiAtJ_eq_rightCosetProduct`, `rightCosetEval_smul`, `rightCosetMul`, `Gamma0RightCosets`, `rightCosetEval`
- **Used by**: `coxPhiFunction_coeff_slashInvariant`
- **Visibility**: public
- **Lines**: 192–198, proof body ≈ 3 lines
- **Notes**: `classical`. Twin of `Interpolation.interpolationAtCosets_smul_aux` (Interpolation.lean:54–67).

### `theorem Cox.coxPhiFunction_coeff_slashInvariant`
- **Type**: `(m : ℕ+) (n : ℕ) (δ : SL(2, ℤ)) : ((coxPhiFunction m).coeff n) ∣[(0 : ℤ)] δ = (coxPhiFunction m).coeff n`
- **What**: Every coefficient of the Cox product is a weight-0 `SL₂(ℤ)`-invariant function.
- **How**: `funext`; `ModularForm.SL_slash_apply` at weight 0 reduces to `f (δ • τ) = f τ`, then `coxPhiFunction_coeff_apply` twice and `coxPhiAtJ_sl2_smul`.
- **Hypotheses**: none.
- **Uses from project**: `coxPhiFunction`, `coxPhiFunction_coeff_apply`, `coxPhiAtJ_sl2_smul`
- **Used by**: `coxPhiFunction_coeff_widthOne_cuspMeromorphicAt`, `coxPhiFunction_coeff_modularFunction`
- **Visibility**: public
- **Lines**: 200–207, proof body ≈ 3 lines
- **Notes**: External user: IntegralDescent.lean:243. Twin of `Interpolation.interpolation_coeff_slashInvariant_aux` (Interpolation.lean:252–260).

### `theorem Cox.coxPhiFunction_coeff_mdifferentiable`
- **Type**: `(m : ℕ+) (n : ℕ) : MDiff ((coxPhiFunction m).coeff n)`
- **What**: Every coefficient of the Cox product is holomorphic on `ℍ`.
- **How**: For `n ≤ |C(m)|`, Vieta (`Finset.prod_X_add_C_coeff`, Mathlib/RingTheory/Polynomial/Vieta.lean:67) expresses the coefficient as a sum over `powersetCard (|C(m)| - n)` of products of `-j∘σ`; each root `j(σ·τ)` is holomorphic as `levelJ_mdifferentiable` composed with `UpperHalfPlane.mdifferentiable_smul`; close with `MDifferentiable.sum`/`.prod`. For `n > |C(m)|` the coefficient is `0` (`Polynomial.coeff_eq_zero_of_natDegree_lt`).
- **Hypotheses**: none.
- **Uses from project**: `coxPhiFunction`, `Gamma0RightCosets`, `rightCosetEval`, `levelJ_mdifferentiable`, `rightCosetEval_equiv`, `coxMatrixEquivRightCosets`, `CoxMatrix`, `CoxMatrix.act`, `j`
- **Used by**: `coxPhiFunction_coeff_modularFunction`, `coxPhiFunction_coeff_polynomialInJ`
- **Visibility**: public
- **Lines**: 209–236, proof body ≈ 22 lines
- **Notes**: `open scoped Manifold in`, `classical`. Inner `hcoset`/`hroot` (L215–221) re-prove the private `UpperHalfPlaneFunctionField.rightCosetEval_mdifferentiable` (UpperHalfPlaneFunctionField.lean:221) and `Interpolation.coxRoot_mdifferentiable_aux` (Interpolation.lean:135–139). The Vieta/powersetCard detour (L222–233) is repeated verbatim in IntegralDescent.lean:200–214 and would be unnecessary with the coefficient-closure lemma `Interpolation.polynomial_prod_coeff_mdifferentiable_aux` (Interpolation.lean:156–173), which lives downstream and so cannot be used here — the cusp-meromorphic analogue `coxPhiFunction_coeff_widthM_cuspMeromorphicAt` (L239–247) IS proved the short way.

### `theorem Cox.coxPhiFunction_coeff_widthM_cuspMeromorphicAt`
- **Type**: `(m : ℕ+) (n : ℕ) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) ((coxPhiFunction m).coeff n)) 0`
- **What**: Every Cox-product coefficient is meromorphic in the width-`m` cusp parameter.
- **How**: `polynomial_prod_coeff_cuspMeromorphicAt` applied to the linear factors, each handled by `coxLinearFactor_coeff_cuspMeromorphicAt`.
- **Hypotheses**: none.
- **Uses from project**: `coxPhiFunction`, `polynomial_prod_coeff_cuspMeromorphicAt`, `coxLinearFactor_coeff_cuspMeromorphicAt`, `CoxMatrix`, `j`
- **Used by**: `coxPhiFunction_coeff_widthOne_cuspMeromorphicAt`
- **Visibility**: public
- **Lines**: 238–247, proof body ≈ 5 lines
- **Notes**: `classical`. Twin of `Interpolation.interpolationRootProduct_coeff_cuspMeromorphicAt_aux` (Interpolation.lean:222–233).

### `theorem Cox.coxPhiFunction_coeff_widthOne_cuspMeromorphicAt`
- **Type**: `(m : ℕ+) (n : ℕ) : MeromorphicAt (cuspFunction 1 ((coxPhiFunction m).coeff n)) 0`
- **What**: Every Cox-product coefficient is meromorphic in the ordinary width-1 parameter `q`.
- **How**: `meromorphicAt_cuspFunction_of_nat_mul` (width `m·1` meromorphy + 1-periodicity ⇒ width-1 meromorphy), with periodicity from `periodic_comp_of_slashInvariant_one`.
- **Hypotheses**: none.
- **Uses from project**: `coxPhiFunction`, `meromorphicAt_cuspFunction_of_nat_mul`, `coxPhiFunction_coeff_widthM_cuspMeromorphicAt`, `periodic_comp_of_slashInvariant_one`, `coxPhiFunction_coeff_slashInvariant`
- **Used by**: `coxPhiFunction_coeff_modularFunction`
- **Visibility**: public
- **Lines**: 250–257, proof body ≈ 5 lines
- **Notes**: External user: IntegralDescent.lean:241. Verbatim twin of `Interpolation.interpolation_coeff_widthOne_cuspMeromorphicAt_aux` (Interpolation.lean:262–270).

### `def Cox.coxPhiFunction_coeff_modularFunction`
- **Type**: `(m : ℕ+) (n : ℕ) : ModularFunction 𝒮ℒ`
- **What**: Packages the `n`-th Cox-product coefficient as a level-one modular function (the invariant-coefficient argument before Cox (11.14)).
- **How**: Fields: slash invariance from `coxPhiFunction_coeff_slashInvariant`; meromorphy on `ℍ` via `MeromorphicField.ofHolomorphic` from `coxPhiFunction_coeff_mdifferentiable`; boundedness at cusps via `isCusp_SL2Z_iff'` + `OnePoint.isOfExponentialGrowthAt_iff` + `isOfExponentialGrowth_of_meromorphicAt_cuspFunction` using width-1 cusp meromorphy and periodicity.
- **Hypotheses**: none.
- **Uses from project**: `coxPhiFunction`, `ModularFunction`, `MeromorphicField.ofHolomorphic`, `MeromorphicField.toFun_ofHolomorphic`, `OnePoint.isOfExponentialGrowthAt_iff`, `IsOfExponentialGrowth`, `isOfExponentialGrowth_of_meromorphicAt_cuspFunction`, `periodic_comp_of_slashInvariant_one`, `coxPhiFunction_coeff_slashInvariant`, `coxPhiFunction_coeff_mdifferentiable`, `coxPhiFunction_coeff_widthOne_cuspMeromorphicAt`
- **Used by**: `coe_coxPhiFunction_coeff_modularFunction`, `coxPhiFunction_coeff_polynomialInJ`
- **Visibility**: public
- **Lines**: 259–277, proof body ≈ 16 lines
- **Notes**: A `def` producing data (the structure) with theorem-style name. Its only consumer `coxPhiFunction_coeff_polynomialInJ` feeds it to `levelOne_polynomialInJ_of_holomorphic`, which immediately converts back to `CuspData` (`CuspData.of_levelOneModularFunction`, CuspData.lean:73). The direct route `CuspData.polynomialInJ_of_holomorphic (hf : LevelOneCuspData f) (hfH : MDiff f)` (ModularFunction.lean:198) exists and would avoid building a `ModularFunction` at all; Interpolation.lean takes that route (`interpolation_coeff_cuspData`).

### `theorem Cox.coe_coxPhiFunction_coeff_modularFunction`
- **Type**: `(m : ℕ+) (n : ℕ) : (coxPhiFunction_coeff_modularFunction m n : ℍ → ℂ) = (coxPhiFunction m).coeff n`
- **What**: The underlying function of the packaged modular function is the coefficient.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `coxPhiFunction_coeff_modularFunction`, `coxPhiFunction`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 279–281, proof body ≈ 1 line
- **Notes**: `@[simp]`. No users anywhere in the project (junk candidate together with the def if the `CuspData` route is adopted).

### `theorem Cox.coxPhiFunction_coeff_polynomialInJ`
- **Type**: `(m : ℕ+) (n : ℕ) : ∃ P : Polynomial ℂ, (coxPhiFunction m).coeff n = polynomialIn P j`
- **What**: Cox Lemma 11.10 applied to the coefficients: each is a polynomial in `j`.
- **How**: `levelOne_polynomialInJ_of_holomorphic` (holomorphic level-one modular functions are polynomials in `j`).
- **Hypotheses**: none.
- **Uses from project**: `coxPhiFunction`, `polynomialIn`, `j`, `levelOne_polynomialInJ_of_holomorphic`, `coxPhiFunction_coeff_modularFunction`, `coxPhiFunction_coeff_mdifferentiable`
- **Used by**: `coxCoefficientPolynomialAux`, `coxCoefficientPolynomialAux_eval`
- **Visibility**: public
- **Lines**: 283–288, proof body ≈ 3 lines
- **Notes**: —

### `private def Cox.coxCoefficientPolynomialAux`
- **Type**: `(m : ℕ+) (n : ℕ) : Polynomial ℂ := (coxPhiFunction_coeff_polynomialInJ m n).choose`
- **What**: A chosen polynomial `P_n` with `P_n(j) = ` the `n`-th coefficient.
- **How**: `Exists.choose`.
- **Hypotheses**: none.
- **Uses from project**: `coxPhiFunction_coeff_polynomialInJ`
- **Used by**: `coxCoefficientPolynomialAux_eval`, `modularPolynomialCandidateAux`
- **Visibility**: private
- **Lines**: 290–292, proof body ≈ 0 lines
- **Notes**: Redundant `noncomputable` keyword inside `noncomputable section`.

### `private theorem Cox.coxCoefficientPolynomialAux_eval`
- **Type**: `(m : ℕ+) (n : ℕ) (τ : ℍ) : (coxCoefficientPolynomialAux m n).eval (j τ) = (coxPhiFunction m).coeff n τ`
- **What**: The chosen polynomial evaluated at `j(τ)` gives the coefficient at `τ`.
- **How**: `choose_spec` unfolded through `polynomialIn` and `congrFun`.
- **Hypotheses**: none.
- **Uses from project**: `coxCoefficientPolynomialAux`, `coxPhiFunction_coeff_polynomialInJ`, `polynomialIn`, `coxPhiFunction`, `j`
- **Used by**: `modularPolynomialCandidateAux_specializeY`
- **Visibility**: private
- **Lines**: 294–299, proof body ≈ 2 lines
- **Notes**: Same statement as the public `IntegralDescent.modularPolynomialC_coeff_polynomialIn` (IntegralDescent.lean:265–273) once `modularPolynomialC` exists.

### `private def Cox.modularPolynomialCandidateAux`
- **Type**: `(m : ℕ+) : BivariatePolynomial ℂ := Polynomial.X ^ Fintype.card (CoxMatrix m) + ∑ n ∈ Finset.range (Fintype.card (CoxMatrix m)), Polynomial.monomial n (coxCoefficientPolynomialAux m n)`
- **What**: The candidate `Φ_m(X,Y) = X^{|C(m)|} + Σ_{n<|C(m)|} P_n(Y) X^n`.
- **How**: Explicit monic assembly from the chosen coefficient polynomials.
- **Hypotheses**: none.
- **Uses from project**: `BivariatePolynomial`, `CoxMatrix`, `coxCoefficientPolynomialAux`
- **Used by**: `modularPolynomialCandidateAux_specializeY`, `modularPolynomialCandidateAux_monic`, `existsUnique_modularPolynomialC`
- **Visibility**: private
- **Lines**: 301–305, proof body ≈ 0 lines
- **Notes**: Redundant `noncomputable`.

### `private theorem Cox.modularPolynomialCandidateAux_specializeY`
- **Type**: `(m : ℕ+) (τ : ℍ) : (modularPolynomialCandidateAux m).specializeY (j τ) = coxPhiAtJ m τ`
- **What**: The candidate specializes at `Y = j(τ)` to the Cox product.
- **How**: `Polynomial.Monic.as_sum` writes `coxPhiAtJ m τ` as `X^deg + Σ coeff_n X^n`; match termwise with `Polynomial.map_sum`, `coxCoefficientPolynomialAux_eval`, `coxPhiFunction_coeff_apply`, `coxPhiAtJ_natDegree`, `C_mul_X_pow_eq_monomial`.
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialCandidateAux`, `specializeY`, `coxPhiAtJ`, `coxCoefficientPolynomialAux_eval`, `coxPhiFunction_coeff_apply`, `coxPhiAtJ_natDegree`, `coxPhiAtJ_monic`, `j`
- **Used by**: `existsUnique_modularPolynomialC`
- **Visibility**: private
- **Lines**: 307–314, proof body ≈ 4 lines
- **Notes**: `classical`; single large `simpa` call.

### `private theorem Cox.modularPolynomialCandidateAux_monic`
- **Type**: `(m : ℕ+) : (modularPolynomialCandidateAux m).Monic`
- **What**: The candidate is monic in `X`.
- **How**: `Polynomial.monic_X_pow_add` (Mathlib/Algebra/Polynomial/Monic.lean) after bounding the degree of the sum by `Polynomial.degree_sum_le`, `Finset.sup_lt_iff`, `degree_monomial_le`.
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialCandidateAux`
- **Used by**: `existsUnique_modularPolynomialC`
- **Visibility**: private
- **Lines**: 316–325, proof body ≈ 8 lines
- **Notes**: `classical`.

### `theorem Cox.existsUnique_modularPolynomialC`
- **Type**: `(m : ℕ+) : ∃! Φ : BivariatePolynomial ℂ, Φ.Monic ∧ ∀ τ : ℍ, Φ.specializeY (j τ) = coxPhiAtJ m τ`
- **What**: Cox (11.14): there is a unique monic `Φ ∈ ℂ[X][Y]` with `Φ(X, j(τ)) = ∏_{σ}(X - j(σ·τ))` for all `τ`.
- **How**: Existence from the candidate (`modularPolynomialCandidateAux_monic/_specializeY`); uniqueness from `specializeY_ext` since `j` is surjective onto `ℂ` (`j_surjective`).
- **Hypotheses**: none.
- **Uses from project**: `BivariatePolynomial`, `specializeY`, `coxPhiAtJ`, `j`, `modularPolynomialCandidateAux`, `modularPolynomialCandidateAux_monic`, `modularPolynomialCandidateAux_specializeY`, `specializeY_ext`, `j_surjective`
- **Used by**: `modularPolynomialC`, `modularPolynomialC_monic`, `modularPolynomialC_specializeY`
- **Visibility**: public
- **Lines**: 328–340, proof body ≈ 8 lines
- **Notes**: No external users.

### `def Cox.modularPolynomialC`
- **Type**: `(m : ℕ+) : BivariatePolynomial ℂ := (existsUnique_modularPolynomialC m).choose`
- **What**: Cox's complex modular polynomial `Φ_m(X,Y)`.
- **How**: Choice from the existence-uniqueness statement.
- **Hypotheses**: none.
- **Uses from project**: `BivariatePolynomial`, `existsUnique_modularPolynomialC`
- **Used by**: `modularPolynomialC_monic`, `modularPolynomialC_specializeY`, `modularPolynomialC_rightCosetProduct`, `modularPolynomialC_eval_levelJ_j`, `modularPolynomialC_natDegree`
- **Visibility**: public
- **Lines**: 342–344, proof body ≈ 0 lines
- **Notes**: Redundant `noncomputable`. Central object: used in LevelThree (14), Arithmetic (14), DiagonalLaurent (4), Classification, Interpolation, Irreducibility, IntegralDescent.

### `theorem Cox.modularPolynomialC_monic`
- **Type**: `(m : ℕ+) : (modularPolynomialC m).Monic`
- **What**: `Φ_m` is monic in `X`.
- **How**: `choose_spec.1.1`.
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialC`, `existsUnique_modularPolynomialC`
- **Used by**: `modularPolynomialC_natDegree`
- **Visibility**: public
- **Lines**: 346–347, proof body ≈ 1 line
- **Notes**: External: Arithmetic (3), LevelThree, Irreducibility, IntegralDescent.

### `theorem Cox.modularPolynomialC_specializeY`
- **Type**: `(m : ℕ+) (τ : ℍ) : (modularPolynomialC m).specializeY (j τ) = coxPhiAtJ m τ`
- **What**: Cox (11.15): `Φ_m(X, j(τ)) = ∏_{σ∈C(m)} (X - j(σ·τ))`.
- **How**: `choose_spec.1.2`.
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialC`, `specializeY`, `coxPhiAtJ`, `existsUnique_modularPolynomialC`, `j`
- **Used by**: `modularPolynomialC_rightCosetProduct`, `modularPolynomialC_eval_levelJ_j`, `modularPolynomialC_natDegree`
- **Visibility**: public
- **Lines**: 349–352, proof body ≈ 1 line
- **Notes**: External: Interpolation.lean:327, IntegralDescent.lean:270, SingularModuli.lean:214, Classification.lean:331.

### `theorem Cox.modularPolynomialC_rightCosetProduct`
- **Type**: `(m : ℕ+) (τ : ℍ) : (modularPolynomialC m).specializeY (j τ) = ∏ c : Gamma0RightCosets m, (Polynomial.X - Polynomial.C (rightCosetEval m c τ))`
- **What**: Cox (11.14): the specialization as a product over right cosets.
- **How**: `modularPolynomialC_specializeY` then `coxPhiAtJ_eq_rightCosetProduct`.
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialC`, `specializeY`, `Gamma0RightCosets`, `rightCosetEval`, `modularPolynomialC_specializeY`, `coxPhiAtJ_eq_rightCosetProduct`, `j`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 354–359, proof body ≈ 1 line
- **Notes**: External: Interpolation.lean:416, Irreducibility.lean:38.

### `theorem Cox.modularPolynomialC_eval_levelJ_j`
- **Type**: `(m : ℕ+) (τ : ℍ) : (modularPolynomialC m).eval (levelJ m τ) (j τ) = 0`
- **What**: The distinguished root: `Φ_m(j(mτ), j(τ)) = 0`.
- **How**: `specializeY_eval` + `modularPolynomialC_specializeY` + `Polynomial.eval_prod` + `Finset.prod_eq_zero` at `σ₀` where `j(σ₀·τ) = j(mτ)` (`j_act_sigmaZero`).
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialC`, `eval`, `levelJ`, `j`, `specializeY_eval`, `modularPolynomialC_specializeY`, `coxPhiAtJ`, `sigmaZero`, `j_act_sigmaZero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 361–369, proof body ≈ 6 lines
- **Notes**: External: Arithmetic (3). Same `eval_prod`/`prod_eq_zero`-at-`σ₀` pattern reappears in Irreducibility.lean:77–79, SingularModuli.lean:214, Classification.lean:331.

### `theorem Cox.modularPolynomialC_natDegree`
- **Type**: `(m : ℕ+) : (modularPolynomialC m).natDegree = Fintype.card (CoxMatrix m)`
- **What**: `Φ_m` has `X`-degree `|C(m)|`.
- **How**: Specialize at `τ = I`: `Polynomial.Monic.natDegree_map` shows specialization preserves the degree of a monic polynomial, then `coxPhiAtJ_natDegree`.
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialC`, `CoxMatrix`, `coxPhiAtJ_natDegree`, `modularPolynomialC_specializeY`, `modularPolynomialC_monic`, `specializeY`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 371–377, proof body ≈ 4 lines
- **Notes**: External: LevelThree, Arithmetic, Irreducibility.lean:128.

## File Summary
- Total declarations: 43 (13 defs incl. 1 abbrev, 30 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `BivariatePolynomial`, `specializeY`, `coxPhiAtJ`, `coxPhiFunction`, `modularPolynomialC`, `modularPolynomialC_specializeY`, `coxPhiFunction_coeff_apply`/`coxPhiAtJ_natDegree` (2 each)
- Unused declarations (not used by anything in this file): `varX`, `varY`, `eval_swap`, `map_swap`, `diagonal_eval`, `diagonal_map`, `diagonal_eval₂`, `diagonal_swap`, `coe_coxPhiFunction_coeff_modularFunction`, `modularPolynomialC_rightCosetProduct`, `modularPolynomialC_eval_levelJ_j`, `modularPolynomialC_natDegree` (all but `coe_coxPhiFunction_coeff_modularFunction` are used in other files)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: `coxPhiFunction_coeff_mdifferentiable`, 22 lines)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- Bivariate layer vs `Mathlib/Algebra/Polynomial/Bivariate.lean` (pinned): `BivariatePolynomial R` = `R[X][Y]` (:29); `varX` = notation `Y` (:26); `varY` = `C X`; `eval Φ x y` = `evalEval y x` (:44, argument order swapped); `specializeY y` = `map (evalRingHom y)` (unnamed in mathlib, :162); `map f` = `map (mapRingHom f)` (unnamed, :172–182). Lemma-level duplicates: `specializeY_eval` (L70–72) ≡ `Polynomial.map_evalRingHom_eval` (:162); `diagonal_map` (L126–131) ≡ `map_mapRingHom_eval_map` at `q := X` (:172); `eval_swap` (L88–93) ≡ `Bivariate.aevalAeval_swap` (:286) + `coe_aevalAeval_eq_evalEval` (:237); `diagonal_eval` (L116–123) ≡ `eval₂_evalRingHom` (:159) + `hom_eval₂`; `diagonal_eval₂` (L135–141) ≡ `eval₂_eval₂RingHom_apply` (:194) after `diagonal_map`. Not in mathlib (grep-verified in Bivariate.lean): `coeff_coeff_swap` (L97–105), `map_swap` (L108–113), `diagonal_swap` (L145–156), `specializeY_ext` (L75–83), and the `diagonal` definition itself — the first three are general `CommSemiring` facts about `Bivariate.swap` and are PR candidates.
- Current state of the "two evaluation conventions": `BivariatePolynomial.eval` (this file) and raw `Polynomial.evalEval` (Interpolation.lean:355–393, 398, 436, 446; ModularFunction/CuspData.lean:57–59 `RationalInTwo`; ModularFunctionField.lean:38, 91–93) both survive after the Sep 21 cleanup. They agree semantically (`P.evalEval (j τ) (levelJ N τ) = BivariatePolynomial.eval P (levelJ N τ) (j τ)`), and the only bridge is the private `Interpolation.modularPolynomialC_derivative_evalEval` (Interpolation.lean:397–402). Consolidation option: make `BivariatePolynomial.eval` an `abbrev` for `fun Φ x y ↦ Φ.evalEval y x` (it already is definitionally) and add `@[simp] eval_eq_evalEval`, or drop it and state everything with `evalEval`.
- `coxPhiAtJ m τ` (L59–60) and `coxPhiFunction m` (L63–65) are definitionally `Lagrange.nodal Finset.univ _` (`Mathlib/LinearAlgebra/Lagrange.lean:543`); `coxPhiAtJ_monic` (L159–162) = `Lagrange.nodal_monic` (:568), `coxPhiAtJ_natDegree` (L165–168) = `Lagrange.natDegree_nodal` (:551) + `Finset.card_univ`. `coxPhiFunction_coeff_mdifferentiable` (L212–236) hand-rolls Vieta (`Finset.prod_X_add_C_coeff`, Vieta.lean:67) where `Polynomial.liftsRing holomorphicFunctions.subtype` (Lifts.lean:209; `holomorphicFunctions : Subring (ℍ → ℂ)` at ModularFunctions/FieldAction.lean:26) + `Subring.prod_mem` + `lifts_iff_coeff_lifts` (:72) gives the result in 3 lines.
- `coxPhiFunction_coeff_modularFunction` (L261–277) + `coxPhiFunction_coeff_polynomialInJ` (L284–288): replace by `CuspData.polynomialInJ_of_holomorphic` (ModularFunction.lean:198) applied to a `LevelOneCuspData` built from L200–257; this removes the `ModularFunction 𝒮ℒ` packaging and the unused `coe_` simp lemma (L279–281).
### Missing API / repeated patterns
- Level-one descent pipeline (A15) is duplicated between this file and Interpolation.lean: {`_map_eval` L171–174 / Interpolation:105–112}, {`_coeff_apply` L178–180 / :114–119}, {coset reindexing L183–198 / :40–73}, {`_slashInvariant` L201–207 / :252–260}, {`_widthM_cuspMeromorphicAt` L239–247 / :222–233}, {`_widthOne_cuspMeromorphicAt` L251–257 / :262–270}, {holomorphy of roots L215–221 / :135–139 / UpperHalfPlaneFunctionField.lean:221}. Single collapsing lemma: `theorem LevelOneCuspData.of_widthM {m : ℕ+} {f : ℍ → ℂ} (hH : ∀ z : ℂ, 0 < z.im → MeromorphicAt (f ∘ ofComplex) z) (hslash : ∀ δ : SL(2, ℤ), f ∣[(0 : ℤ)] δ = f) (hcusp : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) f) 0) : LevelOneCuspData f` (packaging `meromorphicAt_cuspFunction_of_nat_mul` + `periodic_comp_of_slashInvariant_one` + the `hfun` rewrite of Interpolation.lean:282–289), plus a `Polynomial (ℍ → ℂ)`-level lemma `coeff_slashInvariant_of_prod_X_sub_C` for the invariance step. Both files then reduce to one call each.
- `specializeY_coeff : (specializeY y Φ).coeff n = (Φ.coeff n).eval y` is re-derived by `simp [specializeY, coeff_map]` at L83, L311, Irreducibility.lean:43, IntegralDescent.lean:272.
- `BivariatePolynomial.eval` lacks `_add/_mul/_C/_X/_sum/_map` companions; `map` lacks `map_eval`/`map_specializeY`; `varX`/`varY` lack any lemma.
- Redundant `noncomputable def` inside `noncomputable section` at L59, L63, L290, L301, L343.
### Junk candidates
- `coe_coxPhiFunction_coeff_modularFunction` (L279–281): no users anywhere (`grep -rnw` over XYin).
- `varX`, `varY` (L32–36): not used in this batch; only LevelThree/Kronecker/KroneckerFrobenius, where mathlib's `Y`/`C X` would serve.
- One-line mathlib wrappers: `specializeY_eval` (L70–72), `diagonal_map` (L126–131), `eval_swap` (L88–93).
- `existsUnique_modularPolynomialC` (L330–340) is only consumed through `choose`; could be inlined by defining `modularPolynomialC := modularPolynomialCandidateAux` and proving uniqueness as a separate `modularPolynomialC_unique` lemma (which would also make `modularPolynomialC` transparent rather than `choose`-opaque).
### Moral duplicates within this batch
- `coxCoefficientPolynomialAux_eval` (L294–299) vs `IntegralDescent.modularPolynomialC_coeff_polynomialIn` (IntegralDescent.lean:265–273): same content once `modularPolynomialC` is known; the latter belongs in this file (it uses only this file's API).
- `coxPhiFunction_coeff_mdifferentiable` L222–233 vs `IntegralDescent.coxPhiFunction_coeff_laurentqExpansion_widthM` L200–214: identical Vieta `powersetCard` expansion of `coxPhiFunction` coefficients.
- All pairs listed under "Level-one descent pipeline" above.
### Generalization notes
- `coeff_coeff_swap`, `map_swap`, `diagonal_swap`, `diagonal_eval`, `diagonal_map`, `diagonal_eval₂`: stated for `CommSemiring`; `diagonal`/`map` only need `Semiring` (the `CommSemiring` is forced by `Polynomial.eval` needing commutativity for `eval X`; fine).
- `specializeY_ext` needs `Infinite R` + `IsDomain R` only through `Polynomial.funext`; could be stated for any infinite `CommRing` domain or, more generally, for any `R` and any set of `y`'s that is "polynomially dense".
- `coxPhiAtJ`, `coxPhiFunction` and the invariance/holomorphy lemmas are specific to `j`; the coset-reindexing lemmas (`coxPhiAtJ_eq_rightCosetProduct`, `coxPhiAtJ_sl2_smul`) hold for any `CuspData m f` in place of `levelJ_cuspData m` (this generality is exactly what Interpolation.lean re-proves for `rightCosetTranslate m hf`).
