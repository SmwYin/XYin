# XYin/PhD/Cox/Arithmetic.lean

**Source**: `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/Arithmetic.lean`
**Project-internal imports**: `XYin.PhD.Cox.CyclicSublattice.Classification`, `XYin.PhD.Cox.LevelThree`
**Module doc**: Arithmetic of the modular polynomial — Cox *Primes of the Form x² + ny²*, Theorem 11.18. Everything lives in `noncomputable section`, `namespace Cox`, with `open UpperHalfPlane` and `open UpperHalfPlaneFunctionField`.

### `theorem theorem_11_18_i`
- **Type**: `(m : ℕ+) : BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m) = modularPolynomialC m`
- **What**: Cox Theorem 11.18(i): the integral modular polynomial `Φ_m ∈ ℤ[X,Y]`, base-changed to ℂ, equals the analytically constructed complex modular polynomial.
- **How**: Immediate restatement of the integral-descent theorem `modularPolynomial_map_complex` (a term-mode alias giving the result its Cox numbering).
- **Hypotheses**: `m` a positive natural.
- **Uses from project**: [`modularPolynomial`, `modularPolynomialC`, `BivariatePolynomial.map`, `modularPolynomial_map_complex`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 22–24, proof 1 line (term)
- **Notes**: none

### `theorem theorem_11_18_ii`
- **Type**: `(m : ℕ+) : Irreducible (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (modularPolynomialC m))`
- **What**: Cox Theorem 11.18(ii): `Φ_m(X, Y)` is irreducible as a polynomial in the root variable `X` over the coefficient field ℂ(Y).
- **How**: Term-mode alias of `modularPolynomialC_irreducibleInX` (proved in `ModularPolynomial/Irreducibility.lean` via transitivity of the coset action / minimal-polynomial degree count).
- **Hypotheses**: `m` a positive natural.
- **Uses from project**: [`modularPolynomialC`, `modularPolynomialC_irreducibleInX`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 28–30, proof 1 line (term)
- **Notes**: none

### `theorem modularPolynomial_map_complex_zero_swap`
- **Type**: `(m : ℕ+) (u v : ℂ) : (BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m)).eval u v = 0 ↔ (BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m)).eval v u = 0`
- **What**: The complex modular curve `Φ_m(u,v) = 0` is invariant under swapping its two coordinates: `Φ_m(u,v)=0 ↔ Φ_m(v,u)=0`.
- **How**: Via the lattice-theoretic characterization `theorem_11_23` (zeros of `Φ_m` classify cyclic index-`m` sublattice inclusions): given a cyclic sublattice `S ⊂ L` witnessing `Φ_m(u,v)=0`, the dual inclusion `S.dual` of `mL ⊂ S` (as sublattice of `S.toPeriodPair`) witnesses the swapped zero, using `dual_sub_j` (`S.dual.j = L.j`) and `dual_base_j` (`S.toPeriodPair.j = S.j`).
- **Hypotheses**: `m` a positive natural; `u v : ℂ` arbitrary.
- **Uses from project**: [`modularPolynomial`, `BivariatePolynomial.map`, `theorem_11_23`, `PeriodPair.CyclicSublattice.toPeriodPair`, `PeriodPair.CyclicSublattice.dual`, `PeriodPair.CyclicSublattice.dual_sub_j`, `PeriodPair.CyclicSublattice.dual_base_j`]
- **Used by**: `modularPolynomialC_eval_j_levelJ`
- **Visibility**: public
- **Lines**: 34–47, proof ~13 lines
- **Notes**: none

### `theorem modularPolynomialC_eval_j_levelJ` (private)
- **Type**: `(m : ℕ+) (τ : ℍ) : (modularPolynomialC m).eval (j τ) (levelJ m τ) = 0`
- **What**: The swapped evaluation of the complex modular polynomial vanishes on the pair `(j(τ), j(mτ))` — i.e. `Φ_m(j(τ), j(mτ)) = 0` with the arguments in the reverse of the defining order.
- **How**: Transports the defining relation `modularPolynomialC_eval_levelJ_j` (`Φ_m(j(mτ), j(τ)) = 0`) through the coordinate-swap invariance `modularPolynomial_map_complex_zero_swap`, converting between the integral and complex polynomials via `modularPolynomial_map_complex`.
- **Hypotheses**: `m` a positive natural, `τ` in the upper half-plane.
- **Uses from project**: [`modularPolynomialC`, `j`, `levelJ`, `modularPolynomial_map_complex`, `modularPolynomial_map_complex_zero_swap`, `modularPolynomialC_eval_levelJ_j`]
- **Used by**: `modularPolynomial_dvd_swap` (inside `hQzero`)
- **Visibility**: private
- **Lines**: 49–54, proof ~5 lines
- **Notes**: none

### `theorem aeval_base_eq_zero_of_forall_eval_eq_zero` (private)
- **Type**: `(m : ℕ+) (F : BivariatePolynomial ℂ) (hF : ∀ τ : ℍ, F.eval (levelJ m τ) (j τ) = 0) : Polynomial.aeval (rightCosetRoot m (baseRightCoset m)) (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) F) = 0`
- **What**: Any bivariate complex polynomial `F` vanishing pointwise on `(j(mτ), j(τ))` for all `τ` also annihilates, over ℂ(Y) ≅ ℂ(j), the function-field element `j(mτ)` (the root attached to the base right coset), i.e. `F(α, j) = 0` in the modular function field.
- **How**: Identifies the base-coset function with `levelJ m` (via `baseRightCoset` and `rightCosetEval_mk`), shows pointwise vanishing gives vanishing as a holomorphic function using the pointwise evaluation homomorphisms `evaluation τ` and `evalJ_apply`, then transports along the algebra-map factorization `ratFuncEvalJ_algebraMap` (ℂ[Y] → ℂ(Y) → FunctionField equals `evalJFracPoly`) and `Polynomial.eval₂_at_apply`.
- **Hypotheses**: `F` vanishes at `(levelJ m τ, j τ)` for every `τ : ℍ`.
- **Uses from project**: [`BivariatePolynomial`, `levelJ`, `j`, `rightCosetRoot`, `baseRightCoset`, `rightCosetFunction`, `HolomorphicFunction`, `rightCosetEval`, `rightCosetEval_mk`, `evalJ`, `evaluation`, `evalJ_apply`, `FunctionField`, `evalJFracPoly`, `ratFuncEvalJ_algebraMap`]
- **Used by**: `modularPolynomial_dvd_swap` (twice: for `hPzero` and `hQzero`)
- **Visibility**: private
- **Lines**: 56–100, proof ~44 lines
- **Notes**: proof >30 lines

### `theorem modularPolynomial_dvd_swap`
- **Type**: `(m : ℕ+) : modularPolynomial m ∣ Polynomial.Bivariate.swap (modularPolynomial m)`
- **What**: The integral modular polynomial divides its own variable-swap `Φ_m(Y, X)` in ℤ[X,Y] — the key divisibility step toward symmetry of `Φ_m`.
- **How**: Both `Φ_m` and its swap annihilate the function-field element α = `rightCosetRoot m (baseRightCoset m)` (by `aeval_base_eq_zero_of_forall_eval_eq_zero` applied to `modularPolynomialC_eval_levelJ_j` and to the swapped identity `modularPolynomialC_eval_j_levelJ` via `BivariatePolynomial.eval_swap`); since `Φ_m` is irreducible and monic over ℂ(Y) it equals `minpoly (RatFunc ℂ) α` by `minpoly.eq_of_irreducible_of_monic`, hence divides the swap by `minpoly.dvd`. Divisibility descends from ℂ(Y) to ℂ[Y] by `Polynomial.map_dvd_map` with `IsFractionRing.injective` and monicity, and then from ℂ to ℤ by injectivity of `Int.cast` with `modularPolynomial_monic`.
- **Hypotheses**: `m` a positive natural.
- **Uses from project**: [`modularPolynomial`, `modularPolynomialC`, `FunctionField`, `rightCosetRoot`, `baseRightCoset`, `aeval_base_eq_zero_of_forall_eval_eq_zero`, `modularPolynomialC_eval_levelJ_j`, `modularPolynomialC_eval_j_levelJ`, `BivariatePolynomial.eval_swap`, `modularPolynomialC_irreducibleInX`, `modularPolynomialC_monic`, `modularPolynomial_monic`, `BivariatePolynomial.map`, `BivariatePolynomial.map_swap`, `modularPolynomial_map_complex`]
- **Used by**: `theorem_11_18_iii`
- **Visibility**: public
- **Lines**: 103–140, proof ~37 lines
- **Notes**: proof >30 lines

### `theorem modularPolynomialC_not_anti` (private)
- **Type**: `(m : ℕ+) (hm : 1 < (m : ℕ)) : Polynomial.Bivariate.swap (modularPolynomialC m) ≠ -(modularPolynomialC m)`
- **What**: For `m > 1` the complex modular polynomial is not anti-symmetric under variable swap: `Φ_m(Y,X) ≠ -Φ_m(X,Y)`. Rules out the sign ambiguity in the symmetry proof.
- **How**: Anti-symmetry would force the diagonal `Φ_m(X,X)` to be zero (via `BivariatePolynomial.diagonal_swap` and `CharZero.eq_neg_self_iff`), hence `X - C X ∣ Φ_m` in ℂ[Y][X]; over ℂ(Y) irreducibility (`modularPolynomialC_irreducibleInX`) plus `Polynomial.not_isUnit_X_sub_C` forces `Φ_m` to be associated to a degree-1 polynomial, so `natDegree ≤ 1` by `Polynomial.natDegree_le_of_dvd`; but `modularPolynomialC_natDegree` gives degree `card (CoxMatrix m) > 1` by `one_lt_card_coxMatrix` since `m > 1` — contradiction.
- **Hypotheses**: `1 < m`.
- **Uses from project**: [`modularPolynomialC`, `BivariatePolynomial.diagonal`, `BivariatePolynomial.diagonal_swap`, `modularPolynomialC_irreducibleInX`, `modularPolynomialC_monic`, `modularPolynomialC_natDegree`, `CoxMatrix`, `one_lt_card_coxMatrix`]
- **Used by**: `theorem_11_18_iii`
- **Visibility**: private
- **Lines**: 142–172, proof ~30 lines
- **Notes**: proof ~30 lines (borderline)

### `theorem eq_or_eq_neg_of_associated_int_bivariate` (private)
- **Type**: `{P Q : BivariatePolynomial ℤ} (h : Associated P Q) : Q = P ∨ Q = -P`
- **What**: Two associated bivariate integer polynomials are equal up to sign, since the units of ℤ[X][Y] are ±1.
- **How**: Peels the unit through two applications of `Polynomial.isUnit_iff` (units of `R[X]` are constant units of `R`) down to `Int.isUnit_iff` (units of ℤ are ±1), then case-splits.
- **Hypotheses**: `P` and `Q` are associated in ℤ[X][Y].
- **Uses from project**: [`BivariatePolynomial`]
- **Used by**: `theorem_11_18_iii`
- **Visibility**: private
- **Lines**: 174–185, proof ~11 lines
- **Notes**: fully generic lattice-free fact about ℤ[X][Y]; candidate for a general utility file

### `theorem theorem_11_18_iii`
- **Type**: `(m : ℕ+) (hm : 1 < (m : ℕ)) : Polynomial.Bivariate.swap (modularPolynomial m) = modularPolynomial m`
- **What**: Cox Theorem 11.18(iii): for level `m > 1` the integral modular polynomial is symmetric in its two variables, `Φ_m(X,Y) = Φ_m(Y,X)`.
- **How**: `modularPolynomial_dvd_swap` gives `Φ_m ∣ swap Φ_m`; applying `swap` (an involution, `Polynomial.Bivariate.swap_swap_apply`) gives the reverse divisibility, so the two are associated (`associated_of_dvd_dvd`), hence equal up to sign by `eq_or_eq_neg_of_associated_int_bivariate`. The sign −1 is excluded by base-changing to ℂ and invoking `modularPolynomialC_not_anti`.
- **Hypotheses**: `1 < m`.
- **Uses from project**: [`modularPolynomial`, `modularPolynomialC`, `modularPolynomial_dvd_swap`, `eq_or_eq_neg_of_associated_int_bivariate`, `modularPolynomialC_not_anti`, `BivariatePolynomial.map`, `BivariatePolynomial.map_swap`, `modularPolynomial_map_complex`]
- **Used by**: `theorem_11_18_iv_degree`, `modularPolynomial_three`
- **Visibility**: public
- **Lines**: 188–210, proof ~22 lines
- **Notes**: none

### `def modularPolynomialDiagonal`
- **Type**: `(m : ℕ+) : Polynomial ℤ`
- **What**: The diagonal restriction `Φ_m(X, X) ∈ ℤ[X]` of the integral modular polynomial — the polynomial whose roots are singular moduli in Cox's Chapter 11 development.
- **How**: Definition: `BivariatePolynomial.diagonal` (evaluate the outer variable at the inner variable `X`) applied to `modularPolynomial m`.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial.diagonal`, `modularPolynomial`]
- **Used by**: `modularPolynomialDiagonal_leadingCoeff_pow_two_mul`, `modularPolynomialDiagonal_leadingCoeff_isRootOfUnity`, `theorem_11_18_iv_leadingCoeff`, `modularPolynomialDiagonal_map_eval_fixedPoint`, `theorem_11_18_iv_degree`
- **Visibility**: public
- **Lines**: 213–214, definition
- **Notes**: none

### `theorem modularPolynomialDiagonal_leadingCoeff_pow_two_mul`
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) : (modularPolynomialDiagonal m).leadingCoeff ^ (2 * (m : ℕ)) = 1`
- **What**: Integral form of Cox equation (11.19): for nonsquare `m`, the leading coefficient of `Φ_m(X,X) ∈ ℤ[X]` raised to the explicit power `2m` equals 1.
- **How**: Base-changes the diagonal to ℂ via `BivariatePolynomial.diagonal_map` and `modularPolynomial_map_complex`; injectivity of `Int.cast` transfers leading coefficients (`Polynomial.leadingCoeff_map_of_injective`), so the complex result `modularPolynomialC_diagonal_leadingCoeff_pow` (from DiagonalLaurent.lean) casts back down to ℤ by `exact_mod_cast`.
- **Hypotheses**: `m` is not a perfect square.
- **Uses from project**: [`modularPolynomialDiagonal`, `modularPolynomialC`, `BivariatePolynomial.diagonal`, `BivariatePolynomial.diagonal_map`, `modularPolynomial_map_complex`, `modularPolynomialC_diagonal_leadingCoeff_pow`]
- **Used by**: `modularPolynomialDiagonal_leadingCoeff_isRootOfUnity`
- **Visibility**: public
- **Lines**: 217–232, proof ~15 lines
- **Notes**: none

### `theorem modularPolynomialDiagonal_leadingCoeff_isRootOfUnity`
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) : ∃ k : ℕ, 0 < k ∧ (modularPolynomialDiagonal m).leadingCoeff ^ k = 1`
- **What**: Existential packaging of (11.19): the leading coefficient of the diagonal is a root of unity (before integrality is used to pin it to ±1).
- **How**: Instantiates the witness `k = 2m` with `modularPolynomialDiagonal_leadingCoeff_pow_two_mul`; positivity from `PNat.pos`.
- **Hypotheses**: `m` is not a perfect square.
- **Uses from project**: [`modularPolynomialDiagonal`, `modularPolynomialDiagonal_leadingCoeff_pow_two_mul`]
- **Used by**: `theorem_11_18_iv_leadingCoeff`
- **Visibility**: public
- **Lines**: 236–240, proof 2 lines
- **Notes**: none

### `theorem theorem_11_18_iv_leadingCoeff`
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) : (modularPolynomialDiagonal m).leadingCoeff = 1 ∨ (modularPolynomialDiagonal m).leadingCoeff = -1`
- **What**: Cox Theorem 11.18(iv), leading-coefficient half: for nonsquare `m` the diagonal `Φ_m(X,X)` has leading coefficient ±1 (Cox states ±1; the sign is later pinned in the literature).
- **How**: An integer whose `k`-th power is 1 (k > 0) is ±1: applies mathlib's `pow_eq_one_iff_of_ne_zero` to the root-of-unity fact `modularPolynomialDiagonal_leadingCoeff_isRootOfUnity`.
- **Hypotheses**: `m` is not a perfect square.
- **Uses from project**: [`modularPolynomialDiagonal`, `modularPolynomialDiagonal_leadingCoeff_isRootOfUnity`]
- **Used by**: `theorem_11_18_iv_degree`
- **Visibility**: public
- **Lines**: 243–250, proof ~5 lines
- **Notes**: none

### `theorem diagonal_coeff_one` (private)
- **Type**: `{R : Type*} [CommRing R] (Φ : BivariatePolynomial R) : (BivariatePolynomial.diagonal Φ).coeff 1 = (Φ.coeff 0).coeff 1 + (Φ.coeff 1).coeff 0`
- **What**: The degree-1 coefficient of the diagonal `Φ(X,X)` is the sum of the two "cross" coefficients of `Φ` of total degree 1 (the `X⁰Y¹` and `X¹Y⁰` coefficients).
- **How**: Induction on `Φ` by `Polynomial.induction_on'` (additivity plus monomial case); the monomial case splits on outer degree 0, 1, ≥2 and uses `Polynomial.coeff_mul_X_pow'` and `Polynomial.coeff_monomial` to see only total degree 1 contributes.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: [`BivariatePolynomial`, `BivariatePolynomial.diagonal`]
- **Used by**: `theorem_11_18_iv_degree`
- **Visibility**: private
- **Lines**: 252–269, proof ~17 lines
- **Notes**: generic bivariate-coefficient lemma; candidate to move next to `BivariatePolynomial.diagonal`

### `def diagonalFixedPoint` (private)
- **Type**: `(m : ℕ+) : ℍ`
- **What**: The point `τ₀ = i/√m` of the upper half-plane, the fixed point of `τ ↦ -1/(mτ)` at which `j(mτ₀) = j(τ₀)`, used to exhibit a root of the diagonal.
- **How**: Constructs `I * (√m)⁻¹` with positivity of the imaginary part checked by `Complex.mul_im` and `norm_num`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `diagonalFixedPoint_scale_eq`, `levelJ_diagonalFixedPoint`, `modularPolynomialDiagonal_map_eval_fixedPoint`, `theorem_11_18_iv_degree`
- **Visibility**: private
- **Lines**: 271–274, definition
- **Notes**: `noncomputable`

### `theorem diagonalFixedPoint_scale_eq` (private)
- **Type**: `(m : ℕ+) : (⟨(m : ℂ) * (diagonalFixedPoint m : ℂ), _⟩ : ℍ) = ModularGroup.S • diagonalFixedPoint m`
- **What**: Scaling the fixed point by `m` coincides with acting on it by the modular inversion `S : τ ↦ -1/τ`; i.e. `m·(i/√m) = -1/(i/√m)` in ℍ.
- **How**: Unfolds the S-action with `UpperHalfPlane.modular_S_smul`, then a direct computation with `Real.sq_sqrt` (so `(√m)² = m`) and `field_simp`, using that `√m ≠ 0`.
- **Hypotheses**: `m` a positive natural (positivity of `√m` used throughout).
- **Uses from project**: [`diagonalFixedPoint`]
- **Used by**: `levelJ_diagonalFixedPoint`
- **Visibility**: private
- **Lines**: 276–293, proof ~16 lines
- **Notes**: none

### `theorem levelJ_diagonalFixedPoint` (private)
- **Type**: `(m : ℕ+) : levelJ m (diagonalFixedPoint m) = j (diagonalFixedPoint m)`
- **What**: At the fixed point `τ₀ = i/√m`, the level function `j(mτ)` agrees with `j(τ)` — producing a common root of both coordinates of the modular curve.
- **How**: Unfolds `levelJ`/`jN` to `j(m·τ₀)`, rewrites `m·τ₀ = S•τ₀` by `diagonalFixedPoint_scale_eq`, and concludes by SL(2,ℤ)-invariance of `j` (`j_modularGroup_smul`).
- **Hypotheses**: `m` a positive natural.
- **Uses from project**: [`levelJ`, `jN`, `j`, `diagonalFixedPoint`, `diagonalFixedPoint_scale_eq`, `j_modularGroup_smul`]
- **Used by**: `modularPolynomialDiagonal_map_eval_fixedPoint`
- **Visibility**: private
- **Lines**: 295–299, proof 3 lines
- **Notes**: none

### `theorem modularPolynomialDiagonal_map_eval_fixedPoint` (private)
- **Type**: `(m : ℕ+) : ((modularPolynomialDiagonal m).map (Int.castRingHom ℂ)).eval (j (diagonalFixedPoint m)) = 0`
- **What**: The complexified diagonal polynomial `Φ_m(X,X)` has `j(i/√m)` as a root — the diagonal is not the zero-degree constant story; it genuinely vanishes somewhere.
- **How**: Commutes diagonal with base change (`BivariatePolynomial.diagonal_map`, `BivariatePolynomial.diagonal_eval`, `modularPolynomial_map_complex`), then applies the defining zero `modularPolynomialC_eval_levelJ_j` at `τ₀` and identifies both arguments via `levelJ_diagonalFixedPoint`.
- **Hypotheses**: `m` a positive natural.
- **Uses from project**: [`modularPolynomialDiagonal`, `BivariatePolynomial.diagonal_map`, `BivariatePolynomial.diagonal_eval`, `modularPolynomial_map_complex`, `modularPolynomialC_eval_levelJ_j`, `levelJ_diagonalFixedPoint`, `diagonalFixedPoint`, `j`]
- **Used by**: `theorem_11_18_iv_degree`
- **Visibility**: private
- **Lines**: 301–307, proof ~6 lines
- **Notes**: none

### `theorem theorem_11_18_iv_degree`
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) : 1 < (modularPolynomialDiagonal m).natDegree`
- **What**: Cox Theorem 11.18(iv), degree half: for nonsquare `m` the diagonal `Φ_m(X,X)` has degree at least 2 (so singular moduli are algebraic integers of honest degree).
- **How**: Degree > 0 because `j(i/√m)` is a transcendental-free root of `Φ_m(X,X)` over ℤ (`modularPolynomialDiagonal_map_eval_fixedPoint` fed into mathlib's `Polynomial.natDegree_pos_of_eval₂_root`, using injectivity of `Int.cast`). Degree ≠ 1: symmetry (`theorem_11_18_iii`, valid since nonsquare forces `m > 1`) plus `BivariatePolynomial.coeff_coeff_swap` shows the two cross-coefficients in `diagonal_coeff_one` are equal, so the degree-1 coefficient of the diagonal is even, contradicting leading coefficient ±1 (`theorem_11_18_iv_leadingCoeff`) via integer arithmetic (`lia`).
- **Hypotheses**: `m` is not a perfect square (in particular `m > 1`).
- **Uses from project**: [`modularPolynomialDiagonal`, `theorem_11_18_iv_leadingCoeff`, `modularPolynomialDiagonal_map_eval_fixedPoint`, `diagonalFixedPoint`, `j`, `theorem_11_18_iii`, `BivariatePolynomial.coeff_coeff_swap`, `diagonal_coeff_one`, `modularPolynomial`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 310–348, proof ~38 lines
- **Notes**: proof >30 lines; uses the `lia` linear-integer-arithmetic tactic (3 call sites)

### `theorem modularPolynomial_three`
- **Type**: `modularPolynomial (3 : ℕ+) = modularPolynomialThreeExplicit`
- **What**: Cox equation (11.22): the level-3 modular polynomial equals the explicit classical bivariate integer polynomial (the degree-4 Smith table).
- **How**: Applies `modularPolynomial_three_of_complex_swap` (from LevelThree.lean), whose remaining hypothesis — symmetry of the complexified `Φ_3` — is supplied by base-changing `theorem_11_18_iii` at `m = 3` through `BivariatePolynomial.map_swap` and `modularPolynomial_map_complex`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomial`, `modularPolynomialThreeExplicit`, `modularPolynomial_three_of_complex_swap`, `theorem_11_18_iii`, `BivariatePolynomial.map`, `BivariatePolynomial.map_swap`, `modularPolynomial_map_complex`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 351–357, proof ~6 lines
- **Notes**: none

### File Summary
- Total declarations: 20 (2 defs, 18 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): [`modularPolynomialDiagonal` (5), `diagonalFixedPoint` (4)]
- Unused declarations (not used by anything in this file): [`theorem_11_18_i`, `theorem_11_18_ii`, `theorem_11_18_iv_degree`, `modularPolynomial_three`] — all four are the file's exported end results
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [`aeval_base_eq_zero_of_forall_eval_eq_zero` (~44), `modularPolynomial_dvd_swap` (~37), `theorem_11_18_iv_degree` (~38); `modularPolynomialC_not_anti` borderline (~30)]
