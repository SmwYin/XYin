# Inventory: XYin/PhD/Cox/Arithmetic.lean  (346 lines)

Cox Theorem 11.18 (i)–(iv) for the integral modular polynomial `Φ_m ∈ ℤ[X][Y]` (`modularPolynomial m`,
IntegralDescent.lean:287): (i) it maps to the complex `Φ_mᶜ`; (ii) `Φ_mᶜ` is irreducible in `X` over `ℂ(Y)`;
(iii) `Φ_m` is symmetric for `m > 1`; (iv) for nonsquare `m` the diagonal `Φ_m(X,X)` has leading coefficient
`±1` and degree `> 1`. It closes with Cox eq. (11.22): `Φ₃` equals the explicit polynomial of LevelThree.lean,
by feeding (iii) at `m = 3` into `modularPolynomial_three_of_complex_swap`. (11.18(v) lives in
KroneckerFrobenius.lean:221.)

## Declarations

### `theorem Cox.theorem_11_18_i`
- **Type**: `(m : ℕ+) → BivariatePolynomial.map (Int.castRingHom ℂ) (modularPolynomial m) = modularPolynomialC m`
- **What**: Theorem 11.18(i): the integral `Φ_m` has integer coefficients and specializes to the complex `Φ_m`.
- **How**: Term-mode alias of `modularPolynomial_map_complex` (IntegralDescent.lean:290).
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial.map`, `modularPolynomial`, `modularPolynomialC`, `modularPolynomial_map_complex`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 21–24, body 0 lines (alias)
- **Notes**: Pure restatement; Cox's (i) is "Φ_m(X,Y) ∈ ℤ[X,Y]", which the project encodes by the existence of the integral descent — so the alias is the honest formal content.

### `theorem Cox.theorem_11_18_ii`
- **Type**: `(m : ℕ+) → Irreducible (Polynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (modularPolynomialC m))`
- **What**: Theorem 11.18(ii): `Φ_mᶜ(X, Y)` is irreducible as a polynomial in `X` over the field `ℂ(Y)`.
- **How**: Alias of `modularPolynomialC_irreducibleInX` (Irreducibility.lean:134).
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialC`, `modularPolynomialC_irreducibleInX`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 26–30, body 0 lines (alias)
- **Notes**: Stated for the complex polynomial (Cox: irreducible in `ℂ(j)[X]`); no integral-irreducibility statement in the project.

### `theorem Cox.modularPolynomial_map_complex_zero_swap`
- **Type**: `(m : ℕ+) (u v : ℂ) → (map ℤ→ℂ (modularPolynomial m)).eval u v = 0 ↔ (map ℤ→ℂ (modularPolynomial m)).eval v u = 0`
- **What**: The complex zero locus of `Φ_m` is symmetric under `(u,v) ↦ (v,u)`.
- **How**: By Theorem 11.23 a zero `(u,v)` is `(j(L'), j(L))` for a cyclic index-`m` sublattice `L' ⊂ L`; the dual sublattice `mL ⊂ L'` (`CyclicSublattice.dual`, CyclicSublattice.lean:506) is again cyclic of index `m` with `dual_sub_j : S.dual.j = L.j` and `dual_base_j`, which gives the swapped zero.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial.map`, `BivariatePolynomial.eval`, `modularPolynomial`, `theorem_11_23`, `PeriodPair.CyclicSublattice.toPeriodPair`, `PeriodPair.CyclicSublattice.dual`, `dual_sub_j`, `dual_base_j`]
- **Used by**: `modularPolynomialC_eval_j_levelJ`
- **Visibility**: public
- **Lines**: 32–44, body ≈ 8

### `theorem Cox.modularPolynomialC_eval_j_levelJ` (private)
- **Type**: `(m : ℕ+) (τ : ℍ) → (modularPolynomialC m).eval (j τ) (levelJ m τ) = 0`
- **What**: `Φ_mᶜ(j(τ), j(mτ)) = 0` (the swapped form of the distinguished root `Φ_mᶜ(j(mτ), j(τ)) = 0`).
- **How**: `modularPolynomial_map_complex` backwards, `modularPolynomial_map_complex_zero_swap`, `modularPolynomialC_eval_levelJ_j` (Construction.lean:362).
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialC`, `j`, `levelJ`, `modularPolynomial_map_complex`, `modularPolynomial_map_complex_zero_swap`, `modularPolynomialC_eval_levelJ_j`]
- **Used by**: `modularPolynomial_dvd_swap`
- **Visibility**: private
- **Lines**: 46–51, body ≈ 4

### `theorem Cox.aeval_base_eq_zero_of_forall_eval_eq_zero` (private)
- **Type**: `(m : ℕ+) (F : BivariatePolynomial ℂ) (hF : ∀ τ, F.eval (levelJ m τ) (j τ) = 0) → Polynomial.aeval (rightCosetRoot m (baseRightCoset m)) (Polynomial.map (algebraMap ℂ[Y] ℂ(Y)) F) = 0`
- **What**: If `F(j(mτ), j(τ))` vanishes identically on `ℍ`, then `F(α, Y) = 0` in the function field, where `α = j∘(m·)` is the root attached to the identity coset and `Y` acts as `j`.
- **How**: Identify `rightCosetFunction m (baseRightCoset m)` with `levelJ m` (`rightCosetEval_mk`, `baseRightCoset`); show `Polynomial.eval f (F.map evalJ) = 0` in `HolomorphicFunction` by evaluating pointwise with `evaluation τ` (`Polynomial.eval₂_hom`, `Polynomial.eval₂_map`, `evalJ_apply`, `Polynomial.eval₂_evalRingHom`); then rewrite `aeval` as `eval` of the `FunctionField`-mapped polynomial using `ratFuncEvalJ_algebraMap` coefficientwise and `Polynomial.eval₂_at_apply`.
- **Hypotheses**: `F(j(mτ), j(τ)) = 0` for all `τ ∈ ℍ`.
- **Uses from project**: [`BivariatePolynomial`, `BivariatePolynomial.eval`, `levelJ`, `j`, `rightCosetRoot`, `baseRightCoset`, `rightCosetFunction`, `rightCosetEval`, `rightCosetEval_mk`, `HolomorphicFunction`, `evalJ`, `evalJ_apply`, `evaluation`, `FunctionField`, `ratFuncEvalJ_algebraMap`]
- **Used by**: `modularPolynomial_dvd_swap`
- **Visibility**: private
- **Lines**: 53–92, body ≈ 35
- **Notes**: Proof >30 lines. Two `change` steps (L61, L67, L74, L89) work around missing `_apply` lemmas for `rightCosetFunction`/`evaluation`; a public lemma `rightCosetFunction_baseRightCoset : (rightCosetFunction m (baseRightCoset m)).1 = levelJ m` and `aeval_rightCosetRoot_eq_zero_iff` would belong in UpperHalfPlaneFunctionField.lean.

### `theorem Cox.modularPolynomial_dvd_swap`
- **Type**: `(m : ℕ+) → modularPolynomial m ∣ Polynomial.Bivariate.swap (modularPolynomial m)`
- **What**: `Φ_m(X,Y)` divides `Φ_m(Y,X)` in `ℤ[X][Y]`.
- **How**: Over `ℂ(Y)`, `P := Φ_mᶜ` is the minimal polynomial of `α` (`minpoly.eq_of_irreducible_of_monic` with `modularPolynomialC_irreducibleInX`, `modularPolynomialC_monic`, and the root from `aeval_base_eq_zero_of_forall_eval_eq_zero`); `α` is also a root of `swap Φ_mᶜ` (via `modularPolynomialC_eval_j_levelJ` and `BivariatePolynomial.eval_swap`), so `minpoly.dvd`. Descend `ℂ(Y) → ℂ[Y]` with `Polynomial.map_dvd_map` (Algebra/Polynomial/Div.lean:415) and `IsFractionRing.injective`, then `ℂ → ℤ` again with `map_dvd_map`, `Int.cast_injective`, `modularPolynomial_monic`, `BivariatePolynomial.map_swap`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomial`, `modularPolynomialC`, `rightCosetRoot`, `baseRightCoset`, `FunctionField`, `aeval_base_eq_zero_of_forall_eval_eq_zero`, `modularPolynomialC_eval_levelJ_j`, `modularPolynomialC_eval_j_levelJ`, `BivariatePolynomial.eval_swap`, `modularPolynomialC_irreducibleInX`, `modularPolynomialC_monic`, `modularPolynomial_monic`, `BivariatePolynomial.map`, `BivariatePolynomial.map_swap`, `modularPolynomial_map_complex`]
- **Used by**: `theorem_11_18_iii`
- **Visibility**: public
- **Lines**: 94–132, body ≈ 36
- **Notes**: Proof >30 lines; the `change` at L128–130 re-folds `BivariatePolynomial.map` — a `BivariatePolynomial.map` `rfl`-lemma (`map_eq_polynomial_map`) is missing.

### `theorem Cox.modularPolynomialC_not_anti` (private)
- **Type**: `(m : ℕ+) (hm : 1 < (m : ℕ)) → Polynomial.Bivariate.swap (modularPolynomialC m) ≠ -(modularPolynomialC m)`
- **What**: For `m > 1` the complex `Φ_m` is not antisymmetric.
- **How**: Antisymmetry forces the diagonal `Φ_mᶜ(X,X)` to vanish (`BivariatePolynomial.diagonal_swap`, `CharZero.eq_neg_self_iff`, Algebra/Ring/CharZero.lean:96), hence `X − C X ∣ Φ_mᶜ` (`Polynomial.dvd_iff_isRoot`); irreducibility over `ℂ(Y)` (`Irreducible.dvd_iff`, `Polynomial.not_isUnit_X_sub_C`, `Polynomial.natDegree_le_of_dvd`) forces `natDegree ≤ 1`, contradicting `natDegree = |C(m)| > 1` (`modularPolynomialC_natDegree`, `one_lt_card_coxMatrix`).
- **Hypotheses**: `m > 1`.
- **Uses from project**: [`modularPolynomialC`, `BivariatePolynomial.diagonal`, `BivariatePolynomial.diagonal_swap`, `modularPolynomialC_irreducibleInX`, `modularPolynomialC_monic`, `modularPolynomialC_natDegree`, `CoxMatrix`, `one_lt_card_coxMatrix`]
- **Used by**: `theorem_11_18_iii`
- **Visibility**: private
- **Lines**: 134–162, body ≈ 27

### `theorem Cox.eq_or_eq_neg_of_associated_int_bivariate` (private)
- **Type**: `{P Q : BivariatePolynomial ℤ} (h : Associated P Q) → Q = P ∨ Q = -P`
- **What**: Associated elements of `ℤ[X][Y]` differ by a sign.
- **How**: Units of `ℤ[X][Y]` are constants (`Polynomial.isUnit_iff` twice) and units of `ℤ` are `±1` (`Int.isUnit_iff`, Algebra/Group/Int/Units.lean:45).
- **Hypotheses**: `P ~ Q`.
- **Uses from project**: [`BivariatePolynomial`]
- **Used by**: `theorem_11_18_iii`
- **Visibility**: private
- **Lines**: 164–175, body ≈ 10
- **Notes**: No Cox content; general lemma. Mathlib has only the scalar `Int.associated_iff` (Algebra/GCDMonoid/Nat.lean:168); no polynomial analogue found (searched `associated_iff_eq_or_eq_neg`, `eq_or_eq_neg_of_associated`, `Associated … ↔ … ∨`).

### `theorem Cox.theorem_11_18_iii`
- **Type**: `(m : ℕ+) (hm : 1 < (m : ℕ)) → Polynomial.Bivariate.swap (modularPolynomial m) = modularPolynomial m`
- **What**: Theorem 11.18(iii): `Φ_m(X,Y) = Φ_m(Y,X)` for `m > 1`.
- **How**: `Φ_m ∣ swap Φ_m` and (applying the ring hom `swap`, `Polynomial.Bivariate.swap_swap_apply`) `swap Φ_m ∣ Φ_m`, so they are associated (`associated_of_dvd_dvd`); by `eq_or_eq_neg_of_associated_int_bivariate` `swap Φ_m = ±Φ_m`, and the sign `−` is excluded after mapping to `ℂ` by `modularPolynomialC_not_anti`.
- **Hypotheses**: `m > 1` (necessary: `Φ₁ = X − Y` is antisymmetric).
- **Uses from project**: [`modularPolynomial`, `modularPolynomial_dvd_swap`, `eq_or_eq_neg_of_associated_int_bivariate`, `modularPolynomialC_not_anti`, `BivariatePolynomial.map`, `BivariatePolynomial.map_swap`, `modularPolynomial_map_complex`]
- **Used by**: `theorem_11_18_iv_degree`, `modularPolynomial_three`
- **Visibility**: public
- **Lines**: 177–199, body ≈ 20
- **Notes**: L192–198 is a 7-line detour (`simp only [BivariatePolynomial.map, Polynomial.map_neg]`, `change`, `rw`) to push `map` through negation — `BivariatePolynomial.map_neg` is missing from Construction.lean.

### `def Cox.modularPolynomialDiagonal`
- **Type**: `(m : ℕ+) → Polynomial ℤ`
- **What**: The diagonal `Φ_m(X,X) ∈ ℤ[X]`.
- **How**: `BivariatePolynomial.diagonal (modularPolynomial m)`.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial.diagonal`, `modularPolynomial`]
- **Used by**: `modularPolynomialDiagonal_leadingCoeff_pow_two_mul`, `_isRootOfUnity`, `theorem_11_18_iv_leadingCoeff`, `modularPolynomialDiagonal_map_eval_fixedPoint`, `theorem_11_18_iv_degree`
- **Visibility**: public
- **Lines**: 201–203
- **Notes**: Used downstream by SingularModuli.lean.

### `theorem Cox.modularPolynomialDiagonal_leadingCoeff_pow_two_mul`
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) → (modularPolynomialDiagonal m).leadingCoeff ^ (2 * m) = 1`
- **What**: Integral form of Cox (11.19): the leading coefficient of `Φ_m(X,X)` is a `2m`-th root of unity in `ℤ`.
- **How**: Leading coefficients commute with the injective coefficient map (`Polynomial.leadingCoeff_map_of_injective`, Algebra/Polynomial/Degree/Lemmas.lean:297) and `diagonal` commutes with `map` (`BivariatePolynomial.diagonal_map`); then the complex statement `modularPolynomialC_diagonal_leadingCoeff_pow` (DiagonalLaurent.lean:284) and `exact_mod_cast`.
- **Hypotheses**: `m` not a perfect square.
- **Uses from project**: [`modularPolynomialDiagonal`, `BivariatePolynomial.diagonal`, `BivariatePolynomial.diagonal_map`, `modularPolynomialC`, `modularPolynomial_map_complex`, `modularPolynomialC_diagonal_leadingCoeff_pow`]
- **Used by**: `modularPolynomialDiagonal_leadingCoeff_isRootOfUnity`
- **Visibility**: public
- **Lines**: 205–219, body ≈ 11

### `theorem Cox.modularPolynomialDiagonal_leadingCoeff_isRootOfUnity`
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) → ∃ k : ℕ, 0 < k ∧ (modularPolynomialDiagonal m).leadingCoeff ^ k = 1`
- **What**: Existential weakening of the previous lemma.
- **How**: Witness `k = 2m`.
- **Hypotheses**: `m` nonsquare.
- **Uses from project**: [`modularPolynomialDiagonal`, `modularPolynomialDiagonal_leadingCoeff_pow_two_mul`]
- **Used by**: `theorem_11_18_iv_leadingCoeff`
- **Visibility**: public
- **Lines**: 221–227, body ≈ 2
- **Notes**: Middle-man: its only consumer could use `_pow_two_mul` directly.

### `theorem Cox.theorem_11_18_iv_leadingCoeff`
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) → (modularPolynomialDiagonal m).leadingCoeff = 1 ∨ … = -1`
- **What**: Theorem 11.18(iv), first half: for nonsquare `m`, `Φ_m(X,X)` has leading coefficient `±1`.
- **How**: `pow_eq_one_iff_of_ne_zero` (Algebra/Order/Ring/Abs.lean:233) in the linearly ordered ring `ℤ`.
- **Hypotheses**: `m` nonsquare.
- **Uses from project**: [`modularPolynomialDiagonal`, `modularPolynomialDiagonal_leadingCoeff_isRootOfUnity`]
- **Used by**: `theorem_11_18_iv_degree`
- **Visibility**: public
- **Lines**: 229–237, body ≈ 5
- **Notes**: Used downstream by `isIntegral_j_of_isImaginaryQuadratic` (SingularModuli.lean:222).

### `theorem Cox.diagonal_coeff_one` (private)
- **Type**: `{R} [CommRing R] (Φ : BivariatePolynomial R) → (diagonal Φ).coeff 1 = (Φ.coeff 0).coeff 1 + (Φ.coeff 1).coeff 0`
- **What**: The linear coefficient of `Φ(X,X)` is the sum of the `Y¹`- and `X¹`-coefficients.
- **How**: `Polynomial.induction_on'` (additive + monomial cases), `Polynomial.eval_monomial`, `Polynomial.coeff_mul_X_pow'` (Algebra/Polynomial/Coeff.lean:240), `Polynomial.coeff_monomial`.
- **Hypotheses**: none.
- **Uses from project**: [`BivariatePolynomial`, `BivariatePolynomial.diagonal`]
- **Used by**: `theorem_11_18_iv_degree`
- **Visibility**: private
- **Lines**: 239–256, body ≈ 14
- **Notes**: General; belongs with the `BivariatePolynomial.diagonal_*` API in Construction.lean. `CommSemiring` suffices (no subtraction used; `ring` works in commutative semirings), matching `diagonal`'s own typeclass.

### `def Cox.diagonalFixedPoint` (private)
- **Type**: `(m : ℕ+) → ℍ`
- **What**: The point `τ₀ = i/√m ∈ ℍ`, a fixed point of `τ ↦ −1/(mτ)`.
- **How**: `⟨I * (√m)⁻¹, im > 0⟩`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `diagonalFixedPoint_scale_eq`, `levelJ_diagonalFixedPoint`, `modularPolynomialDiagonal_map_eval_fixedPoint`, `theorem_11_18_iv_degree`
- **Visibility**: private
- **Lines**: 258–261, body ≈ 3

### `theorem Cox.diagonalFixedPoint_scale_eq` (private)
- **Type**: `(m : ℕ+) → (⟨m * τ₀, _⟩ : ℍ) = ModularGroup.S • τ₀`
- **What**: `m·τ₀ = S·τ₀ = −1/τ₀` for `τ₀ = i/√m`.
- **How**: `UpperHalfPlane.modular_S_smul` (Analysis/Complex/UpperHalfPlane/MoebiusAction.lean:308), `Real.sq_sqrt`, `field_simp`, `norm_num`.
- **Hypotheses**: none.
- **Uses from project**: [`diagonalFixedPoint`]
- **Used by**: `levelJ_diagonalFixedPoint`
- **Visibility**: private
- **Lines**: 263–280, body ≈ 12

### `theorem Cox.levelJ_diagonalFixedPoint` (private)
- **Type**: `(m : ℕ+) → levelJ m τ₀ = j τ₀`
- **What**: `j(mτ₀) = j(τ₀)` at the fixed point.
- **How**: Unfold `levelJ`/`jN`, rewrite by `diagonalFixedPoint_scale_eq`, then `j_modularGroup_smul S` (jFunction/jfunction.lean:76).
- **Hypotheses**: none.
- **Uses from project**: [`levelJ`, `jN`, `j`, `diagonalFixedPoint`, `diagonalFixedPoint_scale_eq`, `j_modularGroup_smul`]
- **Used by**: `modularPolynomialDiagonal_map_eval_fixedPoint`
- **Visibility**: private
- **Lines**: 282–286, body ≈ 3
- **Notes**: Reusable fact `∃ τ, levelJ m τ = j τ` (ModularFunction/LevelJ.lean would be its home).

### `theorem Cox.modularPolynomialDiagonal_map_eval_fixedPoint` (private)
- **Type**: `(m : ℕ+) → ((modularPolynomialDiagonal m).map (Int.castRingHom ℂ)).eval (j τ₀) = 0`
- **What**: `j(τ₀)` is a root of `Φ_m(X,X)`.
- **How**: `BivariatePolynomial.diagonal_map`, `diagonal_eval`, `modularPolynomial_map_complex`, then `modularPolynomialC_eval_levelJ_j` at `τ₀` with `levelJ_diagonalFixedPoint`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialDiagonal`, `BivariatePolynomial.diagonal_map`, `BivariatePolynomial.diagonal_eval`, `modularPolynomial_map_complex`, `modularPolynomialC_eval_levelJ_j`, `diagonalFixedPoint`, `levelJ_diagonalFixedPoint`, `j`]
- **Used by**: `theorem_11_18_iv_degree`
- **Visibility**: private
- **Lines**: 288–294, body ≈ 4

### `theorem Cox.theorem_11_18_iv_degree`
- **Type**: `(m : ℕ+) (hm : ¬ IsSquare (m : ℕ)) → 1 < (modularPolynomialDiagonal m).natDegree`
- **What**: Theorem 11.18(iv), second half: for nonsquare `m`, `Φ_m(X,X)` has degree `> 1`.
- **How**: `D ≠ 0` (leading coefficient `±1`); `D` has the root `j(τ₀)` so `natDegree > 0` (`Polynomial.natDegree_pos_of_eval₂_root`, Algebra/Polynomial/Degree/Lemmas.lean:236); `natDegree ≠ 1` by parity: symmetry (`theorem_11_18_iii`, `BivariatePolynomial.coeff_coeff_swap`) makes the linear coefficient `2·(Φ.coeff 0).coeff 1` (`diagonal_coeff_one`), which cannot be `±1` (`lia`).
- **Hypotheses**: `m` nonsquare (so `m ≠ 1`, derived inline L315–322 for `theorem_11_18_iii`).
- **Uses from project**: [`modularPolynomialDiagonal`, `theorem_11_18_iv_leadingCoeff`, `modularPolynomialDiagonal_map_eval_fixedPoint`, `diagonalFixedPoint`, `j`, `theorem_11_18_iii`, `BivariatePolynomial.coeff_coeff_swap`, `modularPolynomial`, `diagonal_coeff_one`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 296–335, body ≈ 37
- **Notes**: Proof >30 lines; mixes three separable facts (nonzero, positive degree, degree ≠ 1). The parity argument is the project's own; Cox derives degree `> 1` from the `q`-expansion order (11.19)–(11.20). Terminal result (no in-project consumer).

### `theorem Cox.modularPolynomial_three`
- **Type**: `modularPolynomial (3 : ℕ+) = modularPolynomialThreeExplicit`
- **What**: Cox equation (11.22): the integral level-3 modular polynomial is the explicit one.
- **How**: `modularPolynomial_three_of_complex_swap` applied to `theorem_11_18_iii 3` transported to `ℂ` by `BivariatePolynomial.map_swap` and `modularPolynomial_map_complex`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomial`, `modularPolynomialThreeExplicit`, `modularPolynomial_three_of_complex_swap`, `theorem_11_18_iii`, `BivariatePolynomial.map`, `BivariatePolynomial.map_swap`, `modularPolynomial_map_complex`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 337–344, body ≈ 7
- **Notes**: Terminal. Axioms of the whole chain: `propext, Classical.choice, Quot.sound` (checked on `modularPolynomial_three_of_complex_swap`).

## File Summary
- Total declarations: 20 (2 defs, 18 theorems, 0 instances, 0 other); 12 public, 8 private.
- Key API (used by 3+ others in the file): `modularPolynomialDiagonal` (5), `diagonalFixedPoint` (4), `theorem_11_18_iii` (2, plus external).
- Unused declarations (not used by anything in this file): `theorem_11_18_i`, `theorem_11_18_ii`, `theorem_11_18_iv_degree`, `modularPolynomial_three` — all terminal statements, none referenced by any other XYin `.lean` file (grep); `theorem_11_18_iv_leadingCoeff` and `modularPolynomialDiagonal` are used by SingularModuli.lean.
- Declarations with sorry: none.
- Declarations with set_option: none.
- Proofs >30 lines: `aeval_base_eq_zero_of_forall_eval_eq_zero` (35, L53–92), `modularPolynomial_dvd_swap` (36, L95–132), `theorem_11_18_iv_degree` (37, L297–335).

## Observations (evidence for the analysis phases)

### Mathlib API candidates
- `eq_or_eq_neg_of_associated_int_bivariate` (L164): mathlib has `Int.associated_iff : Associated a b ↔ a = b ∨ a = -b` (Algebra/GCDMonoid/Nat.lean:168) for scalars only; searched `Mathlib/Algebra/Polynomial`, `Mathlib/RingTheory` for `associated_iff_eq_or_eq_neg`, `eq_or_eq_neg_of_associated`, `Associated .* ↔ .* ∨` — nothing for `R[X]`. Candidate general lemma: `Polynomial.associated_iff_eq_or_eq_neg` over any domain whose units are `{±1}`; here proven via `Polynomial.isUnit_iff` (twice) + `Int.isUnit_iff` (Algebra/Group/Int/Units.lean:45).
- `diagonal_coeff_one` (L239): no mathlib analogue (searched `Polynomial.Bivariate` file, `evalEval_*` lemmas at Algebra/Polynomial/Bivariate.lean:44–145 — coefficient formulas for `evalEval`/`eval X` are absent).
- `theorem_11_18_iv_leadingCoeff` (L230): `pow_eq_one_iff_of_ne_zero` (Algebra/Order/Ring/Abs.lean:233) is the right tool and is used; fine.
- Symmetry argument (L177–199) uses mathlib's `Polynomial.Bivariate.swap` (Algebra/Polynomial/Bivariate.lean:248; `swap_swap_apply`:268) correctly; `Associated` + `associated_of_dvd_dvd` is the standard route.
- `theorem_11_18_iv_degree`: `Polynomial.natDegree_pos_of_eval₂_root` (Degree/Lemmas.lean:236) used correctly. No mathlib "symmetric bivariate ⇒ even linear diagonal coefficient" lemma (none expected).
- Hand-rolled pattern: the pointwise-to-function-field transfer in `aeval_base_eq_zero_of_forall_eval_eq_zero` (L64–77) re-proves "a polynomial in `HolomorphicFunction` vanishes iff it vanishes at every `τ`" via `Subtype.ext`/`funext`; that is `Polynomial.eval₂_hom` + the (missing) ring-hom lemma `evaluation_eval : evaluation τ (Polynomial.eval f P) = P.eval (evaluation τ f)` — i.e. `Polynomial.hom_eval` (`RingHom.map_polynomial_eval`-style), which mathlib has as `Polynomial.eval₂_hom`/`Polynomial.hom_eval₂` (Algebra/Polynomial/Eval/Coeff.lean:172).

### Missing API / repeated patterns
- Fragment `rw [BivariatePolynomial.map_swap, modularPolynomial_map_complex]` (with a preceding `congrArg (BivariatePolynomial.map (Int.castRingHom ℂ))`) at L131, L192–194, L341–343: add `modularPolynomial_map_complex_swap (m) : BivariatePolynomial.map (Int.castRingHom ℂ) (swap (modularPolynomial m)) = swap (modularPolynomialC m)` to IntegralDescent.lean.
- `BivariatePolynomial.map` lacks `map_neg`/`map_sub`/`map_add` (`simp`) lemmas — cause of the 7-line detour at L192–198 and the `change` at L128–130. Also missing: `BivariatePolynomial.diagonal_coeff_one` (this file's private lemma), `BivariatePolynomial.diagonal_ne_zero_of_monic`? (not needed here but `hP : P ≠ 0` at L303–305 is derived ad hoc from the leading coefficient).
- `theorem_11_18_iv_degree` should be split: `modularPolynomialDiagonal_ne_zero (hm)`, `modularPolynomialDiagonal_natDegree_pos (m)` (needs only the fixed-point root, no nonsquare hypothesis), `modularPolynomialDiagonal_coeff_one_even (hm : 1 < m) : Even ((modularPolynomialDiagonal m).coeff 1)`.
- The fixed-point block (L258–294, 4 private decls) proves the reusable `∃ τ, levelJ m τ = j τ` — should be a public lemma in ModularFunction/LevelJ.lean (`levelJ_eq_j_at_I_div_sqrt` or similar).
- `modularPolynomialDiagonal_leadingCoeff_isRootOfUnity` (L223) is a middle-man between `_pow_two_mul` and `theorem_11_18_iv_leadingCoeff`.

### Junk candidates
- `theorem_11_18_i`, `theorem_11_18_ii` (L22, L28): 0-line aliases with no consumer anywhere in XYin; keep only if the numbered-theorem naming is a deliberate index (the blueprint/decomposition references them), otherwise fold into docstrings.
- `modularPolynomialDiagonal_leadingCoeff_isRootOfUnity` (L223): single consumer, trivially inlined.
- No dead `#check`/`example`, no commented-out code, no TODO/FIXME, no stale docstrings detected (docstring L26–27 correctly says "over the coefficient field ℂ(Y)").

### Moral duplicates within this batch
- `modularPolynomialC_eval_j_levelJ` (L46) is the swap of `modularPolynomialC_eval_levelJ_j` (Construction.lean:362) — once `theorem_11_18_iii` is available it is literally `theorem_11_18_iii ▸ modularPolynomialC_eval_levelJ_j`, but it is needed *before* symmetry, so the dependency order forces the lattice-theoretic route via `theorem_11_23`. Not removable, but worth a comment.
- `modularPolynomial_map_complex_zero_swap` (L34) and `theorem_11_18_iii` (L178) both express symmetry of `Φ_m` (as zero locus vs as polynomial identity); the former is the seed of the latter.
- `modularPolynomialThreeComplexExplicit_swap` (LevelThree.lean:753) and the `hmap` step of `modularPolynomial_three` (L340–344) both transport `swap` through `map ℤ→ℂ`.

### Generalization notes
- `diagonal_coeff_one` (L239): `[CommRing R]` → `[CommSemiring R]` (uses `induction_on'`, `coeff_add`, `eval_monomial`, `coeff_mul_X_pow'`, `coeff_monomial`, `ring`; no negation).
- `eq_or_eq_neg_of_associated_int_bivariate` (L164): `ℤ` → any `R` with `[CommRing R] [IsDomain R]` and `∀ u : Rˣ, (u:R) = 1 ∨ (u:R) = -1`; and `R[X][Y]` → `R[X]` (one `Polynomial.isUnit_iff` layer per polynomial variable).
- `theorem_11_18_iii` hypothesis `1 < m` is sharp (`Φ₁ = X − Y`); `theorem_11_18_iv_*` hypothesis `¬IsSquare m` matches Cox exactly (for square `m` the leading coefficient is not a unit in general).
- `modularPolynomialDiagonal_leadingCoeff_pow_two_mul`: the exponent `2m` is what DiagonalLaurent.lean:284 provides; Cox's (11.19) only needs "some root of unity", which is why the existential variant exists.
