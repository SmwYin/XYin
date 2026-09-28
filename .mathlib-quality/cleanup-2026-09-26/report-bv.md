# Report — switch of the bivariate layer to mathlib's `Polynomial.Bivariate` API (sandbox `bv`), 2026-09-28

## 1. Final build
`lake build` (targets `XYin`, `XYinTest`) in SB:
```
✔ [3712/3713] Built XYin (3.9s)
Build completed successfully (3713 jobs).
```
0 errors, 0 warnings. `grep -rnw sorry XYin XYinTest XYin.lean XYinTest.lean` → 0.
No `admit`/`axiom`/`native_decide`/heartbeat or other option changes.
`lake env lean …/cleanup-2026-09-26/AxiomCheck.lean` (run from SB, unmodified file): all 27 lines
`[propext, Classical.choice, Quot.sound]` (no name in it was renamed).
`#lint only defsWithUnderscore in XYin` (scratch importing `XYin`, `XYinTest`, `Batteries.Tactic.Lint`):
"All linting checks passed" (1293 declarations). Also `#lint only simpNF simpComm simpVarHead
unusedArguments defLemma docBlame synTaut in XYin`: all passed.
`grep -rnwE "BivariatePolynomial|varX|varY|specializeY" XYin XYinTest` → 0 hits (docstrings included).

## 2. Files changed (lines before → after); none added or deleted, `XYin.lean`/`XYinTest.lean` untouched
| file | before | after |
|---|---|---|
| Cox/ModularPolynomial/Construction.lean | 416 | 317 |
| Cox/ModularPolynomial/IntegralDescent.lean | 169 | 169 |
| Cox/ModularPolynomial/Interpolation.lean | 326 | 326 |
| Cox/ModularPolynomial/Irreducibility.lean | 134 | 135 |
| Cox/LaurentPolynomialEvaluation.lean | 187 | 188 |
| Cox/DiagonalLaurent.lean | 105 | 105 |
| Cox/SymmetricCubicLaurent.lean | 277 | 280 |
| Cox/Kronecker.lean | 355 | 355 |
| Cox/KroneckerFrobenius.lean | 109 | 101 |
| Cox/LevelThree.lean | 376 | 372 |
| Cox/CyclicSublattice/Classification.lean | 220 | 223 |
| Cox/Arithmetic.lean | 247 | 247 |
| Cox/SingularModuli.lean | 166 | 166 |
| Cox/UpperHalfPlaneFunctionField.lean (docstrings only) | 168 | 170 |
| Cox/Section11BC.lean (docstring only) | 35 | 35 |
| **total** | **3290** | **3187** (−103) |

Import changes: `LaurentPolynomialEvaluation` `+Mathlib.Algebra.Polynomial.Bivariate` (for `R[X][Y]`).
Opens: `open scoped Polynomial.Bivariate` added to LaurentPolynomialEvaluation, SymmetricCubicLaurent,
Kronecker, KroneckerFrobenius, LevelThree, Classification, Arithmetic; `open Polynomial` added to
LevelThree and Arithmetic (KroneckerFrobenius already had it).

## 3. Done
- Deleted `abbrev Cox.BivariatePolynomial` and every def of namespace `Cox.BivariatePolynomial`
  (`varX`, `varY`, `eval`, `specializeY`, `map`, `diagonal`, `mapRingHom`). All types are now
  `ℤ[X][Y]` / `ℂ[X][Y]` / `(ZMod (p : ℕ))[X][Y]` / `K[X][Y]` / `R[X][Y]`.
- Deleted the lemmas that are mathlib lemmas after the switch and used mathlib directly:
  `specializeY_eval` → `Polynomial.map_evalRingHom_eval`; `eval_eq_evalEval` (rfl, gone);
  `derivative_specializeY` → `Polynomial.derivative_map`; `coe_mapRingHom` → `Polynomial.coe_mapRingHom`
  (no longer needed); `map_injective` → `Polynomial.map_injective _ (Polynomial.map_injective _ hf)`;
  `map_neg`/`map_sub` → `Polynomial.map_neg`/`Polynomial.map_sub`; `eval_swap` →
  `Polynomial.coe_aevalAeval_eq_evalEval` + `Polynomial.Bivariate.aevalAeval_swap`;
  `diagonal_map` → `Polynomial.map_mapRingHom_eval_map` + `Polynomial.map_X`.
- Kept the genuine lemmas, restated for mathlib's expressions and moved to `Polynomial.Bivariate`
  (top of Construction.lean; grep of mathlib: no name clash, no duplicate):
  `ext_of_map_evalRingHom`, `coeff_coeff_swap`, `map_mapRingHom_swap`, `eval_eval_X`,
  `eval₂_eval_X`, `eval_X_swap` (`@[simp]`, as before), `coeff_eval_X_one`.
- Restated every project definition on the layer with the same name and meaning:
  `modularPolynomialC`, `modularPolynomial : ℤ[X][Y]`, `modularPolynomialDiagonal := (modularPolynomial m).eval X`,
  `modularPolynomialThreeExplicit` (Cox (11.22) transliterated letter by letter: Cox's `X ↦ Y`, Cox's
  `Y ↦ C X`; the `let`s are gone), private `modularPolynomialThreeComplexExplicit`,
  `specializeJMod`, `specializeJIntegral`, `bivariateSpecializeLaurent`, `bivariateLaurentEvalHom`.
- Convention documented prominently in the module docstring of `Construction.lean` (section
  "Variable convention": outer `Y` = Cox's root variable `X`, inner `C X` = Cox's parameter `Y`;
  Cox's `Φ_m(x, y)` = `Φ.evalEval y x`; `Φ_m(X, j(τ))` = `Φ.map (evalRingHom (j τ))`;
  `Φ_m(X, X)` = `Φ.eval X`; `(X^p − Y)(X − Y^p)` = `(Y ^ p - C X) * (Y - C X ^ p)`), and briefly at
  `modularPolynomialC`, `modularPolynomial`, `modularPolynomialThreeExplicit`, `theorem_11_18_v`.
  Every other docstring that used the old vocabulary/letters was updated (Cox's `ℂ(Y)` is now
  "`RatFunc ℂ` (Cox's `ℂ(Y)`)" in UHPFF/Irreducibility/Arithmetic; "coefficient variable `Y`" →
  "parameter, i.e. the inner variable `C X`"; `ℤ[X,Y]` → `ℤ[X][Y]`; `Φ(j(9τ), j(3τ))` and
  `P(T, J)` now say which variable gets which value).
- Proof simplifications that fell out: `modularPolynomial_monic` term-mode (3 lines instead of 7);
  `modularPolynomial_dvd_swap` loses its `change` to the old `map`; `modularPolynomialC_not_anti`
  `hdiv` is now `dvd_iff_isRoot.mpr hdiag`; `modularPolynomialC_evalEval_eq_zero_iff` is `rw` + `simp`.

## 4. Rename table (every public declaration renamed or removed)
| old | new |
|---|---|
| `Cox.BivariatePolynomial R` (abbrev) | removed → `R[X][Y]` |
| `Cox.BivariatePolynomial.varX` / `.varY` | removed → `Y` / `C X` |
| `Cox.BivariatePolynomial.eval Φ x y` | removed → `Φ.evalEval y x` |
| `Cox.BivariatePolynomial.specializeY y Φ` | removed → `Φ.map (Polynomial.evalRingHom y)` |
| `Cox.BivariatePolynomial.map f Φ` | removed → `Φ.map (Polynomial.mapRingHom f)` |
| `Cox.BivariatePolynomial.diagonal Φ` | removed → `Φ.eval Polynomial.X` |
| `Cox.BivariatePolynomial.mapRingHom f` | removed → `Polynomial.mapRingHom (Polynomial.mapRingHom f)` |
| `Cox.BivariatePolynomial.specializeY_eval` | removed → `Polynomial.map_evalRingHom_eval` |
| `Cox.BivariatePolynomial.eval_eq_evalEval` | removed (rfl) |
| `Cox.BivariatePolynomial.derivative_specializeY` | removed → `Polynomial.derivative_map` |
| `Cox.BivariatePolynomial.coe_mapRingHom` | removed → `Polynomial.coe_mapRingHom` |
| `Cox.BivariatePolynomial.map_injective` | removed → `Polynomial.map_injective` (twice) |
| `Cox.BivariatePolynomial.map_neg` / `map_sub` | removed → `Polynomial.map_neg` / `Polynomial.map_sub` |
| `Cox.BivariatePolynomial.eval_swap` | removed → `Polynomial.Bivariate.aevalAeval_swap` + `Polynomial.coe_aevalAeval_eq_evalEval` |
| `Cox.BivariatePolynomial.diagonal_map` | removed → `Polynomial.map_mapRingHom_eval_map` (+ `Polynomial.map_X`) |
| `Cox.BivariatePolynomial.specializeY_ext` | `Polynomial.Bivariate.ext_of_map_evalRingHom` |
| `Cox.BivariatePolynomial.coeff_coeff_swap` | `Polynomial.Bivariate.coeff_coeff_swap` |
| `Cox.BivariatePolynomial.map_swap` | `Polynomial.Bivariate.map_mapRingHom_swap` |
| `Cox.BivariatePolynomial.diagonal_eval` | `Polynomial.Bivariate.eval_eval_X` |
| `Cox.BivariatePolynomial.diagonal_eval₂` | `Polynomial.Bivariate.eval₂_eval_X` |
| `Cox.BivariatePolynomial.diagonal_swap` | `Polynomial.Bivariate.eval_X_swap` |
| `Cox.BivariatePolynomial.diagonal_coeff_one` | `Polynomial.Bivariate.coeff_eval_X_one` |
| `Cox.modularPolynomialC_specializeY` | `Cox.modularPolynomialC_map_evalRingHom` |
| `Cox.modularPolynomialC_eval_eq_zero_iff` | `Cox.modularPolynomialC_evalEval_eq_zero_iff` |
| `Cox.modularPolynomialC_eval_act_j` | `Cox.modularPolynomialC_evalEval_j_act` |
| `Cox.modularPolynomialC_eval_levelJ_j` | `Cox.modularPolynomialC_evalEval_j_levelJ` |
| `Cox.modularPolynomialC_diagonal_series` | `Cox.modularPolynomialC_eval_X_eval₂_j` |
| `Cox.modularPolynomialC_diagonal_leadingCoeff_pow` | `Cox.modularPolynomialC_eval_X_leadingCoeff_pow` |
| `Cox.specializeJMod_varX` / `specializeJMod_varY` | `Cox.specializeJMod_Y` / `Cox.specializeJMod_C_X` |
Private: `modularPolynomialCandidateAux_specializeY` → `…_map_evalRingHom`; Arithmetic
`modularPolynomialC_eval_j_levelJ` → `modularPolynomialC_evalEval_levelJ_j`,
`aeval_base_eq_zero_of_forall_eval_eq_zero` → `aeval_base_eq_zero_of_forall_evalEval_eq_zero`.
Note the evaluation-order swap in the names: the old public `…_eval_levelJ_j` (Cox's
`Φ_m(j(mτ), j(τ))`) is now `…_evalEval_j_levelJ` (`evalEval (j τ) (levelJ m τ)`), and the old private
`…_eval_j_levelJ` is now `…_evalEval_levelJ_j`.

Names kept although they contain `map`: `modularPolynomial_map_complex(_swap)`,
`modularPolynomial_map_complex_zero_swap`, `specializeJIntegral_map_zmod/_map_complex`,
`specializeJIntegral_modularPolynomial_map_complex`: their head function is still `Polynomial.map`.
Statements restated (names kept): `existsUnique_modularPolynomialC`, `modularPolynomialC_rightCosetProduct`,
`exists_modularPolynomialZ`, `modularPolynomial_map_complex(_swap)`, `recoveryFormula`,
`specializeJMod_modularPolynomial_eq_formal`, `kronecker_after_specializeJ`,
`modularPolynomial_map_complex_zero_swap`, `modularPolynomialC_zero_iff_normalizedCyclicSublattice`,
`specializeJIntegral_map_zmod/_map_complex`; types only spelled `R[X][Y]` (same term):
`bivariateSpecializeLaurent(_map_apply)`, `bivariateLaurentEvalHom(_apply/_map)`,
`symmetric_bidegree_three_eq_zero_of_laurent_coeff`.

## 5. Book-numbered statements whose text changed (meaning unchanged)
- `theorem_11_18_i (m : ℕ+) : (modularPolynomial m).map (mapRingHom (Int.castRingHom ℂ)) = modularPolynomialC m`
- `theorem_11_18_v (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
   (modularPolynomial p).map (mapRingHom (Int.castRingHom (ZMod (p : ℕ)))) = (Y ^ (p : ℕ) - C X) * (Y - C X ^ (p : ℕ))`
- `theorem_11_23 (m : ℕ+) (u v : ℂ) :
   ((modularPolynomial m).map (Polynomial.mapRingHom (Int.castRingHom ℂ))).evalEval v u = 0 ↔
     ∃ L : PeriodPair, ∃ S : PeriodPair.CyclicSublattice L m, u = S.j ∧ v = L.j`
- `modularPolynomial_three_of_complex_swap`: source text `Polynomial.Bivariate.swap` → `Bivariate.swap`
  (file now `open Polynomial`; identical elaborated statement). `theorem_11_18_ii/iii/iv_*`,
  `theorem_11_9_*`, `modularPolynomial_three`: text unchanged.

## 6. New public API (all in `Polynomial.Bivariate`, file Construction.lean)
- `ext_of_map_evalRingHom [CommRing R] [IsDomain R] [Infinite R] {p q : R[X][Y]}
   (h : ∀ y, p.map (evalRingHom y) = q.map (evalRingHom y)) : p = q`
- `coeff_coeff_swap (p) (i j) : ((swap p).coeff i).coeff j = (p.coeff j).coeff i`
- `map_mapRingHom_swap (f) (p) : (swap p).map (mapRingHom f) = swap (p.map (mapRingHom f))`
- `eval_eval_X (x) (p) : (p.eval X).eval x = p.evalEval x x`
- `eval₂_eval_X (f) (x) (p) : (p.eval X).eval₂ f x = p.eval₂ (eval₂RingHom f x) x`
- `@[simp] eval_X_swap (p) : (swap p).eval X = p.eval X`
- `coeff_eval_X_one (p) : (p.eval X).coeff 1 = (p.coeff 0).coeff 1 + (p.coeff 1).coeff 0`

## 7. Kept on purpose
All genuine lemmas of the old layer (section 6). No mathematics deleted.

## 8. Deferred / follow-ups
- Outside the owned set: `PROJECT_OVERVIEW.md` still mentions the old layer (lines 157, 275, 398,
  461, 472, 477, 509, 553, 571: `BivariatePolynomial`, `varX/varY`, `specializeY_*`,
  `modularPolynomialC_eval_act_j`, `modularPolynomialC_eval_eq_zero_iff`, `specializeJMod_varX/varY`,
  "eval argument order"); `.mathlib-quality/deferred-changes.md` item "`BivariatePolynomial R` is an
  abbreviation …" is now done. Old `.mathlib-quality/overview/*` inventories are historical.
- Optional (not a required rename, so not done): `modularPolynomialC_irreducibleInX` (Irreducibility)
  — "InX" is Cox's root variable, which in mathlib's letters is the outer variable `Y`; a neutral
  name such as `irreducible_map_modularPolynomialC` would avoid the letter clash (2 uses:
  Arithmetic `theorem_11_18_ii`, `modularPolynomialC_not_anti`).

## 9. Perf — `lake env lean XYin/PhD/Cox/LevelThree.lean` (warm, real / user seconds)
before: 9.48 / 10.75, 9.42 / 10.68, 9.91 / 11.04 (first cold run 57.5 s, discarded)
after : 10.01 / 11.10, 9.91 / 11.13, 10.14 / 11.31, final file 9.81 / 11.06, 10.02 / 11.16
≈ +4 %, well under the 1.5× limit; the `decide +kernel` certificate (`explicitCandidateClearedJetThree`)
does not involve the bivariate polynomial and is unchanged.
