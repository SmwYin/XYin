# Cleanup and API pass — 2026-09-26

Scope: the user asked to implement the 2026-09-25 overview's recommendations ("do everything that is not dangerous").
Nothing was committed. All changes are in the working tree of branch `PhD_Experiment`.

## Result

- `lake build`: green (both targets `XYin` and the new test library `XYinTest`), 0 warnings.
- `sorry`: **1 → 0**. The last open statement, `dim_gen_cong_levels` (finite-dimensionality of `ModularForm Γ k` for finite-index Γ), is now proved.
- Axiom audit (`AxiomCheck.lean`): 27/27 checked theorems use only `propext`, `Classical.choice`, `Quot.sound`
  (the 22 original headline theorems, plus `dim_gen_cong_levels`, `ModularForm.sturm_bound_of_finiteIndex`,
  `Cox.theorem_11_9_i_subfield`, `Cox.theorem_11_9_ii_subfield`, `Cox.gamma0ModularFunctionField_one`).
- Headline theorem statements are unchanged (checked by the workers and by the audit file).
- Mathlib environment linters (`simpNF simpComm simpVarHead unusedArguments defLemma docBlame synTaut`): 0 issues in 1,329 declarations.

## Size by folder (before → after)

Declarations are lexical `def/theorem/lemma/instance/structure/abbrev/…` headers; tests are the three files now in `XYinTest/`.

| Folder | Files | Lines | Declarations | `@[simp]` | sorry |
|---|---:|---:|---:|---:|---:|
| Cox | 29 → 30 | 9,786 → 7,579 | 821 → 732 | 52 → 65 | 0 → 0 |
| Modularforms | 26 → 11 | 4,289 → 1,472 | 452 → 112 | 9 → 6 | 1 → 0 |
| ModularFunctions | 11 → 12 | 1,622 → 2,913 | 138 → 334 | 16 → 68 | 0 → 0 |
| jFunction | 5 → 5 | 1,246 → 934 | 157 → 130 | 2 → 3 | 0 → 0 |
| LaurentQExpansion | 2 → 2 | 1,147 → 1,306 | 77 → 124 | 3 → 13 | 0 → 0 |
| qExpansion_tactic | 2 → 2 | 714 → 594 | 71 → 63 | 0 → 0 | 0 → 0 |
| uniqueness.lean | 1 → 1 | 298 → 306 | 15 → 15 | 0 → 0 | 0 → 0 |
| IntegralPowerSeries | 1 → 1 | 230 → 268 | 33 → 39 | 1 → 4 | 0 → 0 |
| Tactic2 | 2 → 2 | 212 → 181 | 27 → 15 | 0 → 0 | 0 → 0 |
| Tests | 3 → 3 | 186 → 195 | 0 → 0 | 0 → 0 | 0 → 0 |
| Basic.lean | 1 → 0 | 2 → 0 | 1 → 0 | 0 → 0 | 0 → 0 |
| **Total** | 83 → 69 | 19,732 → 15,748 | 1792 → 1564 | 83 → 159 | 1 → 0 |

## New mathematics (theorems that did not exist before)

- **Sturm bound for arithmetic subgroups** (`Modularforms/SturmBound.lean`, 260 lines, mathlib-only imports):
  `ModularFormClass.sturm_bound`, `ModularForm.sturm_bound`, `ModularForm.sturm_bound_of_finiteIndex`, and the instance
  `ModularForm.instFiniteDimensional [Γ.IsArithmetic] [Γ.HasDetOne] : FiniteDimensional ℂ (ModularForm Γ k)`,
  which proves `dim_gen_cong_levels`. Supporting API: exponential decay ⇔ vanishing q-coefficients, the norm is `O(f)` at i∞.
- **Thm 11.9 as statements about fields of modular functions**: `Cox.theorem_11_9_ii_subfield` (the Γ₀(N)-modular functions
  are exactly ℂ(j, j_N)), `Cox.theorem_11_9_i_subfield` (level one: exactly ℂ(j)), `Cox.gamma0ModularFunctionField_one`.
- **Algebra of modular functions** (`ModularFunctions/Algebra.lean`): `ModularFunction Γ` is an `AddCommGroup`, a `CommRing`
  (±1-determinant Γ), a `Field` (discrete Γ) and a ℂ-algebra; `ModularFunction.range_toMeromorphicField : Set.range toMeromorphicField = subfield Γ`.
- **Counting**: `gamma0_index_eq_card_coxMatrix` ([SL₂(ℤ) : Γ₀(m)] = |C(m)|), `card_coxMatrix_eq_factorization_prod`
  (|C(m)| = ∏ (p^e + p^(e−1)) in ℕ), `card_coxMatrix_of_prime`, `nat_card_cyclicSublattice`.
- **Hermite normal form**: uniqueness `IsColumnHermiteNormalForm.eq_of_mul_isUnit_det`, `Matrix.exists_SL2_mul_eq_upperTriangular`,
  `Matrix.toLin_injective_iff_det_ne_zero`, `rankTwoContent_eq_finset_gcd`, Cramer's rule `HermiteNormalForm.det_smul_repr`.
- **Polynomials / Laurent series**: `Polynomial.eq_or_eq_neg_of_associated` (domains with units ±1), `modularPolynomialC_map_eq_minpoly`,
  the conjugate-counting irreducibility lemma for any nonzero polynomial, `HahnSeries.mapRingHom`, `HahnSeries.coeffSubring`,
  `HahnSeries.leadingCoeff_pow`, `CharP` instance for Hahn series, `LaurentSeries.coeff_single_neg_mul_coe_expand`,
  `PowerSeries.pow_prime_pow_eq_expand`, `Cox.transformedJSeries_injective`.
- **j-function**: explicit integer Laurent coefficients (`j_laurentQExpansion_coeff`), so `Cox.jIntCoeff` is now an explicit
  definition instead of `Classical.choose`.

## Main API added (the user's focus)

- Laurent layer: cusp-function transport family (`cuspFunction_comp_eventuallyEq`, `…comp₂…`, `cuspFunction_eventuallyEq_comp`),
  closure lemmas `meromorphicAt_cuspFunction_{neg,sub,div,inv,pow,const_mul,smul,polynomial_eval}`,
  `laurentqExpansion_{sub,pow,polynomial_eval,const_mul,smul}`, `laurentqExpansion_nat_mul` (period change as `embDomain`),
  pole-order helpers (`poleOrder_eq_iff`, `poleOrder_lt_iff`, `poleRemoved_of_poleOrder_eq_zero`, `coeff_of_geq'`), and a simp API
  (the core file had zero `@[simp]`). Integral power series: cast/coefficient lemmas, `hasCoeffsIn_{pow,X,algebraMap,finset_sum,finset_prod}`.
- Modular functions: growth predicate ⇔ `IsBigO` form and its closure set, growth at all cusps via SL₂(ℤ) representatives,
  `ofMeromorphic_*`, `orderAtAddValuation`, divisor/order completeness lemmas, `toFun_precomp`, `precomp_one/_mul`,
  `HolomorphicFunction.ext`, constructors `ModularFunction.ofLevelOneHolomorphic` / `ofGamma0Holomorphic`.
- Cox: `CoxMatrix.ext`, `ofColumnHNF`, divisibility lemmas, `act_eq_smul_of_mul_eq`, `LevelOneCuspData.of_widthM`,
  `CuspData` named accessors, `Polynomial.coeff_finset_prod_mem`, `jLaurentSeriesWidth` (one series instead of six),
  `coxPhiAtJ_eq_nodal` (Lagrange), `BivariatePolynomial.map` ring-hom lemmas, `modularPolynomialC_eval_eq_zero_iff`.
- q-expansion calculator: the engine now uses mathlib's `ArithmeticFunction.sigma`, `Array.ofFn` and `Finset` sums;
  public bridges `qjCoeffs_eq_qjCoeffInt`, `qjCoeffs_cast`; kernel evaluation time unchanged within noise.

## Cleanup

- 16 `Modularforms/` files deleted (each verified as a duplicate of pinned mathlib: Eisenstein q-expansions, E₂, Δ as η²⁴,
  Dedekind η, cusp-form submodule, level-one dimension formula, summability/derivative helpers, `norm_numI` vendored copy);
  `Delta`/`Δ`/`E₄`/`E₆` now derive their facts from mathlib's `CuspForm.discriminant` / `ModularForm.E₄`.
- `ScratchGS.lean` and the template `XYin/Basic.lean` removed; tests and examples moved out of the library into `XYinTest/`.
- Duplicates unified across files (private copies made public once, e.g. HNF uniqueness, Möbius affine lemma, cusp-function
  lemmas); 35 LevelThree jet lemmas → one `decide +kernel` certificate; the 190-line Frobenius chain → 7 lines.
- Global instances removed: `FunLike (ℍ → ℂ) ℍ ℂ`, `SMul ℕ+ ℍ`. Boilerplate imports and stale comments removed.
- Performance: `Cox/LevelThree.lean` elaborates slightly faster than before (≈0.86×); other kernel-computation files unchanged.

## Kept on purpose (genuine mathematics, currently unused)

E₂ S-transform, E₂ boundedness at i∞, the imaginary-axis reality/positivity results and `ResToImagAxis.lean`, the Γ(2)
generation chain, `arg_pow_aux`, the `hasProd_le_nonneg` family, the circle-integral Laurent-coefficient subtree,
`CuspPeriod.lean` and the `Cusps.lean` chain (in-progress API), `j_laurentQExpansion_isIntegral`, `weierstrassCurve_c₆`.

## Deferred (need a decision or were judged risky)

- Γ(1) → 𝒮ℒ migration of the exported `E₄`/`E₆`/`Delta` types (changes types seen by jFunction/Cox).
- Style renames (naming items of the overview; `defsWithUnderscore` names; theorem-number names) — they may be referenced
  in the thesis text.
- `CuspData` as a structure (named accessors added instead); Dedekind ψ as an `ArithmeticFunction` (did not shorten the proof;
  the ℕ product formula is exposed instead); `LaurentSeries.substMonomial` bridge (no net deletion); `PowerSeries.lifts`;
  rank-n HNF, bidegree-≤n detection, cyclic sublattices over general rank-2 ℤ-modules (High/Medium generalisations);
  the per-declaration `/mathlibable` loop and upstream PRs.
- Refuted during the work: `weierstrassCurve_j` via `j_of_isShortNF` is not shorter; a bundled `laurentqExpansion` ring hom.

## How to review or undo

- Full diff against the pre-cleanup state: `changes-XYin.diff` (this directory).
- Per-worker reports: `report-{mf,lqe,coxa,coxc,mfn,coxb,jq,sorry,fina,finb}.md`; merge log `LOG.md`; follow-up ledger `FOLLOWUPS.md`.
- Pre-cleanup snapshot (all sources, including the 15 git-untracked files): `.mathlib-quality/backups/pre-cleanup-2026-09-26.tar.gz`.
  Restore one file: `tar -xzf .mathlib-quality/backups/pre-cleanup-2026-09-26.tar.gz XYin/PhD/<path>`.

## Follow-up round (2026-09-27/28): mathlib's 𝒮ℒ, one name per object, mathlib-style definition names

Requested by the user: switch the level-one objects from Γ(1) to mathlib's 𝒮ℒ; give definitions with underscores
mathlib-standard names; keep one name per object with no aliases; do not rename the book-numbered theorems.
Build green (0 warnings), 0 sorry, axiom audit 27/27 standard, `#lint only defsWithUnderscore in XYin` clean, no `Γ(1)` left.
Worker report: `report-sl.md` (full rename list, incl. private helpers and statements whose text now shows mathlib objects).

| Old name | New name |
|---|---|
| `E₄`, `E₆` (on Γ(1)); `E4`, `E6` | `ModularForm.E₄`, `ModularForm.E₆` (mathlib, on 𝒮ℒ) |
| `Δ` (function); `Delta` (cusp form on Γ(1)) | `ModularForm.discriminant`; `CuspForm.discriminant` (mathlib) |
| `Δ_ne_zero`, `Delta_q_one_term`, `Delta_eq_E4_E6`, `Delta_boundedfactor` | mathlib's `discriminant_ne_zero`, `discriminant_qExpansion_coeff_one`, `discriminant_eq_E₄_cube_sub_E₆_sq`, `tendsto_atImInfty_tprod_one_sub_eta_q_pow` |
| `Delta_eq_eta_pow`, `Δ_eq_discriminant`, `Delta_apply`, `coe_Delta` | removed (definition / `rfl`), or `CuspForm.coe_discriminant` |
| lemmas named `E4_*`, `E6_*`, `Delta_*`, `Δ_*` about these objects | `E₄_*`, `E₆_*`, `discriminant_*` (e.g. `discriminant_qExpansion_coeff_two…five`, `discriminant_imag_axis_pos`) |
| `jN`, `Cox.levelJ`; `jN_*`, `Cox.levelJ_apply` | `levelJ (N : ℕ) [NeZero N]`; `levelJ_*`, `levelJ_apply` |
| `Cox.UpperHalfPlaneFunctionField.FunctionField` | `UpperHalfPlane.MeromorphicField` |
| `Cox.laurentSeriesMapRingHom` (+ `_coeff`, `_comp_eval₂RingHom`) | `HahnSeries.mapRingHom` (+ `mapRingHom_coeff`, `mapRingHom_comp_eval₂RingHom`) |
| `QExpSimp.one_mem_strictPeriods_gamma1` | mathlib `one_mem_strictPeriods_SL` |
| `UpperHalfPlane.to_qExpansion` (+ lemmas `to_qExpansion_*`) | `UpperHalfPlane.toQExpansion` (+ `toQExpansion_*`) |
| namespace `XYin.PhD.qExpansion_tactic` | namespace `QExpansionTactic` |
| `qj_qexpansion`, `Delta_qexpansion` (+ `_coeff_eq`, `_link`) | `qjQExpansion`, `deltaQExpansion` (+ `_coeff_eq`, `_link`) |
| `Cox.coxPhiFunction_coeff_modularFunction` | `Cox.coxPhiFunctionCoeffModularFunction` |
| `PeriodPair.instSMulUnitsComplex_xYin` (auto-named) | `PeriodPair.instSMulUnitsComplex` |
| tactic target `#qexp Delta`, `qexp_coeff Delta` | `#qexp discriminant`, `qexp_coeff discriminant` |

Unchanged on purpose: all `theorem_11_*` names; file and module names; names of other objects that merely contain these
letters (`integralE4`, `integralDelta`, `deltaOverQ`, `qOverDelta`, `deltaCoeffInt`, `levelJElement`, `jLevelFunctionField`, …).
Statement text changed only where a unified name appears (e.g. `theorem_11_9_i_subfield` now reads `MeromorphicField`).
Not treated as a synonym, noted in `.mathlib-quality/deferred-changes.md`: `BivariatePolynomial R`, an abbreviation of
`R[X][Y]` that carries the project's bivariate API through dot notation.

## Bivariate polynomials on mathlib's API (2026-09-28)

Requested by the user: "switch fully to mathlib's API". The project abbreviation `Cox.BivariatePolynomial` and its
vocabulary are gone; the modular polynomial now lives in mathlib's `R[X][Y]` (`Mathlib/Algebra/Polynomial/Bivariate.lean`).
Convention, stated in the module docstring of `Cox/ModularPolynomial/Construction.lean`: Cox's Φ_m(X, Y) is `Φ : ℤ[X][Y]`
whose OUTER variable `Y` plays Cox's root variable X and whose inner variable `C X` plays Cox's parameter Y, so Cox's
Φ_m(x, y) is `Φ.evalEval y x`. Build green (0 warnings), 0 sorry, axiom audit 27/27, lint clean. Worker report: `report-bv.md`.

| Old (project) | New (mathlib or `Polynomial.Bivariate`) |
|---|---|
| `BivariatePolynomial R` | `R[X][Y]` |
| `varX`, `varY` | `Y`, `C X` |
| `eval Φ x y` | `Φ.evalEval y x` |
| `specializeY y Φ` | `Φ.map (evalRingHom y)` |
| `map f Φ`; bivariate `mapRingHom f` | `Φ.map (mapRingHom f)`; `mapRingHom (mapRingHom f)` |
| `diagonal Φ` | `Φ.eval X` |
| `specializeY_eval`, `derivative_specializeY`, `coe_mapRingHom`, `map_injective`, `map_neg`, `map_sub`, `eval_swap`, `diagonal_map`, `eval_eq_evalEval` | mathlib's `map_evalRingHom_eval`, `derivative_map`, `Polynomial.coe_mapRingHom`, `map_injective`, `map_neg`, `map_sub`, `Bivariate.aevalAeval_swap`, `map_mapRingHom_eval_map`; `rfl` |
| `specializeY_ext`, `coeff_coeff_swap`, `map_swap`, `diagonal_eval`, `diagonal_eval₂`, `diagonal_swap`, `diagonal_coeff_one` | `Polynomial.Bivariate.ext_of_map_evalRingHom`, `.coeff_coeff_swap`, `.map_mapRingHom_swap`, `.eval_eval_X`, `.eval₂_eval_X`, `.eval_X_swap`, `.coeff_eval_X_one` |
| `modularPolynomialC_specializeY` | `modularPolynomialC_map_evalRingHom` |
| `modularPolynomialC_eval_eq_zero_iff`, `modularPolynomialC_eval_act_j`, `modularPolynomialC_eval_levelJ_j` | `modularPolynomialC_evalEval_eq_zero_iff`, `modularPolynomialC_evalEval_j_act`, `modularPolynomialC_evalEval_j_levelJ` |
| `modularPolynomialC_diagonal_series`, `modularPolynomialC_diagonal_leadingCoeff_pow` | `modularPolynomialC_eval_X_eval₂_j`, `modularPolynomialC_eval_X_leadingCoeff_pow` |
| `specializeJMod_varX`, `specializeJMod_varY` | `specializeJMod_Y`, `specializeJMod_C_X` |
| `modularPolynomialC_irreducibleInX` | `irreducible_map_modularPolynomialC` |

Book-numbered statements whose text changed (names and meaning unchanged):
- 11.18(i): `(modularPolynomial m).map (mapRingHom (Int.castRingHom ℂ)) = modularPolynomialC m`
- 11.18(v): `(modularPolynomial p).map (mapRingHom (Int.castRingHom (ZMod p))) = (Y ^ p - C X) * (Y - C X ^ p)`, Cox's (X^p − Y)(X − Y^p) in mathlib's letters
- 11.23: `((modularPolynomial m).map (mapRingHom (Int.castRingHom ℂ))).evalEval v u = 0 ↔ …`
