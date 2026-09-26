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
| Cox | 29 → 30 | 9,786 → 7,693 | 821 → 753 | 52 → 67 | 0 → 0 |
| Modularforms | 26 → 11 | 4,289 → 1,529 | 452 → 124 | 9 → 6 | 1 → 0 |
| ModularFunctions | 11 → 12 | 1,622 → 2,913 | 138 → 334 | 16 → 68 | 0 → 0 |
| jFunction | 5 → 5 | 1,246 → 936 | 157 → 132 | 2 → 3 | 0 → 0 |
| LaurentQExpansion | 2 → 2 | 1,147 → 1,306 | 77 → 124 | 3 → 13 | 0 → 0 |
| qExpansion_tactic | 2 → 2 | 714 → 594 | 71 → 63 | 0 → 0 | 0 → 0 |
| uniqueness.lean | 1 → 1 | 298 → 306 | 15 → 15 | 0 → 0 | 0 → 0 |
| IntegralPowerSeries | 1 → 1 | 230 → 268 | 33 → 39 | 1 → 4 | 0 → 0 |
| Tactic2 | 2 → 2 | 212 → 185 | 27 → 16 | 0 → 0 | 0 → 0 |
| Tests | 3 → 3 | 186 → 194 | 0 → 0 | 0 → 0 | 0 → 0 |
| Basic.lean | 1 → 0 | 2 → 0 | 1 → 0 | 0 → 0 | 0 → 0 |
| **Total** | 83 → 69 | 19,732 → 15,924 | 1792 → 1600 | 83 → 161 | 1 → 0 |

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
