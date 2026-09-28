# Project Overview: XYin

## Current status — after the 2026-09-26 cleanup and API pass

`lake build` green (3,713 jobs, 0 warnings) · **0 `sorry`** · 27/27 audited theorems use only
`propext`, `Classical.choice`, `Quot.sound` · mathlib pin `2abc242` · branch `PhD_Experiment` (changes not committed).

On 2026-09-26 most recommendations of the 2026-09-25 overview below were implemented. Full account:
`.mathlib-quality/cleanup-2026-09-26/SUMMARY.md` (what changed, new theorems and API, what was kept or deferred, how to
review or undo); full diff against the pre-cleanup tree: `.mathlib-quality/cleanup-2026-09-26/changes-XYin.diff`;
pre-cleanup snapshot: `.mathlib-quality/backups/pre-cleanup-2026-09-26.tar.gz`.

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

Highlights:
- The last `sorry` is proved: `dim_gen_cong_levels` follows from a new Sturm bound for arithmetic subgroups
  (`Modularforms/SturmBound.lean`, `ModularForm.sturm_bound_of_finiteIndex`, `FiniteDimensional ℂ (ModularForm Γ k)`).
- New theorems: `Cox.theorem_11_9_ii_subfield` (Γ₀(N)-modular functions = ℂ(j, j_N) as subfields), `Cox.theorem_11_9_i_subfield`,
  `gamma0_index_eq_card_coxMatrix`, HNF uniqueness `IsColumnHermiteNormalForm.eq_of_mul_isUnit_det`, `Polynomial.eq_or_eq_neg_of_associated`.
- `ModularFunction Γ` is now a field (`ModularFunctions/Algebra.lean`, `range_toMeromorphicField = subfield Γ`).
- About 400 API declarations added (Laurent-layer closure/transport/simp lemmas, growth-predicate closure set, Hahn/Laurent-series
  ring homs and subrings, `CoxMatrix` API); `@[simp]` lemmas 83 → 161.
- 16 `Modularforms/` files that duplicated pinned mathlib were deleted; duplicates across folders unified; tests moved to `XYinTest/`.
- 2026-09-28: level-one objects use mathlib's `𝒮ℒ` convention (`ModularForm.E₄/E₆`, `ModularForm.discriminant`,
  `CuspForm.discriminant`); one name per object (`levelJ`, `MeromorphicField`, `HahnSeries.mapRingHom`); definitions renamed
  to mathlib style (`toQExpansion`, namespace `QExpansionTactic`, …). Rename table: `.mathlib-quality/cleanup-2026-09-26/SUMMARY.md`.
- 2026-09-28: the bivariate layer uses mathlib's `R[X][Y]` API (`evalEval`, `Y`, `C X`, `Bivariate.swap`); `Cox.BivariatePolynomial`
  is gone. Convention and rename table in the same summary. Names in the 2026-09-25 analysis below predate these renames.

Still open, deliberately postponed: `CuspData` as a structure, Dedekind ψ as an `ArithmeticFunction`, Hermite normal
form in any rank, upstream pull requests to mathlib, and a few smaller redesigns. Each is described, with the reason
for postponing and an effort estimate, in `.mathlib-quality/deferred-changes.md`.

---

## 2026-09-25 overview (pre-cleanup analysis — kept for reference; its file names, line numbers and counts describe the tree before 2026-09-26)

Generated: 2026-09-25 · mathlib pin `2abc242` (2026-05-28) · Lean v4.30.0 · branch `PhD_Experiment` ·
`lake build` green (oleans current as of 2026-09-21) · active `sorry`: **1** (`dim_gen_cong_levels`,
Modularforms/DimensionFormulas.lean:198)

Scope: the **entire repository** (83 `.lean` files, 19,732 lines, 1,792 lexical declarations). This is the first
overview to cover `PhD/Modularforms/` (26 files, excluded from the July 2026 pass) and `PhD/ModularFunctions/`
(11 files, created September 2026). Focus requested by the user: **missing API** and **code that can be cleaned up**.

Evidence (all under `.mathlib-quality/overview/`):
- `inventory-2026-09-25/<Module>.md` — per-declaration inventories for all 83 files (1,798 entries; Type / What / How /
  Hypotheses / Uses / Used-by / Notes + per-file Observations), plus `_worker-digests.md`, `_crossfile-usage.tsv`,
  `_public-unused-candidates.tsv`, `_import-graph.md`, `_file-stats.tsv`, `_step9-prefilter.tsv`, `_mathlib-collisions.tsv`.
- `analysis-2026-09-25/step4-analytic.md`, `step4-cox-compute.md` (mathlib audit), `step5-duplications.md` (pairwise table),
  `step6-generalization.md`, `step7-api-analytic.md`, `step7-api-cox.md` (API design), `step8-junk.md` (junk, with safe
  deletion order), `step9-mathlibable-triage.md`.
- Previous overviews: `PROJECT_OVERVIEW-archive-2026-09-21.md` (July 2026 overview + the two 2026-09-21 passes) and the
  July evidence in `analysis/`, `inventory/`, `mathlibable/`.

Method notes. 13 inventory workers read every file in full; 7 analysis agents (plus a workflow with adversarial
verification for the duplication table) re-verified every carried-forward July item against the current source. The
`lean-lsp` and `chatgpt-math` MCP servers were unavailable for most of the session, so mathlib claims are grep-verified
against the pinned source and, where marked **[C]**, confirmed by a `lake env lean` scratch compile (about 25 compiles
in total). The Step 9 per-declaration `/mathlibable` loop was **not** run (see Part 8).

---

## Executive Summary

XYin formalises Cox, *Primes of the form x²+ny²*, Ch. 11 §§B–C on top of a self-built modular-forms layer: the
j-invariant classification of ℂ-lattices, level-one and Γ₀(m) modular functions (Thm 11.9 in both pointwise and
intermediate-field form), the modular polynomial Φ_m (construction, interpolation, irreducibility, ℤ-descent, the explicit
Φ₃ certified by `decide +kernel`), Cox matrices and cyclic sublattices (Thm 11.23), the Kronecker congruence
(Thm 11.18(v)), and integrality of singular moduli. Supporting infrastructure: a Laurent-expansion-at-the-cusp theory for
meromorphic-at-∞ functions, a bundled `ModularFunction Γ` living in a codiscrete meromorphic germ field, a rank-two Hermite
normal form, integral power series, and a kernel-checked q-expansion coefficient calculator. Mathematically the project
is complete: one sorry remains (finite-dimensionality of `ModularForm Γ k` for general Γ), all headline theorems are
axiom-clean.

The biggest finding is that **the pinned mathlib has caught up with the `Modularforms/` folder**. Between the project's
start and the 2026-05-28 pin, mathlib gained `EisensteinSeries.E₂` with its full slash law, `ModularForm.discriminant`
as η²⁴ with the `CuspForm` division equivalence, `DedekindEta`, `CuspFormSubmodule.IsCuspForm`, the level-one dimension
formula and Sturm bound, `Cusps.lean`/`BoundedAtCusp.lean`, and the `qExpansion` ring-hom API. As a result 4,100 of the
folder's 4,289 lines duplicate mathlib or are dead; project-wide, **≈ 5,300 lines (27 %) are removable without
mathematical loss** (Part 7 gives a safe, import-ordered deletion sequence). The single blocker is a convention: the
project states results over `↑Γ(1)` while mathlib uses `𝒮ℒ`, and the two do not unify (scratch-verified isDefEq
timeout); a six-step migration plan with verified bridges (`ModularForm.mcast … Gamma_one_coe_eq_SL`) is in Part 3.

On the user's two focus areas: (1) **Missing API** — Parts 6 lists ≈ 80 missing lemmas, of which ≈ 30 were
scratch-compiled as 1–8-line statements this session. The highest-leverage ones are a cusp-function transport lemma
(`cuspFunction h f =ᶠ[𝓝[≠]0] f ∘ ofComplex ∘ invQParam h`, 13 sites), a Laurent-series monomial-substitution bridge
(`substMonomial` + `laurentqExpansion_comp_of_qParam_eq`, ≈ 210 lines across four files), `laurentqExpansion_polynomialIn`
(two verbatim 20-line inductions), one `jLaurentSeriesWidth R m` replacing four "Laurent series of j" definitions, a
`CuspData` structure with `apply_smul` (24 projection sites), `CoxMatrix.ext`/`ofColumnHNF`, and simp families for the
core Laurent definitions (LaurentQExpansion.lean has zero `@[simp]`). (2) **Cleanup** — beyond the dead code, ≈ 15 Cox
definitions hand-roll mathlib abstractions that would unlock large APIs: `Matrix.BlockTriangular`, `Finset.gcd`,
`Matrix.adjugate`, `Submodule.equivSubtypeMap`, `HahnSeries.embDomain`, `Polynomial.evalEval`, `Lagrange.nodal`,
`UpperHalfPlane.glAction`/`posRealAction`, `ArithmeticFunction` (Dedekind ψ). Roughly 45 declarations are verified
mathlib gaps worth upstreaming (Part 8), the strongest being the lattice-uniqueness block, `HahnSeries.mapRingHom` /
`coeffSubring` / `leadingCoeff_pow` (all compiled this session), Dedekind ψ with the Γ₀(m) index formula, and the two
fully general conjugate-counting irreducibility lemmas.

## Statistics

- Files: 83 (+ root `XYin.lean`, orphan `ScratchGS.lean`) · Lines: 19,732 · Declarations: 1,792 (600 private, 1,192 public;
  29 instances; 83 `@[simp]`, 28 `@[fun_prop]`, 2 `@[ext]` tags)
- By folder (files / lines / decls / public): Cox 29 / 9,786 / 821 / 343 · Modularforms 26 / 4,289 / 452 / 437 ·
  ModularFunctions 11 / 1,622 / 138 / 125 · jFunction 5 / 1,246 / 157 / 87 · LaurentQExpansion 2 / 1,147 / 77 / 53 ·
  qExpansion_tactic 3 / 780 / 71 / 71 · Tactic2 4 / 332 / 27 / 27 · uniqueness 1 / 298 / 15 / 15 · IntegralPowerSeries 1 / 230 / 33 / 33
- Sorries: 1 · `set_option`: 1 (`linter.style.header false`, link.lean:4) · `native_decide`: 0 in the library · `decide +kernel`: 30 (LevelThree)
- Mathlib API audit: 51 definitions/lemma families to replace with mathlib (23 analytic + 28 Cox/compute), 24 API re-expressions, 25 hand-rolled pattern families
- Moral duplications: 214 pairs rated in source (171 non-DISTINCT: 22 DELETE-ONE, 12 REPLACE-WITH-MATHLIB, 28 UNIFY, 27 DERIVE, 22 PUBLICIZE, 60 EXTRACT-HELPER; 43 DISTINCT); 45 deletion-grade rows adversarially verified (34 confirmed, 11 corrected); ≈ 1,700–2,100 net lines saved; 77 shared helpers proposed (21 scratch-verified)
- Generalization opportunities: 41 (22 Low, 6 Low–Medium, 9 Medium, 4 High) + 8 refuted
- Missing-API items: 44 analytic + 40 Cox missing lemmas; 11 + 25 definitions with thin simp API; 9 + 8 instance/structure verdicts; 22 + 20 long proofs mapped
- Junk: 33 whole files (≈ 4,580 net lines), 83 dead declarations (569 lines), 6 wrappers, 7 inlines, 15 REPLACE, 74 non-declaration items — ≈ 5,300 lines removable
- Mathlibable: pre-filter 1,792 → 1,088 candidates (704 SKIP); July verdicts carried forward: 1 YES-add-as-is, 2 YES-but-generalise-first, 2 NO-composable, 8 BORDERLINE; triage this session: ≈ 45 LIKELY-YES, 8 BORDERLINE families, ≈ 200 NO-mathlib-has-it, ≈ 30 NO-composable; **full per-declaration runs: 0 this session**

---

## Part 1: Declaration Inventory

Per-declaration inventories are in `.mathlib-quality/overview/inventory-2026-09-25/<Module.Path>.md` (one per file,
1,798 entries; every entry has Type / What / How / Hypotheses / Uses-from-project / Used-by / Visibility / Lines / Notes,
followed by File Summary and Observations). Per-file character (Decls column = total (private); simp = `@[simp]` tags):

| File | Lines | Decls (priv) | simp | Character |
|---|---:|---:|---:|---|
| `XYin/Basic.lean` | 2 | 1 (0) | 0 | Lake template stub `hello` — REMOVE |
| `Cox/Arithmetic.lean` | 347 | 20 (9) | 0 | Thm 11.18(i–iv); (i),(ii) are 0-line aliases; `eq_or_eq_neg_of_associated_int_bivariate` general |
| `Cox/CoxMatrices.lean` | 15 | 0 (0) | 0 | Umbrella |
| `Cox/CoxMatrices/Basic.lean` | 823 | 76 (41) | 6 | `CoxMatrix` (no `@[ext]`, no `ofColumnHNF`), reduction, right cosets; `act` hand-rolls Möbius (= `glAction`) |
| `Cox/CoxMatrices/Cardinality.lean` | 279 | 22 (21) | 1 | \|C(m)\| = Dedekind ψ (absent from mathlib); `card_coxMatrix` ℚ-only and unused |
| `Cox/CoxMatrices/LaurentExpansion.lean` | 355 | 23 (13) | 0 | Cox eq. 11.13; `transformedJSeries` = `embDomain` (VERIFIED); ~180-line private chain collapsible via one substitution bridge |
| `Cox/CyclicSublattice.lean` | 542 | 71 (47) | 8 | Cyclic sublattices; `dualMatrix` = `adjugate`, `carrierEquiv` = `equivSubtypeMap` (both still hand-rolled, ≈140 lines) |
| `Cox/CyclicSublattice/Classification.lean` | 371 | 27 (10) | 4 | Thm 11.23 sublattices ≃ Cox matrices; :28–175 ℂ-free (generalise to any rank-2 free ℤ-module) |
| `Cox/DiagonalLaurent.lean` | 294 | 19 (9) | 0 | Φ_m(X,X) leading coefficient ±1; duplicated copyright header; generic lemmas proved at K=ℂ |
| `Cox/FormalCoxProduct.lean` | 229 | 15 (13) | 0 | ∏(X − j∘σ) with integral coefficients via Galois descent; hand-built `HahnSeries.mapRingHom` twin |
| `Cox/HermiteNormalForm.lean` | 409 | 24 (9) | 1 | Rank-two column HNF over ℤ; `belowDiagonal_eq_zero` = `BlockTriangular`, `rankTwoContent` = `Finset.gcd`; HNF family BORDERLINE (rank-n decision) |
| `Cox/Kronecker.lean` | 772 | 63 (21) | 11 | Mod-p Laurent series, Frobenius/expand; 4 anonymous `HahnSeries` builds (= `embDomain`); 4 series defs collapsible to one |
| `Cox/KroneckerFrobenius.lean` | 234 | 14 (7) | 1 | Thm 11.18(v); re-proves `single_order_mul_powerSeriesPart`; unused `Fact (Prime p)` hyps |
| `Cox/LatticeJ.lean` | 633 | 54 (21) | 4 | `PeriodPair` scaling/homothety/discriminant/j (mathlib has PeriodPair but none of these); imports `uniqueness` for 3 uses |
| `Cox/LaurentPolynomialEvaluation.lean` | 152 | 10 (1) | 1 | `laurentSeriesMapRingHom` (no mathlib `HahnSeries.mapRingHom`), poly-eval into Laurent series; `Field K` → `IsDomain` |
| `Cox/LevelThree.lean` | 859 | 108 (106) | 1 | Explicit Φ₃ via 30 `decide +kernel` jets; 106/108 private; ≈210-line split collapsible to 1–2 decls (6.7 s measured) |
| `Cox/ModularFunction.lean` | 440 | 18 (13) | 0 | Thm 11.9(i) via pole clearing; two generic meromorphic-order lemmas (upstream candidates) |
| `Cox/ModularFunction/CuspData.lean` | 155 | 15 (3) | 0 | Raw `CuspData` triple (anonymous ∧, `.1/.2.1/.2.2` at 20+ sites → structure) |
| `Cox/ModularFunction/LevelJ.lean` | 330 | 22 (17) | 3 | `levelJ` (= `jN`), affine/scaling actions; :159–257 re-derive column HNF; `complex_mobius_scale_eq_affine` exact copy of CoxMatrices/Basic:699 |
| `Cox/ModularFunctionField.lean` | 187 | 15 (0) | 2 | Thm 11.9(ii) as equality of intermediate fields; does not yet assert the range is a subfield (needs ring ops on `ModularFunction`) |
| `Cox/ModularPolynomial.lean` | 17 | 0 (0) | 0 | Umbrella (docstring omits AnalyticSupport) |
| `Cox/ModularPolynomial/AnalyticSupport.lean` | 97 | 5 (0) | 0 | Cusp-meromorphy of Cox product coefficients; verbatim twins of Interpolation lemmas |
| `Cox/ModularPolynomial/Construction.lean` | 380 | 43 (5) | 2 | `BivariatePolynomial`, Φ_m over ℂ; eval convention flipped vs mathlib `evalEval`; 4 wrappers = Bivariate.lean |
| `Cox/ModularPolynomial/IntegralDescent.lean` | 306 | 24 (16) | 0 | ℤ-descent of Φ_m; width-1 inductions verbatim-duplicated in DiagonalLaurent; `integerCoeffLaurentSeries` = missing `HahnSeries.coeffSubring` |
| `Cox/ModularPolynomial/Interpolation.lean` | 499 | 37 (33) | 0 | Thm 11.9(ii) pointwise; un-normalised Lagrange sum (coincident CM nodes); `eval_derivative_prod_X_sub_C_at` now a 3-line wrapper |
| `Cox/ModularPolynomial/Irreducibility.lean` | 142 | 11 (10) | 0 | Two fully general conjugate-counting lemmas (PR candidates) + irreducibility of Φ_m |
| `Cox/Section11BC.lean` | 23 | 0 (0) | 0 | Umbrella; docstring stale (cites non-existent Lemma 11.10/11.11/11.24 names) |
| `Cox/SingularModuli.lean` | 239 | 15 (4) | 1 | Singular moduli are algebraic integers; `not_isSquare…aux` = `Nat.not_exists_sq'`; even/odd twin lemmas |
| `Cox/SymmetricCubicLaurent.lean` | 392 | 39 (38) | 2 | Bidegree-≤3 symmetric detection (hard-coded, not parametric); `bivariateLaurentEvalHom` = `aevalAeval` |
| `Cox/UpperHalfPlaneFunctionField.lean` | 265 | 31 (11) | 4 | `FunctionField` = abbrev of `MeromorphicField`; `evalJ`/`ratFuncEvalJ`; Cox-matrix Laurent facts misplaced here |
| `IntegralPowerSeries/IntegralPowerSeries.lean` | 230 | 33 (0) | 1 | `HasCoeffsIn`/`IsIntegralPowerSeries` — seed of a missing `PowerSeries.lifts`; middle abbrev layer + ModularForms section dead |
| `LaurentQExpansion/Algebra.lean` | 440 | 28 (17) | 3 | Ring laws for `laurentqExpansion` (≈120 lines of hand-expanded `map_*`), `shiftedLaurent`, `analyticTaylor_comp_pow` |
| `LaurentQExpansion/LaurentQExpansion.lean` | 707 | 49 (7) | 0 | Core: `poleOrder`, `poleRemoved`, `to_qExpansion`, `laurentqExpansion`; zero `@[simp]`; circle-integral subtree :600–706 dead |
| `ModularFunctions/Basic.lean` | 98 | 13 (0) | 2 | Bundled `ModularFunction Γ` (verbatim copy of mathlib `ModularForm` skeleton); no ring ops — the main gap for 11.9(ii) |
| `ModularFunctions/Congruence.lean` | 151 | 9 (2) | 2 | Γ₀(N) restriction/cusp data; `periodic_comp_ofComplex_of_vadd` upstreamable |
| `ModularFunctions/CuspGrowth.lean` | 115 | 7 (4) | 0 | `IsOfExponentialGrowth` (should be an `IsBigO` along `atImInfty`); `meromorphicAt_zero_of_bounded_pow` general |
| `ModularFunctions/CuspPeriod.lean` | 63 | 3 (0) | 0 | Periods at cusps for conjugates; two small mathlib gaps |
| `ModularFunctions/Cusps.lean` | 89 | 5 (0) | 0 | `OnePoint.IsMeromorphicAt`; growth ⇔ meromorphy at cusps |
| `ModularFunctions/FieldAction.lean` | 150 | 16 (5) | 3 | SL₂-action on the germ field; `holomorphicFunctions` is a `Subring` (should be `Subalgebra ℂ`) |
| `ModularFunctions/GrowthAtCusp.lean` | 74 | 5 (0) | 0 | Growth at every cusp = mathlib `BoundedAtCusp.lean` with growth predicate swapped |
| `ModularFunctions/JInvariant.lean` | 58 | 5 (0) | 1 | j as a bundled `ModularFunction`; `j_periodic` real API |
| `ModularFunctions/MeromorphicField.lean` | 659 | 67 (0) | 8 | Codiscrete meromorphic germ field (`Filter.Germ` + `Subring.map`) — mathlib-idiomatic; 8 codiscrete/NeBot lemmas upstreamable; 13 dead decls |
| `ModularFunctions/NormalFormGrowth.lean` | 67 | 2 (0) | 0 | `MeromorphicNFAt.analyticAt_of_eventually_norm_le` — strong upstream candidate |
| `ModularFunctions/NormalFormSlash.lean` | 98 | 6 (2) | 0 | NF stability under analytic reparametrisation / conj — three upstream candidates |
| `Modularforms/AtImInfty.lean` | 28 | 3 (0) | 0 | `Filter.eventually_atImInfty` small ForMathlib (wrong namespace); 2 dead |
| `Modularforms/BigO.lean` | 62 | 8 (1) | 0 | 8 lemmas, all mathlib (`linear_inv_isBigO_*`); ENTIRELY DEAD |
| `Modularforms/Delta.lean` | 409 | 41 (1) | 0 | `Δ`/`Delta` = mathlib `discriminant`/`CuspForm.discriminant`; 27/42 decls dead; global `SMul ℕ+ ℍ` instance |
| `Modularforms/DimensionFormulas.lean` | 201 | 30 (2) | 0 | Γ(1)-transports of mathlib `LevelOne/DimensionFormula.lean`; holds the ONLY sorry (`dim_gen_cong_levels`, general-Γ finite-dimensionality) |
| `Modularforms/E2.lean` | 110 | 18 (0) | 0 | Renames of mathlib `EisensteinSeries.G2/E2/D2`; keep `E₂_S_transform`, `E₂_eq` |
| `Modularforms/Eisenstein.lean` | 693 | 71 (0) | 3 | E₄/E₆/E₂ facts; ≈40 live lines of 692 — mathlib now has E_k q-expansions; keep B₆, E₂ boundedness, imag-axis reality |
| `Modularforms/Eisensteinqexpansions.lean` | 156 | 15 (0) | 0 | `E` = mathlib `ModularForm.E`; :26–145 dead (mathlib `gammaSetDivGcdEquiv`) |
| `Modularforms/ForMathlib_Cusps.lean` | 22 | 2 (0) | 0 | Two live lemmas composing `isCusp_iff_isCusp_SL2Z` + `isZeroAt_iff_forall_SL2Z` — genuinely ForMathlib |
| `Modularforms/IsCuspForm.lean` | 153 | 17 (1) | 0 | Entire file = mathlib `CuspFormSubmodule.lean`; blocked only by Γ(1)-vs-𝒮ℒ |
| `Modularforms/NormNumI.lean` | 206 | 16 (0) | 0 | Vendored `norm_numI` extension declared into `Mathlib.Meta.NormNum` namespaces; invoked nowhere |
| `Modularforms/ResToImagAxis.lean` | 404 | 45 (4) | 2 | Restriction to the imaginary axis (no mathlib analogue); 18 unused; decay section dead |
| `Modularforms/SlashActionAuxil.lean` | 288 | 27 (5) | 0 | `slash_S_apply`/generators = mathlib; Γ(2) generation genuinely new but unused (~190 lines) |
| `Modularforms/Summability/Basic.lean` | 207 | 25 (0) | 0 | ℤ/ℕ+ tsum shuttling; 7 exact mathlib wrappers; 4 live decls |
| `Modularforms/Summability/QExpansion.lean` | 297 | 25 (0) | 0 | By-hand `qExpansion_identity_pnat` (mathlib ships it); 0 external uses |
| `Modularforms/Summability/Reciprocal.lean` | 298 | 35 (0) | 2 | δ/G₂ summability = mathlib `E2/Transform.lean` block (not yet public there); 1 live decl |
| `Modularforms/clog_arg_lems.lean` | 95 | 8 (1) | 0 | ENTIRELY DEAD; `arg_pow_aux` small ForMathlib |
| `Modularforms/csqrt.lean` | 58 | 5 (0) | 0 | `csqrt` ≈ `Complex.sqrt`; used only by dead eta.lean |
| `Modularforms/equivs.lean` | 47 | 6 (0) | 1 | `Equiv.neg`/`addRight`/`arrowCongr` re-implemented; root-level `swap` |
| `Modularforms/eta.lean` | 82 | 4 (0) | 0 | 1:1 image of mathlib `Discriminant.lean:66–143`; all 4 lemmas unused — REMOVE-FILE |
| `Modularforms/exp_lems.lean` | 30 | 3 (0) | 0 | Alias of `norm_exp_two_pi_I_lt_one` (6 call sites) |
| `Modularforms/iteratedderivs.lean` | 73 | 6 (0) | 0 | All 6 lemmas are mathlib (`iter_deriv_inv_linear`, Cotangent.lean); dead |
| `Modularforms/multipliable_lems.lean` | 82 | 13 (0) | 0 | 5 mathlib wrappers; genuine gap `hasProd_le_nonneg`; 2 live decls |
| `Modularforms/qExpansion_lems.lean` | 114 | 16 (0) | 1 | Γ(n) specialisations of mathlib `qExpansion_*`; global `FunLike (ℍ→ℂ)` instance (delete) |
| `Modularforms/summable_lems.lean` | 17 | 0 (0) | 0 | Compat facade; only importer is `XYin.lean` — replace root line, delete |
| `Modularforms/tsumderivWithin.lean` | 139 | 11 (0) | 0 | `ℍ'` = `upperHalfPlaneSet`; `derivWithin_tsum` re-proved; live only via `ℍ'` |
| `Modularforms/upperhalfplane.lean` | 18 | 2 (0) | 0 | `im_pnat_div_pos` alias; 1 dead |
| `Tactic2/LaurentQExpSimpTests.lean` | 64 | 0 (0) | 0 | Tests of `laurentqExpansion.coeff_*` (misnamed; never uses `qexp_simp`); imported by root |
| `Tactic2/QExpSimpAttr.lean` | 4 | 0 (0) | 0 | `register_simp_attr qexp_simps` |
| `Tactic2/QExpSimpConditionTests.lean` | 56 | 0 (0) | 0 | Sole consumer of `qexp_simp`; imported by root |
| `Tactic2/qexp_simp.lean` | 208 | 27 (0) | 0 | `qexp_simps` simp set + macro; 22/29 lemmas are aliases of mathlib; unused outside its tests |
| `jFunction/Deltaqexpansions.lean` | 301 | 41 (24) | 0 | Integral q-expansions of E₄,E₆,Δ; `E4`=`E₄`=mathlib `ModularForm.E₄` (three names); 8 E4/E6 twin lemmas |
| `jFunction/jInvariantLink.lean` | 82 | 10 (0) | 2 | Bridge PeriodPair → mathlib `WeierstrassCurve.j`; genuinely project-provided; two dead leaves |
| `jFunction/jLevelN.lean` | 194 | 15 (11) | 0 | `jN` = j(Nτ) (second name `levelJ` in Cox); hand-rolled scaling that is `posRealAction` |
| `jFunction/jfunction.lean` | 505 | 67 (29) | 0 | `j`, `qj`, `qjCoeffs`, integrality of j-Laurent coefficients; re-derives a private mathlib lemma (:143–195) |
| `jFunction/qexp_coeffs.lean` | 164 | 24 (6) | 0 | Explicit coefficient values τ(1..3), j-coeffs; documentation-grade (0 external uses); holds the only `qjCoeffs = qjCoeffInt` bridge (private) |
| `qExpansion_tactic/Examples.lean` | 66 | 0 (0) | 0 | Test-only (`#qexp`/`#check`/`example`); imported by library root |
| `qExpansion_tactic/Qj.lean` | 305 | 28 (0) | 0 | Computable coefficient engine (σ_k sums, convolution, inversion) + `#qexp` meta layer used only by Examples |
| `qExpansion_tactic/link.lean` | 409 | 43 (0) | 0 | Soundness of the engine vs analytic q-expansions; 43 root-namespace lemmas; `coeff_invOfUnit_one_succ` upstream candidate |
| `XYin/uniqueness.lean` | 298 | 15 (0) | 0 | Lattice determined by (g₂,g₃) via ℘ Laurent recursion; sorry-free; upstreamable into mathlib `Weierstrass.lean` (TODO there at :938) |

Files with proofs > 30 lines (44 total; collapse plans in step7-api-*.md §5): LaurentQExpansion 2, Algebra 1, uniqueness 1,
Eisenstein 4, Eisensteinqexpansions 1, Delta 1, Summability 0, clog_arg_lems 1, MeromorphicField 0, Cox/ModularFunction 3,
HermiteNormalForm 3, LatticeJ 3, CoxMatrices/Basic 3, CoxMatrices/LaurentExpansion 3, Construction 0, Interpolation 1,
IntegralDescent 1, DiagonalLaurent 1, Arithmetic 3, KroneckerFrobenius 1.

## Part 2: Cross-File Dependencies

Full graph: `inventory-2026-09-25/_import-graph.md` (computed from `import` and `public import` lines — the 26
`Modularforms/` files use the new module system with `module` / `public import`; everything else uses classic imports).
All 84 modules are reachable from the root `XYin.lean`; there are no orphan modules (only the root-level `ScratchGS.lean`,
which is outside the `XYin` lean_lib).

Shape — six layers:
0. `uniqueness`, `HermiteNormalForm`, `IntegralPowerSeries`, `LaurentQExpansion/*`, `Modularforms/Summability/*` and helpers (mathlib only)
1. `Modularforms/{Eisenstein, Delta, E2, eta, …}` → `jFunction/Deltaqexpansions` → `jFunction/jfunction` → `jLevelN` → `qExpansion_tactic/link` → `qexp_coeffs`
2. `ModularFunctions/{MeromorphicField → FieldAction, CuspGrowth → GrowthAtCusp, NormalForm*, CuspPeriod → Cusps}` → `Basic` → `JInvariant` → `Congruence`
3. `Cox/LatticeJ` (imports `uniqueness`, `ModularFunctions/JInvariant`, `Modularforms/ForMathlib_Cusps`) → `Cox/ModularFunction/{CuspData, LevelJ}` → `Cox/ModularFunction` → `CoxMatrices/*` → `UpperHalfPlaneFunctionField` → `FormalCoxProduct`
4. `ModularPolynomial/{AnalyticSupport → Construction → Interpolation, Irreducibility, IntegralDescent}` → `LaurentPolynomialEvaluation` → `DiagonalLaurent` → `SymmetricCubicLaurent`, `Kronecker` → `KroneckerFrobenius` → `LevelThree` (imports `qExpansion_tactic/link`) → `Arithmetic`
5. `CyclicSublattice` → `Classification` → `Arithmetic` → `SingularModuli`, `ModularFunctionField` → umbrella `Section11BC`

Notable edges and hygiene issues:
- `XYin.lean` imports three declaration-free test/example files (`Tactic2/LaurentQExpSimpTests`, `Tactic2/QExpSimpConditionTests`,
  `qExpansion_tactic/Examples`) plus the `summable_lems` facade and the template `Basic`; the single `[[lean_lib]]` has no
  `globs`, so these compile on every build (`Examples.lean` emits 14 info messages and runs native evaluation). → separate `test/` lean_lib.
- The Cox spine reaches `Modularforms/` only through `Deltaqexpansions → Eisenstein` (for `E₄`, `E₆`, `bernoulli'_six`,
  `Delta_q_one_term`) and `LatticeJ → ForMathlib_Cusps`; nothing in Cox depends on the other 24 Modularforms files.
- `Cox/LatticeJ` imports `NormTrace` only for `eq_const_of_weight_zero` (mathlib `levelOne_weight_zero_const` suffices).
- Stray boilerplate imports recur across Modularforms (`CStarAlgebra.*`, `StarOrdered`, `CompletePartialOrder`, `Mathlib.Tactic`);
  `Delta.lean` imports `eta`, `clog_arg_lems`, `NormNumI` without using them; `LevelThree` imports `PowerSeries.Trunc` unused.
- `Cox/ModularPolynomial.lean` (umbrella) does not import `AnalyticSupport` (reachable via `Construction`); its docstring omits it.

## Part 3: Mathlib API Audit (most important)

Reports: `analysis-2026-09-25/step4-analytic.md` (§1 23 replacements, §2 the Γ(1)/𝒮ℒ migration plan, §3 12 re-expressions,
§4 9 hand-rolled families ≈ 1,300 lines, §5 24 verified gaps, §6 9 refuted leads, §7 July status) and
`step4-cox-compute.md` (§1 28 replacements, §2 12 re-expressions, §3 16 patterns, §4 22 gaps, §5 12 refuted).

### 3.1 Definitions to replace with mathlib (grep-verified; **[C]** = scratch-compiled)

| Project (file:line) | Mathlib replacement | Unlocks / notes |
|---|---|---|
| `E₄`, `E₆` (Eisenstein:55/59) and `E4`, `E6` (Deltaqexpansions:36/39) — three names, one object | `ModularForm.E₄`/`E₆` (EisensteinSeries/Basic.lean:51/54) | `E_qExpansion_coeff`, `E_ne_zero`, `E₄_qExpansion_coeff_one`, `discriminant_eq_E₄_cube_sub_E₆_sq`; deletes `Ek_q_exp*`, `E4/E6_ne_zero`, `E4/E6_q_exp_one`, `Delta_E4_E6_aux`. Blocker: `↑Γ(1)` vs `𝒮ℒ` (§3.2) |
| `E` (Eisensteinqexpansions:22) | `ModularForm.E` | `E_k_q_expansion` = `simpa` of `q_expansion_riemannZeta` |
| `Δ` (Delta:26), `Delta` (Delta:170) | `ModularForm.discriminant` / `CuspForm.discriminant` (Discriminant.lean:50/235) **[C]** (`⇑` equal by `rfl`) | +9 wrapper lemmas (:123–258), `divDiscriminant`/`discriminantEquiv` (DimensionFormula:95/63) replace `CuspForm_div_Discriminant` (56 lines) |
| `G₂`, `E₂`, `D₂`, `D2_*` (E2.lean:17–55, :82–84) | `EisensteinSeries.G2/E2/D2`, `D2_one/mul/inv/T/S`, `G2_T_transform`, `E2_slash_action` (E2/Defs.lean, E2/Transform.lean) | keep only `E₂_S_transform` (:87) and `E₂_eq` (:104) |
| `eta.lean` (4 lemmas), `csqrt` (csqrt:22) | `Discriminant.lean:75/94/135`; `Complex.sqrt` (bridge `sqrt_eq_exp`, root namespace) | delete both files (138 lines) |
| `IsCuspForm`, `CuspFormSubmodule`, `cuspFormOfCoeffZero`, `IsCuspForm_iff_coeffZero_eq_zero` (IsCuspForm.lean) | `ModularForm.IsCuspForm`, `cuspFormSubmodule`, `toCuspForm`, `isCuspForm_iff_coeffZero_eq_zero` (CuspFormSubmodule.lean:73/68/127/136) | whole file; `isCuspForm_iff` there is general-Γ |
| `DimensionFormulas.lean` (28 proved decls) | `CuspForm.discriminantEquiv`, `ofMulDiscriminant`, `levelOne_weight_{two,four,six}_rank_*`, `rank_eq_one_add_rank_cuspForm`, `dimension_level_one`, `sturm_bound_levelOne` (LevelOne/DimensionFormula.lean) | only the sorry survives |
| `ℍ'` (tsumderivWithin:30) + 51 literal `{z ∣ 0 < z.im}` | `UpperHalfPlane.upperHalfPlaneSet`, `isOpen_upperHalfPlaneSet` | — |
| `⟨N*z,_⟩` (jLevelN:32/37/92/95), `natScaleUpperHalfPlane` (LevelJ:29, re-inlined CoxMatrices/Basic:725) | `UpperHalfPlane.posRealAction` (`coe_pos_real_smul`, `pos_real_im`) **[C]** | — |
| `negEquiv`, `succEquiv`, `swap_equiv` (equivs.lean) | `Equiv.neg ℤ`, `Equiv.addRight 1`, `Equiv.arrowCongr Fin.revPerm _` **[C]** | root-level `swap` collides with `Function.swap` |
| `BigO.lean` (8), `exp_upperHalfPlane_lt_one`, `pnat_div_upper`, `Multipliable_pow`, `tprod_pow`, `summable_pnats`, … (≈ 40 helper lemmas) | `EisensteinSeries.linear_inv_isBigO_right/left`, `norm_exp_two_pi_I_lt_one`, `im_pnat_div_pos`, `Multipliable.pow`, `summable_pnat_iff_summable_nat`, … (per inventory) | see step8-junk §2 for the file-level list |
| `modular_slash_S_apply`, `slashaction_generators(_SL2Z)`, `SL2Z_generate` (SlashActionAuxil:54/220/260/68) | `SlashInvariantForm.slash_S_apply` (Identities:47) **[C]**, `slash_action_generators` (:54), `slash_action_generators_SL2Z` (LevelOne/Basic:56), `SL2Z_generators.symm` | — |
| `coeToComplexPowerSeries.ringHom` (IntegralPowerSeries:107), `powerSeriesMapAlgHom` (:33) | `PowerSeries.map (algebraMap R ℂ)`, `PowerSeries.mapAlgHom` | 10 external callers unfold it |
| `analyticTaylor` (Algebra:285) | literally the body of `UpperHalfPlane.qExpansion` (QExpansion.lean:166) | keep `analyticTaylor_comp_pow` as a `PowerSeries.expand` statement |
| `sigmaPow` (Qj:47), `foldl/push` tabulations (:65/:75/:97/:117), `convArrayCoeff` fold (:69) | `ArithmeticFunction.sigma` (`#eval` **[C]**), `Array.ofFn` **[C]**, `Finset.sum` over `range` **[C]** | deletes link.lean:30–56, :108–129, :271–279; re-time `decide +kernel` consumers |
| `BivariatePolynomial.eval` (Construction:40, argument order flipped), `specializeY_eval` :70, `diagonal_map` :126, `eval_swap` :88, `diagonal_eval₂` :135, `varX`/`varY` :33/:36 (names inverted) | `Polynomial.evalEval`, `map_evalRingHom_eval` (Bivariate.lean:162), `map_mapRingHom_eval_map` (:172), `aevalAeval_swap` (:286), `eval₂_eval₂RingHom_apply` (:194), notation `Y`/`C X` | two evaluation conventions still coexist (Interpolation:355–446, CuspData:57, ModularFunctionField:38/91 use raw `evalEval`) — standardise on `evalEval` |
| `bivariateLaurentEvalHom` (SymmetricCubicLaurent:111; rebuilt inline LevelThree:643–659) | `(evalEvalRingHom J T).comp (mapRingHom (mapRingHom HahnSeries.C))` = `aevalAeval J T` (needs `open scoped Polynomial.Bivariate`) | — |
| `IsColumnHermiteNormalForm.belowDiagonal_eq_zero` (HNF:37) | `Matrix.BlockTriangular A id` **[C]**; `det_of_upperTriangular` **[C]** | replaces 3 `det_fin_two_of` hacks (CyclicSublattice:312/465, Classification:40) |
| `rankTwoContent` (HNF:44) | `Finset.gcd` (residual `normalize_eq` goal only) | collapses HNF:48–83 and 6 AC-gcd `simpa` sites |
| `dualMatrix` (CyclicSublattice:353) | `Matrix.adjugate` **[C]** (+ `mul_adjugate`, `det_adjugate`) | ≈ 110 lines :356–467 collapse |
| `carrierEquiv` (CyclicSublattice:222–249) | `(Submodule.equivSubtypeMap L.lattice S.carrier).trans (LinearEquiv.ofEq …)` **[C]** (`_apply_coe` by `rfl`) | — |
| 4+1 anonymous `HahnSeries` builds (Kronecker:160/184/300/572, LaurentExpansion:50) | `HahnSeries.ofSuppBddBelow`; deeper: `HahnSeries.embDomain`/`embDomainRingHom` along `k ↦ m·k` **[C]** for `jIntegralLaurentSeriesWidth` and `transformedJSeries ζ (sigmaZero m)` | coefficient lemmas :204–226, :320–328, :339–359, :426–458 become `embDomain_coeff` one-liners |
| `coxPhiAtJ_monic/_natDegree` (Construction:159/165); `eval_derivative_prod_X_sub_C_at` (Interpolation:291) | `Lagrange.nodal_monic`/`natDegree_nodal`; `Lagrange.eval_nodal_derivative_eval_node_eq` (now a 3-line wrapper — inline at :328, :417) | `interpolationAt` deliberately ≠ `Lagrange.interpolate` (coincident CM nodes) — keep |
| `not_isSquare_of_between_sq_aux` (SingularModuli:59–72) | `Nat.not_exists_sq'` (Data/Nat/Sqrt.lean:213), 3 lines after `lift` | — |
| `matrixStar` (CoxMatrices/Basic:154) | `(A.submatrix Fin.rev Fin.rev)ᵀ` **[C]** (not `adjugate`) | `_involutive/_mul/_det` from `transpose_mul`, `submatrix_mul_equiv`, `det_transpose` |
| `act` (CoxMatrices/Basic:80) | `UpperHalfPlane.glAction` (MoebiusAction.lean:188) | collapses `levelJ_smul_eq_j_act_of_normalization` + `complex_mobius_scale_eq_affine` (:699–761) + LevelJ:72–90 + SingularModuli:155–186 to `mul_smul` |
| `matrix_eq_upper_triangular_aux` (LevelJ:203) | `Matrix.eta_fin_two` | — |
| `hasse_qExpansion_principle` (IntegralDescent:145–169), `bivariate_exists_of_coeff_lifts` (:254) | `Polynomial.induction_with_natDegree_le` + `Polynomial.lifts`/`lifts_iff_coeff_lifts` | conclusion is `P ∈ lifts (Int.castRingHom ℂ)` |
| `integerCoeffLaurentSeries` (IntegralDescent:72), `integralLaurentSeries` (FormalCoxProduct:51) | today `(laurentSeriesMapRingHom _).range`; upstream `HahnSeries.coeffSubring` **[C]** | also serves `HasCoeffsIn` |
| `precompAlgEquiv` (UHPFF:136), `precomp_ratFunc` (:128) | `AlgEquiv.ofRingEquiv`, `IsLocalization.ringHom_ext` | — |
| `powerSeries_pow_prime_eq_expand` (Kronecker:282, `change`-defeq on `MvPowerSeries.map_frobenius_expand`) + KF:141 twin; `jUnitLaurentSeriesMod_eq_unitJPowerSeries` (KF:77–96) | one n-general lemma (upstream `PowerSeries.map_frobenius_expand`); `LaurentSeries.single_order_mul_powerSeriesPart` (already used Kronecker:377) | — |
| `conjugate_T_pow_mem_Gamma0` (Congruence:50); `Γ2_reduce_row/col` (SlashActionAuxil) | `Gamma_normal` + `Gamma1_in_Gamma0` (+ 2-line `Gamma N ≤ Gamma1 N`); `Int.bmod` | — |
| `CoxMatrix` / `exists_hnf_transform` vs `FixedDetMatrix.reps` / `reduce` | **not** drop-in (different normal form, no primitivity/uniqueness) | HNF stays BORDERLINE |
| `coxDivisorSum` (Cardinality:113–243) | no Dedekind ψ in mathlib, but `IsMultiplicative.mul`, `pmul`, `prodPrimeFactors_apply` unused | define `dedekindPsi = pmul μ μ * id`; `card_coxMatrix` ℕ-valued; `(Gamma0 m).index = ψ m` **[C]** |
| LevelThree jet machinery (:94–120) | not `PowerSeries.trunc` (noncomputable) — but a duplicate of the project's own `Qj.lean` computable layer | merge; collapse the ≈ 210-line split |

### 3.2 The `↑Γ(1)` vs `𝒮ℒ` convention (the one blocker for the Modularforms cleanup)

`↑Γ(1) = map (mapGL ℝ) (SLMOD 1).ker` and `𝒮ℒ = (mapGL ℝ).range` are propositionally equal (`Gamma_one_coe_eq_SL`,
CongruenceSubgroups.lean:73) but not definitionally: applying `ModularForm.isCuspForm_iff_coeffZero_eq_zero` to
`f : ModularForm Γ(1) k` hits an isDefEq heartbeat timeout **[C]**. There are 68 `Γ(1)` sites (DimensionFormulas 30,
IsCuspForm 9, Delta 9, Eisenstein 4, qExpansion_lems 3, jfunction 3, LatticeJ 2, Deltaqexpansions/link/qexp_simp/
SlashActionAuxil/AnalyticSupport 1 each). Bridges that work **[C]**: generalise-and-`subst` (the DimensionFormulas:34
pattern); `ModularForm.mcast rfl ModularForm.E₄ Gamma_one_coe_eq_SL : ModularForm Γ(1) 4` is `rfl`-equal to `E₄` as a
function; `IsCuspForm (mcast ..) ↔ IsCuspForm f` in 6 lines; `(CuspForm.discriminant : ℍ→ℂ) = ModularForm.discriminant` by `rfl`.

Migration plan (six steps, ≈ 1,450 lines deleted, each step builds green):
1. `Eisensteinqexpansions` 155 → 0 (inline `standardcongruencecondition`; `E` → `ModularForm.E`).
2. `Eisenstein` 692 → ≈ 210 (delete `E₄`/`E₆`; `Delta_E4_E6_aux := CuspForm.discriminant` facts; keep B₆, E₂ boundedness, imag-axis reality).
3. `Delta.lean` 408 → ≈ 20 (`Δ`/`Delta` → `ModularForm.discriminant`/`CuspForm.discriminant`; retarget jfunction 34, Qj 11, Deltaqexpansions 7, link 5, LatticeJ 4, qexp_coeffs 4 sites).
4. `IsCuspForm.lean` 152 → 0 (Eisenstein:329/422 → `toCuspForm`/`isCuspForm_iff_coeffZero_eq_zero`; LatticeJ:556–575 → `CuspForm 𝒮ℒ 0` + `levelOne_weight_zero_const`).
5. `DimensionFormulas` 200 → ≈ 15 (only the sorry survives, restated with `[Γ.FiniteIndex]`).
6. Mechanical `Γ(1)` → `𝒮ℒ`, `mem_Gamma_one` → `⟨γ, rfl⟩`, `(by simp)` → `one_mem_strictPeriods_SL` in qExpansion_lems, jfunction:67/279/419, link:400, LatticeJ, AnalyticSupport:86.
The Cox spine is touched only via LatticeJ; `ModularPolynomial/*` is unaffected except AnalyticSupport:86.

### 3.3 API-choice improvements (definitions kept, re-expressed)

- `poleOrder` (LaurentQExpansion:236, `if … natAbs … untopD … else 0`): make the closed form `Int.toNat (-(…).untopD 0)` (:261) the definition — removes 3 normalisation lemmas and an `unfold` proof. `laurentqExpansion` (:326) is `single_order_mul_powerSeriesPart` in shape; `poleOrder_to_order`/`to_qExpansion_eq_powerSeriesPart` collapse via `HahnSeries.order_single_mul_of_isRegular`. Parametrise by the shift `N` (`shiftedLaurent`) so ring laws need no common-shift arithmetic. (Refuted: "`ofPowerSeries` vs `↑` blocks simp" — same term **[C]**.)
- `IsOfExponentialGrowth` (CuspGrowth:26) → `∃ ρ ≥ 0, f =O[atImInfty] fun τ ↦ exp (ρ * τ.im)` **[C]** (12 lines); `.slash/.mul/.add` become one-liners; kills the `∃ M A, ∀ τ, A ≤ im τ → …` unpacking at CuspGrowth:96, GrowthAtCusp:36, NormalFormGrowth:43; `.slash` generalises to weight k as in `BoundedAtCusp.lean:35`.
- `ModularFunction.meromorphic'` (Basic:33, `∃ a, toFun a = f`) → the predicate `MeromorphicNFOn (f ∘ ofComplex) ℍₒ`; removes `choose` in `toMeromorphicField`.
- `holomorphicFunctions` (FieldAction:26) `Subring` → `Subalgebra ℂ` (`Algebra ℂ HolomorphicFunction` currently fails to synthesize **[C]**); then `evalJ = Polynomial.aeval jElement` and `constant` disappears.
- `Algebra R (Filter.Germ l A)` (missing in mathlib) would make `germRing` a `Subalgebra` and delete `constRingHom`/`instAlgebra` (MeromorphicField:427–448).
- `ResToImagAxis` (ResToImagAxis:32) → `fun t ↦ F (ofComplex (I*t))`: kills 9 unfoldings; two names for one function (:32/:38).
- `CuspData` (CuspData.lean) anonymous 3-conjunction → structure (`.1/.2.1/.2.2` at 24 sites); `CoxMatrix` gets `@[ext]`, `ofColumnHNF`, `_a/_b/_d` simp; `jIntCoeff` gets an explicit witness (`qjCoeffs (n+1).toNat`); one `jLaurentSeriesWidth R m` **[C]** replaces `jIntegralLaurentSeries`, `jIntegralLaurentSeriesWidth`, `jUnitLaurentSeriesMod`, `jLaurentSeriesMod`, `unitJPowerSeries`, `qjIntegralPowerSeriesThree`; `reindex` as a `(ZMod m)ˣ`-action; `toCoxMatrix` term-mode; `theorem_11_18_i/ii` are 0-line aliases with no consumer.
- `HasCoeffsIn` (IntegralPowerSeries:51) is the seed of a missing `PowerSeries.lifts` — keep, collapse the middle abbrev layer (:107–145, 0 external users).
- Global instances to delete: `FunLike (ℍ → ℂ) ℍ ℂ` (qExpansion_lems:73; mathlib deliberately has none; leaks through `public section`; zero users) and `SMul ℕ+ ℍ` (Delta:81; unbridged duplicate of `posRealAction`, zero users). Global `Fact` instances for `upperHalfPlaneSet` (MeromorphicField:581–588) should be local.

### 3.4 Hand-rolled patterns to replace (verified; ≈ 1,300 lines analytic + ≈ 500 Cox)

| Pattern | Sites | Mathlib / helper | Lines |
|---|---|---|---|
| summability majorants for `Σ n^k q^n` | Eisenstein:211/491/563/613, Summability/Basic:107/185/138/194 | `summable_pow_mul_cexp` (EisensteinSeries/QExpansion:192), `summable_norm_pow_mul_geometric_div_one_sub` | ≈ 90 |
| differentiation under `tsum`, iterated derivatives of `cexp` sums, cot identities | Summability/QExpansion:27–271, iteratedderivs, tsumderivWithin | `EisensteinSeries.qExpansion_identity_pnat`, `iteratedDerivWithin_tsum_cexp_eq`, `TsumUniformlyOn.derivWithin_tsum`, Cotangent.lean | ≈ 370 (all dead) |
| explicit compact majorants `∃ u, Summable u ∧ ∀ n s, ‖…‖ ≤ u n` | aut_bound_on_comp, iter_deriv_comp_bound2/3 | `SummableLocallyUniformlyOn_of_locally_bounded` | ≈ 230 |
| bounded-at-cusps via two `IsBigO`s | Delta:234–270 | `isBigO_iff_div_isBoundedUnder` + `exp_decay_isBigO_discriminant` | 3 lines |
| "term real ⇒ `im (∑')` = 0" | Eisenstein:482/549, Delta:339 | `Complex.im_tsum_eq_zero_of_forall` **[C]** (2 lines) | ≈ 40 |
| ring-closure inductions for `laurentqExpansion` | LaurentQExpansion:118–143, Algebra:163–281 | bundle as a `RingHom` from the meromorphic-cusp subring (cf. `qExpansionRingHom`) | ≈ 130 |
| private mathlib lemma re-derived | jfunction:143–195 | publicise `hasFPowerSeriesOnBall_update` (QExpansion.lean:239) | ≈ 50 |
| `=ᶠ[𝓝[≠]0]` cusp-function skeleton | CuspData:86/125, ModularFunction:63, LaurentQExpansion:68/79/90, Algebra:55 | `cuspFunction_eventuallyEq_comp` + `cuspFunction_comp₂_eventuallyEq` **[C]** | ≈ 85 |
| Hahn-series order computation (`orderTop_eq_of_le` + `by_contra` + …) | DiagonalLaurent:257/65, Kronecker:263/339 | `le_antisymm (order_le_of_coeff_ne_zero _) ((le_order_iff_forall _).2 _)` **[C]** | ≈ 40 |
| `coeff (single (-N) 1 * ↑(expand N F)) k` case split | KF:104–139, Kronecker:389–458, LevelThree:577–600/609–635 | `LaurentSeries.coeff_single_neg_mul_coe_expand` (statement typechecked) | ≈ 100 |
| entrywise 2×2 `fin_cases` | CoxMatrices/Basic ×10 | `Matrix.mul_fin_two` | ≈ 40 |
| left-SL₂ triangularisation | LevelJ:159–257, HNF:123, CoxMatrices/Basic:343 | one public `Matrix.exists_SL2_inv_mul_eq_upperTriangular` | ≈ 100 |
| `Polynomial.induction_on'` width-1/width-m skeletons | IntegralDescent:25–70 ≡ DiagonalLaurent:31–55/152–185/219–224, LevelThree:715 | `laurentqExpansion_polynomialIn` / `_pow` | ≈ 60 |
| SL₂ cancellation chains, gcd re-association, `Units.mk0 (m:ℂ)`, `∃ z : ℤ, coeff = z`, `CuspData` projections | ×4, ×7, ×8, ×6, ×24 | `SpecialLinearGroup.mul_coe_mul_coe_inv` **[C]**, `CoxMatrix.coprime_gcd_b` **[C]**, public `indexUnit`, subring membership, `CuspData.apply_smul` **[C]** | ≈ 120 |

### 3.5 Verified genuine gaps → see Part 8 (triage) — 24 analytic + 22 algebraic.

### 3.6 Refuted leads (do not act on these)
`ofPowerSeries` vs `↑` coercion (same term); `Complex.sqrt_eq_exp` (it is root-namespace `sqrt_eq_exp`); `bernoulli'_five`
(= `bernoulli'_eq_zero_of_odd`); `bernoulli'_six` (mathlib idiom is `decide +kernel`); `Complex.ofReal_tprod`
(= `Multipliable.map_tprod`); `SMul ℕ+ ℍ` is a hygiene issue, not a defeq diamond; `matrixStar ≠ adjugate`;
`interpolationAt ≠ Lagrange.interpolate`; LevelThree jets ≠ `PowerSeries.trunc`; the KF-inventory identity
`jLaurentSeriesMod p = transformedJSeries 1 (sigmaZero p)` is **false** (width p vs p², **[C]**); "`Fact (Nat.Prime p)`
unused" at KF:26/104 (needed by the statement until `Field K` is weakened); "bidegree ≤ n is a parameter change" (it is not).

## Part 4: Moral Duplications

Report: `analysis-2026-09-25/step5-duplications.md` (1,462 lines: method, seven cluster tables with the mandatory 9-column
pairwise table — 214 rows, deletion-grade rows first — July-table status, counts, top 10, 77 helpers, 34 verification notes,
evidence appendix; source data in the session scratchpad `step5/{rows1-7.json, helpers.json}`).

Method: seven cluster finders (Modularforms analytic · Laurent/j/integral · Cox HNF-lattice-matrices · Cox modular polynomial ·
Kronecker/LevelThree/LPE · ModularFunctions/Cox fields · July-table re-check) opened every candidate pair in the source and rated
statement, proof skeleton and hypotheses. The 45 deletion-grade rows (DELETE-ONE / UNIFY / REPLACE-WITH-MATHLIB / PUBLICIZE, by
lines saved) were each handed to an adversarial verifier instructed to refute: 34 confirmed, 11 refuted and re-rated (the refutation
note stays in the Action column). One confirmed REPLACE-WITH-MATHLIB (`constant`/`evalJ`) was downgraded to DERIVE by its verifier.

| Verdict | Rows (all / cluster tables / July re-check) | Meaning |
|---|---|---|
| DELETE-ONE | 22 / 18 / 4 | identical; delete one, retarget callers |
| REPLACE-WITH-MATHLIB | 12 / 12 / 0 | both are one mathlib lemma (grep-verified path) |
| UNIFY | 28 / 26 / 2 | one parametric lemma replaces both |
| DERIVE | 27 / 25 / 2 | keep the general one, derive the special case |
| PUBLICIZE | 22 / 17 / 5 | private original re-proved elsewhere |
| EXTRACT-HELPER | 60 / 56 / 4 | same skeleton; shared helper named with its statement |
| DISTINCT | 43 / 25 / 18 | looked alike, is not (reason recorded) |

Estimated lines saved over the 171 non-DISTINCT rows: 2,303 gross (2,114 in the cluster tables; the July rows overlap), realistically
≈ 1,700–2,100 net. July 2026 table (35 rows): 16 DONE, 18 STILL OPEN (4 of them kept as DISTINCT), 1 no longer applicable.

Top 10 actions by lines saved (row numbers refer to the report):
1. **LevelThree jet split** (row 124, UNIFY, confirmed, ≈ 170): the 35 private `explicitCandidateClearedJetThree_*` lemmas (LevelThree.lean:349–502) → one `decide +kernel` over the 10-index `Finset`.
2. **`LaurentSeries.substMonomial` + one q-parameter bridge** (row 141, EXTRACT-HELPER, ≈ 100): the `coxPhaseAux … laurentqExpansion_coxAction_coeff_aux` chain (CoxMatrices/LaurentExpansion) vs `laurentqExpansion_nat_mul_coeff` (Algebra) — design ticket, not compiled.
3. **`Matrix.exists_SL2_mul_eq_upperTriangular`** (row 75, EXTRACT-HELPER, ≈ 76): LevelJ:159–257 left-triangularisation vs HNF:123 / CoxMatrices/Basic:343 → one lemma in HermiteNormalForm.lean.
4. **`LaurentSeries.coeff_single_neg_mul_coe_expand`** (row 142, EXTRACT-HELPER, ≈ 66): `transformedJSeries_one_sigmaZero_eq_expand` + Kronecker:389–458 + LevelThree:577–636.
5. **`jLaurentSeriesWidth R m`** (row 125, UNIFY, confirmed, ≈ 45): `jIntegralLaurentSeries` / `…Width` / `jUnitLaurentSeriesMod` / `jLaurentSeriesMod`.
6. **`CoxMatrix.ofColumnHNF`** (row 70, PUBLICIZE, confirmed, ≈ 40): `toCoxMatrix` (Classification) ≡ private `exists_coxMatrix_of_isColumnHermiteNormalForm_aux` (CoxMatrices/Basic).
7. **`LevelOneCuspData.of_widthM`** (row 110, EXTRACT-HELPER, ≈ 40): `coxPhiFunction_coeff_{widthOne,modularFunction,polynomialInJ}` (Construction) ≡ the Interpolation pipeline.
8. `widthLaurentSeriesThree_eq_integral` ≡ `sigmaLaurentSeriesThree_map_complex` (row 133, DERIVE, ≈ 39): two-liners once 4 and 5 exist.
9. **`HermiteNormalForm.ofToLin` + `Matrix.toLin_injective_of_det_ne_zero`** (row 76, EXTRACT-HELPER, ≈ 38): `dualBasis` / `dual_repr_*` / `dualToMatrix_eq` / `dual_index_eq` (CyclicSublattice).
10. `deltaShiftedQSeries_analyticAt_aux` = mathlib's private `hasFPowerSeriesOnBall_update` (row 42, PUBLICIZE, confirmed, ≈ 35; the removable-singularity rewrite compiled) — tie with `jUnitLaurentSeriesMod_order` / `jLaurentSeriesMod_order` (row 126, UNIFY, confirmed, ≈ 35).

Shared helpers to extract (77 after merging 5 duplicate proposals; 21 scratch-verified; statements and home files in the report §6):
- **Modularforms (live parts)**: `bound_of_mem_verticalStrip`, `Summable.pnat_of_int` / `neg_pnat_of_int`, `Complex.im_tsum_eq_zero_of_forall`, `ResToImagAxis.real_iff`, `norm_exp_two_pi_I_pnat_mul_lt_one`, `ModularForm.tendsto_atImInfty_coeff_zero`, `Matrix.SpecialLinearGroup.zpow_val_of_step`, `eventually_clog_pow`, `SlashInvariantForm.S_smul_eq`, `Gamma_natCast_mem_strictPeriods`.
- **IntegralPowerSeries / jFunction**: `coeff_mapAlgHom_ofId_int` (+ `coeff_coeToComplex_int`, `coeff_powerSeriesMapAlgHom`), `IntegralPowerSeries.coeff_toIntegralPowerSeries_cast`, `IntegralPowerSeries.mapAlgHom_ofId_toIntegralPowerSeries`, `ModularForm.qExpansion_coe_pow` (+ `E4_pow_three_qExpansion`, `E6_pow_two_qExpansion`), `UpperHalfPlane.periodic_comp_ofComplex_of_vadd`, `UpperHalfPlane.natScale` (+ `coe_natScale`).
- **LaurentQExpansion**: `norm_lt_one_mem_nhdsNE_zero` + `eventually_ne_zero_and_norm_lt_one`, `cuspFunction_eventuallyEq_comp` + `cuspFunction_comp₂_eventuallyEq`, `cuspFunction_qpow_mul_eventuallyEq_nhdsNE`, `poleRemoved_of_poleOrder_eq_zero`, `PowerSeries.hasSum_coeff_expand_mul_pow`, `cuspMeromorphicSubring`, `invStep` (Qj.lean), `poleOrder_eq_iff`, `laurentqExpansion_pow`, `meromorphicAt_cuspFunction_polynomial_eval`, `laurentqExpansion_polynomial_eval`, `LaurentSeries.substMonomial` + `laurentqExpansion_comp_of_qParam_eq`.
- **Cox HNF / matrices**: `Matrix.exists_SL2_mul_eq_upperTriangular`, the `IsColumnHermiteNormalForm` accessor family (`one_zero … rankTwoContent_eq`), `HermiteNormalForm.diag_mul_eq_index`, `Matrix.rankTwoContent_fin_two_upper` (+ `rankTwoContent_matrixStar`), `CoxMatrix.ofColumnHNF` (+ `inclusionMatrix_ofColumnHNF`), `IsColumnHermiteNormalForm.eq_of_mul_isUnit_det` (+ `Int.eq_of_mem_Ico_of_eq_add_mul`), `Matrix.toMatrix_rangeBasis_subtype` / `HermiteNormalForm.ofToLin` / `Matrix.toLin_injective_of_det_ne_zero`, `CoxMatrix.ext`, `CoxMatrix.d_dvd/a_dvd/div_d/div_a`, `inv_smul_natScale_smul_eq_affine` (publicised), `PeriodPair.homothetic_of_pow_eq`, `indexUnit` (publicised) + `CoxMatrix.dUnit`, `SpecialLinearGroup.mul_coe_mul_coe_inv` / `coe_mul_coe_inv_mul`, `coprime_gcd_iff_primitive`, `determinantScale_mul_eq`, `CoxMatrix.coe_act_eq_of_sl2_mul_eq`.
- **Modular polynomial**: `slash_zero_eq_iff_forall_smul`, `coxNodal_coeff_cuspMeromorphicAt` / `_mdifferentiable`, `LevelOneCuspData.of_widthM`, `rightCosetEval_mdifferentiable` / `coxRoot_mdifferentiable`, `Polynomial.coeff_finset_prod_mem`, `Polynomial.coeff_X_sub_C_mem`, `rightCosetTranslate_cuspMeromorphicAt`, `meromorphicAt_cuspFunction_one_of_widthM_of_slashInvariant`, `modularPolynomial_map_complex_swap` (+ `BivariatePolynomial.map_neg`), `modularPolynomialC_eval_eq_zero_iff` (+ `_eval_act_j`, `formalCoxPolynomial_eval_transformedJSeries`).
- **Kronecker / LevelThree / LPE**: `jLaurentSeriesWidth`, `jLaurentSeriesWidth_coeff_mul` (+ `_coeff_of_not_dvd`), `LaurentSeries.coeff_single_neg_mul_coe_expand`, `HahnSeries.order_eq_of_coeff_ne_zero_of_forall_lt`, `HahnSeries.leadingCoeff_pow`, `LaurentSeries.coeffMemSubring`, `PowerSeries.pow_prime_pow_eq_expand`, `polynomial_eval₂_laurentSeries_coeff_eq_zero_of_lt` (+ `_leadingCoeff`), `formalCoxPolynomial_map_coeff_coeff`.
- **ModularFunctions / Cox fields**: `ModularForm.SL_slash_zero_eq`, `CuspData.apply_smul` / `LevelOneCuspData.slash_sl2`, `OnePoint.isOfExponentialGrowthAt_of_forall_sl2`, `ModularFunction.ofLevelOneHolomorphic`, `UpperHalfPlane.periodic_comp_ofComplex_of_slashInvariant`, `MDifferentiable.meromorphicNFOn_comp_ofComplex` / `ModularFunction.ofGamma0Holomorphic`, `UpperHalfPlane.sl2_det_pos`, `rightCosetEval/rightCosetFunction/rightCosetRoot_baseRightCoset`, `evaluation_comp_evalJ`, `HolomorphicFunction.ext`, `LevelOneCuspData.periodic_comp_ofComplex` / `meromorphicAt_cuspFunction`, `ModularFunction.toMeromorphicField_eq_algebraMap_of_coe`, `MeromorphicField.precomp_algebraMap_eq_of_forall`, `exists_positive_nonsquare_det_aux`.
- **Refuted / merged proposals** (do not act): `laurentqExpansionRingHom` (refuted with row 46 — the seven ring laws are not a single ring hom on one subring without the common-shift bookkeeping), `Cox.natScaleUpperHalfPlane` via `posRealAction` (superseded by `UpperHalfPlane.natScale`), `polynomial_prod_coeff_closure` / `X_sub_C_coeff_closure` (subsumed by the `Subsemiring`/`Subring` versions), `cuspFunction_map₂_eventuallyEq` (same as `cuspFunction_comp₂_eventuallyEq`).

## Part 5: Generalization Opportunities

Report: `analysis-2026-09-25/step6-generalization.md` (41 findings: 22 Low, 6 Low–Medium, 9 Medium, 4 High; 8 refuted; July
carry-over: 2 DONE, 22 still open, 4 refutations confirmed; literature cited per item). Highlights:

| # | Item | Current → target; evidence | Difficulty |
|---|---|---|---|
| G-1 | `[Field K]` in LaurentPolynomialEvaluation:94–140, SymmetricCubicLaurent (26 sites), DiagonalLaurent:57/66/81 | `[CommSemiring K] [NoZeroDivisors K]` / `[CommRing K] [IsDomain K]` **[C]** for LPE:93/103/113/139; only `order_pow/order_mul/leadingCoeff_mul` used — FormalCoxProduct/DiagonalLaurent need `DivisionRing` only because `transformedJSeries` uses `zpow` — phase-as-hom redesign | Low / Medium |
| G-2/3 | `[CharZero K]` dead at FormalCoxProduct:51/75/92; `Fact (Nat.Prime p)` droppable only at KF:77, Kronecker:263 | — | Low |
| G-24 | rank-2 HNF → rank-n over Bézout/PID | correct cyclic criterion is D_{n−1}(A)=1 (gcd of (n−1)-minors); `rankTwoContent` = D₁ only at n=2; naive entry-gcd criterion FALSE for n≥3 (`diag(1,2,2)`) | docstring now (Low); rank-n High, upstream-first |
| G-26 | `symmetric_bidegree_three_eq_zero_of_laurent_coeff` | generic version needs triangle `T_n`, weights `a·i+b·j`, explicit injectivity hypothesis (at level 3 it holds only because `j ≤ i` excludes 9·1 = 3·3) | High |
| G-27/28 | Cardinality:113–243 | Dedekind ψ = `pmul μ μ * id` as `ArithmeticFunction`; `card_coxMatrix` ℕ-valued | Medium / Low |
| G-22/23 | CyclicSublattice:24–157, Classification:28–175 | any `(M, bM : Basis (Fin 2) ℤ M)`; ℂ first used at CyclicSublattice:60/107, Classification:178 | Medium |
| G-18 | `laurentqExpansion_nat_mul_coeff(_of_not_dvd)` (Algebra:384/419) | `HahnSeries.embDomainRingHom (zmultiplesHom ℤ m)` + `embDomain_coeff`; same packaging retires Kronecker:160/184/300/572, KF:104, LaurentExpansion:50 | Low–Medium |
| G-20 | `HasCoeffsIn`, `integralLaurentSeries`, `integerCoeffLaurentSeries` | `PowerSeries.lifts` + `HahnSeries.coeffSubring` | Medium, upstream-first |
| G-25 | Irreducibility:89/102 | drop `minpoly` (contrapositive of `eq_zero_of_natDegree_lt_card_of_eval_eq_zero`); conclude `p = minpoly F α` | Low, upstream |
| G-13/14/15 | Cox/ModularFunction:96/294, NormalFormSlash:22/54 | `𝕜 → E`; weight k via `meromorphicNFAt_mul_iff_left` | Low, upstream |
| G-16 | `IsOfExponentialGrowth`, `GrowthAtCusp.slash` | `IsBigO` form; weight k exactly as `IsBoundedAtImInfty.slash` | Low |
| G-29 | the sorry `dim_gen_cong_levels` | restate with `[Γ.FiniteIndex]` (≡ `IsArithmetic`; instances for Γ(N), Γ₀(N), Γ₁(N)); proof route `ModularForm.norm` → `sturm_bound_levelOne` | restate Low, proof High |
| G-30 | `IsImaginaryQuadratic` | ⇔ `(minpoly ℚ τ).natDegree = 2` ⇔ `IsQuadraticExtension ℚ ℚ⟮τ⟯` | Medium |
| G-19 | `analyticTaylor_comp_pow` | `HasFPowerSeriesAt G p 0 → HasFPowerSeriesAt (G∘(·^m)) (ofScalars (expand m …)) 0` over any 𝕜 | Medium |
| G-9/10, G-7/8, G-11, G-31 | Interpolation:351/301 (any field / `Finset`), Arithmetic:239 (`CommSemiring`) / :164 (`R[X]`), uniqueness:140 (`𝕜`, `ContDiffAt`), 11.9(i) as `gamma0ModularFunctionField 1 = ⊥` | — | Low |
| G-37 | Laurent expansion of a meromorphic germ (July B2) | restate on `meromorphicOrderAt_eq_int_iff`, `MeromorphicNFAt`; circle-integral subtree now dead | High, upstream-first |

Refuted (8): uniqueness beyond ℂ; `meromorphicAt_of_comp_pow` beyond ℂ (codomain → Banach is fine); ℤ compute layer → CommRing;
`primeFinEquivCoxMatrix` beyond primes; KF "Fact unused"; `transformedJSeries` → CommRing for free; bidegree parameter change; canonical HNF over a bare PID.

## Part 6: API Improvements

Reports: `step7-api-analytic.md` (44 missing lemmas, 11 thin-simp definitions with 66 manual unfold sites, 9 instance verdicts,
12 completeness gaps, 22 long proofs, 24 naming items; 4 scratch compiles) and `step7-api-cox.md` (40 missing lemmas L1–L40,
of which 20 compiled or statement-typechecked; 25 definitions' simp status; 20 long proofs; naming).

### 6.1 Missing lemmas — top 12 analytic (statements in step7-api-analytic §1)
1. **Transport family** `cuspFunction_eventuallyEq_comp : cuspFunction h f =ᶠ[𝓝[≠]0] f ∘ ofComplex ∘ invQParam h`, `cuspFunction_comp/comp₂_eventuallyEq` **[C]** — 13 sites, ≈ 85 lines, deletes 4 privates; all future closures (`meromorphicAt_cuspFunction_{neg,sub,pow,inv,smul,polynomialIn}` **[C]** 1–4 lines each, `poleOrder_{add_le,mul,pow,neg}`) become free. Home: LaurentQExpansion.lean top.
2. **`LaurentSeries.substMonomial c r F` + `laurentqExpansion_comp_of_qParam_eq`** (`(∀ τ, qParam h' (φ τ) = c * qParam h τ ^ r) → laurentqExpansion h (f ∘ φ) = substMonomial c r (laurentqExpansion h' f)`) — subsumes Algebra:343–439, LaurentQExpansion:46–66/147–159/275–312, CoxMatrices/LaurentExpansion:93–300 (≈ 210 net lines; Cox eq. 11.13 becomes `rw [bridge]; ext; simp`).
3. **`laurentqExpansion_polynomialIn (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0) (P : ℂ[X]) : laurentqExpansion h (polynomialIn P f) = P.eval₂ HahnSeries.C (laurentqExpansion h f)`** + `_pow` + `meromorphicAt_cuspFunction_polynomialIn` — deletes the IntegralDescent ≡ DiagonalLaurent inductions (≈ 55 lines, 4 privates). Home: Algebra.lean.
4. **`LevelOneCuspData.of_widthM`** (`MeromorphicAt (f∘ofComplex)` on ℍ + SL₂-invariance + `MeromorphicAt (cuspFunction m f) 0 → LevelOneCuspData f`) + `ModularFunction.ofGamma0Holomorphic/ofSL2ZHolomorphic` — the A15 pipeline in Construction/Interpolation/LevelJ/JInvariant (≈ 80 lines, 9 privates).
5. **Canonical `jIntCoeff`**: explicit witness, `jIntCoeff_of_lt_neg_one` (drops the `-(a²) ≤ k` clause at LaurentExpansion:52/69), publish the two private bridges `qjCoeffs = qjCoeffInt` (qexp_coeffs:46) and `jIntCoeff (n-1) = qjCoeffInt n` (LevelThree:122) (5 re-proofs).
6. **`CuspData` structure + `CuspData.apply_smul` / `SL_slash_zero_eq_iff`** **[C]** + closure set (`neg/sub` 6 lines each) — 24 projection sites, 15 slash-idiom sites.
7. **IntegralPowerSeries cast lemmas** `coeff_toIntegralPowerSeries_cast` (×6 re-proofs), `hasCoeffsIn_pow/_X/_algebraMap/_finset_sum`, `coeff_mapAlgHom_ofId` (×3 in link.lean) — 13 sites, ≈ 35 lines.
8. **`tendsto_atImInfty_of_analyticAt_cuspFunction`** family (`ModularFormClass.tendsto_atImInfty (𝓝 (coeff 0))`) — 4 sites (LatticeJ:593, IsCuspForm:113, …); mathlib gap.
9. **`toFun_precomp`** (`toFun (precomp δ a) = fun τ ↦ toFun a (δ • τ)`, = `meromorphicNFOn_slash_zero` + `eqOn_toNF_of_meromorphicNFOn`), `IsOfExponentialGrowth.{add,mul,neg,const,smul,mono}`, `isOfExponentialGrowthAt_of_forall_SL2Z`, and **ring/field operations on `ModularFunction Γ`** — unlocks the subfield form of 11.9(ii).
10. **Order lemmas** `analyticOrderAt_const_mul_pow`, `meromorphicOrderAt_comp_const_mul_pow`, trailing-coefficient versions — 5 sites, ≈ 50 lines (Cox/ModularFunction:174–188, LaurentExpansion:151–160).
11. **`laurentqExpansion_nat_mul` as `HahnSeries.embDomain`** **[C]** (8 lines) + public `qExpansion_const`/`qExpansion_qParam_pow` + `poleRemoved_of_poleOrder_eq_zero` **[C]** / `coeff_of_geq'` **[C]** — ≈ 40 lines, 12 test-file sites.
12. **Simp families**: `poleRemoved_apply`, `coeff_neg_poleOrder_add`, `resToImagAxis_of_pos`, `polynomialIn_apply`, `qj_apply`, `levelJ_apply`, `periodPair_ω₁/ω₂`, `precomp_one/_mul` — 66 manual unfold sites; plus `PeriodPair.smul_lattice_eq_span` (≈ 35 lines) and `SlashInvariantForm.S_smul_eq` **[C]** (4 sites).

### 6.2 Missing lemmas — top 12 Cox (statements in step7-api-cox §1; **[C]** = compiled, **[T]** = statement typechecked)
1. **L19+L20** `LaurentSeries.coeff_single_neg_mul_coe_expand` **[T]** + `Cox.jLaurentSeriesWidth R m` **[C]** (+ the *correct* `transformedJSeries_sigmaZero` identity) — ≈ 340 lines across Kronecker/KF/LevelThree.
2. **L39** LevelThree: one `decide +kernel` for all ten coefficients + a `TriangularCoeffsVanish` predicate — ≈ 220 lines.
3. **L21** `LaurentSeries.substMonomial` **[T]** + analytic bridge — ≈ 60 algebraic + 180 analytic lines.
4. **L28** `LevelOneCuspData.of_widthM` + `Polynomial.prod_X_sub_C_coeff_mem` — ≈ 130 lines (A15 ×2–3).
5. **L1+L2+L3** `Matrix.exists_SL2_inv_mul_eq_upperTriangular` public; publicise `rankTwoContent_dvd_mul_left`, `columnHNF_eq_of_mul`, `exists_sl_right_mul_isColumnHermiteNormalForm_aux` into HNF.lean; `matrix_eq` ≡ `columnHNF_eq_of_mul` dedupe — ≈ 150 lines.
6. **L12** `CoxMatrix.act_eq_sl2_smul_of_mul` **[T]** (generic `act (γ·M) = γ • act M`) — ≈ 80 lines (3 Möbius `field_simp` copies).
7. **L18** `laurentqExpansion_polynomialIn/_pow` (analytic) — ≈ 60 lines.
8. **L24** `HahnSeries.coeffSubring` **[C]** + `HahnSeries.mapRingHom` **[C]** + `laurentSeriesMapRingHom_apply` — ≈ 50 lines, 2 subrings + 2 homs.
9. **L10 + L4/L5/L6** `CoxMatrix.ofColumnHNF` + `_a/_b/_d`; `isColumnHermiteNormalForm_fin_two_iff` **[C]**; `IsColumnHermiteNormalForm.det_eq/det_pos` **[C]**; `rankTwoContent_fin_two_of` **[C]** — ≈ 90 lines over 3 construction copies + 7 field-extraction quadruples + 5 `det_fin_two` hacks + 11 gcd idioms.
10. **L22+L23** `HahnSeries.order_eq_of_coeff_ne_zero_of_forall_lt` **[C]** (2 lines) + LPE siblings `polynomial_eval₂_laurentSeries_{coeff_eq_zero_of_lt,order,leadingCoeff}` + `HahnSeries.leadingCoeff_pow` **[C]** — ≈ 85 lines; 3 PR candidates.
11. **L25+L26** `BivariatePolynomial.map` as a ring hom (`map_neg/map_sub` free), `modularPolynomial_map_complex_swap`, `modularPolynomialC_swap`, `modularPolynomialC_eval_act_j σ τ = 0` (×3 replay) — ≈ 45 lines; supplies the missing named ℂ-symmetry theorem.
12. **L8+L9+L7+L14+L40** `CoxMatrix.ext` `@[ext]` **[C]**, `d_dvd/a_dvd/div_d` **[C]**, `coprime_gcd_b` **[C]**, `SpecialLinearGroup.mul_coe_mul_coe_inv` **[C]**, `zeta_ne_zero` — ≈ 50 lines over 26 sites.
Also: L15 `(Gamma0 m).index = Fintype.card (CoxMatrix m)` **[C]** (5 lines) + L16 ℕ-valued `card_coxMatrix`/`dedekindPsi`; L29 `HolomorphicFunction.ext` **[C]** (6 `Subtype.ext; funext` sites), `evaluation_comp_evalJ` (×2); L31 public `indexUnit`/`CoxMatrix.dUnit` (`Units.mk0` ×8); L32 integrality as subring membership (×6); L33 `PeriodPair.smul_lattice_eq_span` (Classification:261–278 → 2 rewrites); L34 `Matrix.toLin_injective_of_det_ne_zero`; L35–L37 SingularModuli (`IsImaginaryQuadratic` ⇔ `minpoly` degree 2, one `exists_positive_nonsquare_det` lemma, `Nat.not_isSquare_of_lt_of_lt`).

### 6.3 Missing instances / structure (verdicts)
- **Delete**: global `FunLike (ℍ → ℂ) ℍ ℂ` (qExpansion_lems:73), global `SMul ℕ+ ℍ` (Delta:81). **Localise**: `Fact` instances MeromorphicField:581–588.
- **Add**: `Subalgebra ℂ` for `holomorphicFunctions` (FieldAction:26); `Algebra R (Filter.Germ l A)` (upstream); `Zero/One/Add/Mul/Neg/Inv` + a `ModularFunctionClass` on `ModularFunction Γ` (needed for 11.9(ii) as a subfield); `MulAction SL(2,ℤ)` for `precomp` (+ `precomp_one/_mul`); `IsDomain` via `Function.Injective.isDomain` instead of `NoZeroDivisors` (FieldAction:72); `Fintype (CyclicSublattice L m)`; `IsScalarTower` for the three `Algebra _ FunctionField` structures (UHPFF:104); `CharP (LaurentSeries (ZMod p)) p` as an instance (KF:190).
- **Structure**: `CuspData` → structure with named fields; `CoxMatrix` `@[ext]`; `toCoxMatrix` (Classification:28) and Interpolation:32/96/404 term-mode instead of `by classical; exact`.
- **`@[fun_prop]`**: hand-written `ContinuousAt` at NormalFormGrowth:50–53, `ResToImagAxis.Pos.const` lacks the tag its siblings have; `ResToImagAxis.Differentiable` has a non-dischargeable `0 < t` side goal.

### 6.4 API completeness gaps (per definition; full list in step7 §4)
`MeromorphicField`: `orderAt_one/_inv/_algebraMap` + the `AddValuation` promised at :483, `divisor_one/_div`, `toFun_zero/_one/_neg`, `ofMeromorphic_toFun` round-trip, `ofMeromorphic_eq_of_eventuallyEq`/`ofMeromorphic_mul` (ModularFunctionField:56–86 reaches into germ internals) · `PeriodPair`/`CyclicSublattice`: `map_id/map_map/scale_scale/dual_dual/toPeriodPair_ω₁/ω₂` · `BivariatePolynomial.map`: `map_neg/map_sub/map_map/map_id` · `modularPolynomial`: `monic/natDegree/degree/coeff` family · `formalCoxPolynomial`: `monic/natDegree` · `OnePoint.IsMeromorphicAt`: `smul_iff/infty_iff` · `IsOfExponentialGrowth`: closure set · `ResToImagAxis`: public `_add/_mul/_smul` (+ `_neg/_sub/_pow`) · `laurentqExpansion`: `_sub/_pow/_polynomialIn`, simp `_zero/_one`.

### 6.5 Long-proof collapse map — 42 proofs > 30 lines, each with 1–2 named helpers and expected residual length: step7-api-analytic §5 (22) and step7-api-cox §5 (20). Largest wins: `coxMatrix_smith_normalization` 50 → ≈ 15 (via `ofColumnHNF` + `exists_SL2_inv_mul_eq_upperTriangular`), `exists_hnf_transform` 44 → ≈ 20, `analyticAt_cuspFunction_poleRemoved` 43 → ≈ 15 (via `meromorphicOrderAt_eq_int_iff` transport), `exists_const_poleOrder_sub_mul_pow_lt` 42 → ≈ 15, `CuspData.polynomialInJ_of_holomorphic` 41 → ≈ 20, `laurentqExpansion_coxAction_coeff_aux` 41 → 0 (subsumed by the substitution bridge), `E_even_imag_axis_real` 54 → dead.

### 6.6 Naming / namespace hygiene that blocks discovery
Root-namespace `laurentqExpansion.*` (should be `UpperHalfPlane.…`), `to_qExpansion` snake_case, `coeff_of_geq`; `levelJ` vs `jN` (two names, 30+ callers); `E4` vs `E₄`; `varX`/`varY` inverted vs mathlib `X`/`Y`; `eval` argument order vs `evalEval`; theorem-number names (`theorem_11_18_*`, `theorem_11_23`, `theorem_11_9_*`) with no mathematical name; misnamed `one_le_tprod_nonneg`, `qExpansion_injective`, `qExpansion_mul_coeff`, `dual_base_j`, `exp_periodo`; placeholders `auxasdf`, `asdf`, `foo`, `hammerTime`; 43 root-namespace lemmas in link.lean; `Filter.eventually_atImInfty` in the wrong namespace; theorems declared into `Mathlib.Meta.NormNum*`, `ModularGroup`, `SlashInvariantForm` namespaces (bump hazard); root-level `α`, `β`, `swap`; general lemmas hidden as `private` (LevelThree:559/638/689, FormalCoxProduct:163, HNF:76/232/247/343).

## Part 7: Junk / Removable

Report: `analysis-2026-09-25/step8-junk.md` (every one of the 336 unused-candidates re-grepped with a Unicode-aware word matcher;
a conservative declaration-level dependency graph over all 1,792 declarations; closure computed for the `Modularforms/` subtree
and globally; all 84 July entries re-verified — 18 DONE, 14 STILL OPEN, 12 KEEP verdicts reversed to REMOVE on current evidence).

| Verdict | Entries | Lines |
|---|---|---|
| REMOVE-FILE (dead / 100 % mathlib / test-only) | 33 files | 4,709 gross, ≈ 4,580 net after relocating ≈ 130 live lines |
| REMOVE-DEAD (declarations in files that stay) | 83 decls | 569 |
| REMOVE-WRAPPER | 6 | 24 |
| REPLACE (mathlib duplicate with call sites, incl. the LevelThree jet split) | 15 | ≈ 300 |
| INLINE | 7 | 45 |
| Non-declaration junk (stale comments, dead `variable`s, duplicated headers, unused/boilerplate imports, `open` blocks, escapes, placeholders, unreachable branches, instances) | 74 | ≈ 120 |
| KEEP-TERMINAL (headline results with no consumer by design) | 47 | — |
| KEEP (unused-candidates with grep-verified real uses) | 56 | — |

**Total removable ≈ 5,300 lines of 19,732 (27 %) without mathematical loss, plus ≈ 300 under REPLACE.** `Modularforms/`
(4,289 lines) shrinks to ≤ 150 lines now and to `ForMathlib_Cusps.lean` (21 lines) after the Γ(1)→𝒮ℒ retargeting.

Whole-file verdicts (evidence and live-declaration relocation per file in step8 §2): REMOVE-FILE — `Modularforms/{BigO,
clog_arg_lems, eta, csqrt, equivs, upperhalfplane, exp_lems, AtImInfty, IsCuspForm, DimensionFormulas (relocate the sorry),
E2 (optional salvage `E₂_S_transform`, `E₂_eq`), Eisensteinqexpansions (1 live line), Summability/{Basic, Reciprocal, QExpansion},
summable_lems, tsumderivWithin, iteratedderivs, multipliable_lems, qExpansion_lems (inline `qExpansion_ext` first), NormNumI,
ResToImagAxis, SlashActionAuxil (after Delta), Delta (via REPLACE), Eisenstein (keep `E₄`, `E₆`, `bernoulli'_six`,
`Delta_q_one_term` ≈ 20 lines)}`, `Tactic2/*` (4, move to `test/`), `qExpansion_tactic/Examples` (move) + `Qj.lean:166–304`
meta layer (move), `ScratchGS.lean`, `XYin/Basic.lean`, `ModularFunctions/CuspPeriod.lean` (+ Cusps:39–86 dead chain — **confirm
with author**, in-progress API). KEEP — `ForMathlib_Cusps.lean`, `jFunction/qexp_coeffs.lean` (documentation-grade, terminal).
REMOVE-DEAD blocks in files that stay: `LaurentQExpansion.lean:600–706` (circle-integral subtree, advertised as a main result,
zero consumers — July KEEP reversed), `MeromorphicField.lean` 20 decls / 113 lines (ProjectVD port residue), IntegralPowerSeries
middle layer + ModularForms section, Cox 16 declarations (`jIntegralLaurentSeries_coeff/_map_complex`, `specializeJMod_varX/varY`,
`transformedJSeries_one_sigmaZero_eq_primeLower_pow`, `cyclicSublattice_hnf_matrix`, `ratFuncEvalJ_injective`, `algebraMap_jElement`,
`transportedBasis_apply_coe`, `map_carrier`, `toCyclicSublattice_carrier`, `coe_smulLatticeEquiv_apply/_symm_apply`,
`j_eq_iff_exists_sl2_smul_eq`, `bN_eq`, `coe_levelJModularFunction`, `toMeromorphicField_eq_ratFunc`), `jN_cuspFunction_meromorphicAt`
+ 64 lines of private helpers, `invariantsDetermineLattice` (uniqueness:291), link.lean `E6_int_link`/`qoverDeltaCoeffInt_zero`.

Safe deletion order (each step keeps the build green if its listed retargets are done first; details in step8 §6):
0. `ScratchGS.lean`, `XYin/Basic.lean` (+ `XYin.lean:1`), DiagonalLaurent:1–10 duplicate header, the 83 REMOVE-DEAD declarations outside Modularforms (−569).
1. Move `Tactic2/*`, `qExpansion_tactic/Examples.lean`, `Qj.lean:166–304` to a second lean_lib `XYinTest`; drop `XYin.lean:29–32,39` (−532 library lines). Optional: keep `analyticAt_cuspFunction_{mul,add,sub,neg,smul}` + `isBoundedAtImInfty_sub` in a ForMathlib file.
2. `DimensionFormulas.lean` → move the sorry to ForMathlib restated with `[Γ.FiniteIndex]`; delete (−200).
3. `IsCuspForm.lean` (drop Eisenstein:9 after deleting `Delta_E4_E6_aux` :304–329), then `qExpansion_lems.lean` (inline `qExpansion_ext` at link:250) (−265).
4. `Eisenstein.lean` → keep four declarations (or move them to `Deltaqexpansions.lean`) (−672).
5. `Eisensteinqexpansions.lean` → frees `Summability/QExpansion`, `summable_lems`, `Summability/Reciprocal`, `tsumderivWithin`, `iteratedderivs`, `BigO`, `Summability/Basic`, `exp_lems`, `equivs`, `upperhalfplane` (−1,333).
6. `Delta.lean:64–149, 193–408` + its unused `public import`s → frees `clog_arg_lems`, `eta`, `csqrt`, `E2`, `multipliable_lems`, `NormNumI`, `ResToImagAxis`, `AtImInfty` (−1,359).
7. `SlashActionAuxil.lean` Γ(2) chain and wrappers (−250; park `Γ2_generate` in git).
8. REPLACE step (Part 3.2 migration): retarget `Delta`, `Δ`, `E₄/E₆`, `Delta_q_one_term`, `Δ_ne_zero`, `Delta_boundedfactor` to mathlib; delete `Delta.lean`, `SlashActionAuxil.lean`, the Eisenstein remnant (−169).
9. After author confirmation: `CuspPeriod.lean` + Cusps dead chain; LevelThree jet-split collapse (≈ −210); INLINE / REMOVE-WRAPPER items (≈ −70).

Non-declaration junk (74 items, exact lines in step8 §4): stale comments ("being PRed slowly", "in the mod forms repo", "shrug",
"This is the hard one", `talk4.lean`, Section11BC docstring citing non-existent Lemma 11.10/11.11/11.24, MeromorphicField:73);
five merged module docstrings + repeated `open`/`variable` blocks in MeromorphicField; dead `variable` lines (Eisenstein:102/379,
iteratedderivs:59); unused imports (LevelThree `PowerSeries.Trunc`, Delta `eta`/`clog_arg_lems`/`NormNumI`, Kronecker:9, LatticeJ
`NormTrace`, uniqueness `Topology.Algebra.Module.Cardinality`, boilerplate `CStarAlgebra.*`/`StarOrdered`/`CompletePartialOrder`/
`Mathlib.Tactic`); `Classical.choose` with an explicit witness in hand (DimensionFormulas:80, jfunction:319/493, IsCuspForm:84);
deprecated `simp (config := …)` ×16 (qexp_simp); 5 no-op `noncomputable example`s; unreachable branches Qj:248/260;
`reportTiming := true` constant (Qj:44, should be a `register_option`); `linter.style.header false` (link:4).

## Part 8: Mathlibable Assessment

Report: `analysis-2026-09-25/step9-mathlibable-triage.md`. **The full per-declaration `/mathlibable` workflow was not run this
session** (1,088 candidates after pre-filter; the `chatgpt-math` MCP server failed to connect; the July loop stands at 13/595 with all
13 declarations still present). What exists: the cheap pre-filter for all 1,792 declarations, the 13 July verdicts carried forward,
and a triage of every Step 4/6/7 finding graded by grep + scratch-compile evidence.

Pre-filter: 704 SKIP (600 private, 71 exact-name collisions, 18 anonymous instances, 14 `_aux`, 1 internal docstring) → 1,088 candidates
(≈ 560 after Step 8 pruning).

July verdicts (all re-verified to exist): `lattice_eq_of_g₂_eq_of_g₃_eq` **YES-add-as-is** (uniqueness:282; the whole ℘-recursion
block goes with it — mathlib TODO at Weierstrass.lean:938) · `laurentSeriesMapRingHom` YES-but-generalise (now compiled as
`HahnSeries.mapRingHom` **[C]**) · `card_coxMatrix` YES-but-generalise (Dedekind ψ; `(Gamma0 m).index = card (CoxMatrix m)` **[C]**) ·
`index_eq_natAbs_det`, `rankTwoContent` NO-composable · 8 HNF declarations BORDERLINE (one scoping decision: rank-n over Bézout/PID
with the correct criterion D_{n−1}=1, or project-local).

Triage (details and per-item evidence in the report):
- **LIKELY-YES (≈ 45)** — analytic: ℘-uniqueness block; `cuspFunction_inv`, `cuspFunction_apply_zero_of_tendsto`, `cuspFunction_nat_mul_eq_cuspFunction_pow`, hypothesis-free `cuspFunction_add/mul_eventuallyEq`; `meromorphicAt_of_comp_pow`; `analyticTaylor_comp_pow` (as `PowerSeries.expand`); `MeromorphicNFAt.analyticAt_of_eventually_norm_le` **[C]** (𝕜→E), `MeromorphicNFAt.comp_analyticAt_of_deriv_ne_zero`, `AnalyticAt.conj_conj`, `MeromorphicNFAt.conj_conj`; `meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq`, `exists_analyticAt_pow_succ_mul…`; `Subgroup.hasDetPlusMinusOne_conj`/`discreteTopology_conj`; 8 codiscrete/`NeBot` lemmas; `Algebra R (Germ l A)`; `Filter.eventually_atImInfty`, `arg_pow_aux`, `hasProd_le_nonneg`, `Complex.im_tsum_eq_zero_of_forall` **[C]**; `E₂_S_transform`, E₂ boundedness at i∞; `analyticAt_cuspFunction_{mul,add,sub,neg,smul}`, `isBoundedAtImInfty_sub`; `ForMathlib_Cusps`; `periodic_comp_ofComplex_of_vadd`; `modularFormModuleofIsScalarTower`; the transport lemma family **[C]**; two upstream-unlock PRs (publicise `hasFPowerSeriesOnBall_update`; expose the `E2/Transform` δ-block). Algebraic: `HahnSeries.mapRingHom` **[C]**, `coeffSubring` **[C]**, `leadingCoeff_pow` **[C]**, `CharP (HahnSeries Γ R) p` **[C]**, `order_eq_of_coeff_ne_zero_of_forall_lt` **[C]**; `PowerSeries.map_frobenius_expand` **[T]**, `LaurentSeries.coeff_single_neg_mul_coe_expand` **[T]**, `LaurentSeries.substMonomial` **[T]**; `PowerSeries.lifts`; `coeff_invOfUnit_one_succ`; `dedekindPsi` + Γ₀ index **[C]**; `Matrix.exists_SL2_inv_mul_eq_upperTriangular`, `SpecialLinearGroup.mul_coe_mul_coe_inv` **[C]**, `Matrix.toLin_injective_of_det_ne_zero`, `exists_coprime_add_mul_of_gcd_gcd_eq_one`; `Polynomial.associated_iff_eq_or_eq_neg`; conjugate-counting pair (drop `minpoly`); `eval_interpolation_sum_at`; Bivariate `coeff_coeff_swap`/`map_swap`/`diagonal_swap`/`specializeY_ext`; `PeriodPair` scaling/`discriminant`/`j` + `WeierstrassCurve` bridge; `MeromorphicAt.aeval_polynomial`; Γ₀(N) conjugation API.
- **BORDERLINE (8 families)** — HNF (rank-n decision); `ModularFunction Γ` + `MeromorphicField` (coordinate with Kebekus's ProjectVD, add ring ops first); `IsOfExponentialGrowth`/`GrowthAtCusp` (after the `IsBigO` restatement); `OnePoint.IsMeromorphicAt`; bidegree-≤3 detection (level-3 hard-coded); cyclic-sublattice classification (generalise to rank-2 free ℤ-modules first); `Γ2_generate` (new, unused); un-normalised `interpolationAt`.
- **NO — mathlib has it (≈ 200 declarations)** and **NO — composable (≈ 30)**: the lists in Part 3.1 / step9 §9c.

---

## Recommended Action Plan

### Priority 1: Quick wins (mechanical, build stays green)
1. Step 0–1 of the deletion order: `ScratchGS.lean`, `Basic.lean`, duplicate header, 83 dead declarations (−569), test/example files + `#qexp` meta layer to a `XYinTest` lean_lib (−532 library lines), `summable_lems` facade.
2. Delete the two global instances (`FunLike (ℍ→ℂ)`, `SMul ℕ+ ℍ`); localise the `Fact` instances; fix the 74 non-declaration items (stale comments, dead `variable`s, unused/boilerplate imports, `simp (config := …)`, `Classical.choose` with explicit witnesses).
3. One-line mathlib swaps with call sites: `not_isSquare_of_between_sq_aux` → `Nat.not_exists_sq'`; inline `eval_derivative_prod_X_sub_C_at`; `matrix_eq_upper_triangular_aux` → `Matrix.eta_fin_two`; `precompAlgEquiv`/`precomp_ratFunc`; `coxPhiAtJ_monic/_natDegree`; `jUnitLaurentSeriesMod_eq_unitJPowerSeries`; `⟨N*z,_⟩` → `posRealAction`; the 20 verified one-liners of Part 6.2 item 12 (`CoxMatrix.ext`, `d_dvd`, `coprime_gcd_b`, SL₂-cancel, `S_smul_eq`, `im_tsum_eq_zero_of_forall`, `poleRemoved_of_poleOrder_eq_zero`, `coeff_of_geq'`, `HolomorphicFunction.ext`).
4. Publicise the private originals that are re-proved elsewhere: `delta_eq_discriminant`, `rankTwoContent_dvd_mul_left`, `columnHNF_eq_of_mul`, `exists_sl_right_mul_isColumnHermiteNormalForm_aux`, `hermite_repr_apply`/`repr_apply`, `d_mul_a_eq_m`, `dual_content_eq_one`, the two `jIntCoeff` bridges, `eventually_arg_pow`, `qExpansion_qParam_pow`, `indexUnit`.

### Priority 2: API improvements (the user's focus; significant impact)
1. Transport lemma family + `meromorphicAt_cuspFunction_*`/`poleOrder_*` closures, simp families for `poleOrder`/`poleRemoved`/`laurentqExpansion` (LaurentQExpansion.lean currently has zero `@[simp]`), `laurentqExpansion` as a `RingHom`.
2. `laurentqExpansion_polynomialIn/_pow`; `laurentqExpansion_nat_mul` as `embDomain`; then the `substMonomial` bridge (≈ 210 lines, unifies the Cox eq. 11.13 chain and Algebra's period-change block).
3. `CuspData` structure + `apply_smul` + `LevelOneCuspData.of_widthM` + `ModularFunction.ofGamma0Holomorphic`; ring/field operations and a `ModularFunctionClass` on `ModularFunction Γ` (unlocks 11.9(ii) as a genuine subfield statement); `toFun_precomp`; growth-predicate closure set after the `IsBigO` restatement.
4. Cox: `jLaurentSeriesWidth R m` + `coeff_single_neg_mul_coe_expand` (≈ 340 lines across Kronecker/KF/LevelThree); `CoxMatrix.ofColumnHNF` + HNF field lemmas via `BlockTriangular`/`Finset.gcd`; `act_eq_sl2_smul_of_mul` via `glAction`; `Matrix.exists_SL2_inv_mul_eq_upperTriangular`; `BivariatePolynomial.map` as a ring hom + `modularPolynomialC_swap`/`_eval_act_j`; `HahnSeries.coeffSubring`/`mapRingHom`; canonical `jIntCoeff` with explicit witness; IntegralPowerSeries cast lemmas; `evalEval` as the single evaluation convention.
5. LevelThree: state `jIntegralLaurentSeriesWidth m = single (−m) 1 * ↑(expand m …)` at Kronecker level and collapse the 35-lemma jet split into one `decide +kernel` (≈ 220 lines; 6.7 s measured).

### Priority 3: Generalisations (mathematical thought)
`Field K` → `IsDomain` in the three Laurent files (**[C]**); drop dead `CharZero`/`Fact` hypotheses; `HasCoeffsIn` → `PowerSeries.lifts`; `CyclicSublattice`/Classification over any rank-2 free ℤ-module; Dedekind ψ as an `ArithmeticFunction`; conjugate-counting lemmas without `minpoly`; `𝕜 → E` for the four meromorphic-order/normal-form lemmas; weight-k `.slash` for growth; `IsImaginaryQuadratic` ⇔ `minpoly` degree 2; restate the sorry with `[Γ.FiniteIndex]` and attempt the Sturm-bound route; bidegree-≤n detection (needed for any Φ_m beyond 3).

### Priority 4: Structural changes
1. **The Γ(1) → 𝒮ℒ migration** (Part 3.2; ≈ 1,450 lines deleted, six build-green steps) followed by deletion-order steps 2–8 — reduces `Modularforms/` from 4,289 lines to `ForMathlib_Cusps.lean`.
2. Duplication unifications from Part 4 (shared helpers list); the two evaluation conventions; `levelJ` vs `jN` and the three names for `levelJFieldElement`; `CuspPeriod`/`Cusps` dead chain after author confirmation.
3. Upstream-first restructures: Laurent expansion of a meromorphic germ (the whole LaurentQExpansion layer at mathlib generality); rank-n HNF.

### Priority 5: Mathlib contributions (per Part 8 triage; full `/mathlibable` runs still pending)
- **Ready now (YES-add-as-is, some compiled this session)**: `lattice_eq_of_g₂_eq_of_g₃_eq` + ℘-recursion block; `HahnSeries.mapRingHom`, `coeffSubring`, `leadingCoeff_pow`, `CharP` instance, `order_eq_of_coeff_ne_zero_of_forall_lt`; `Subgroup.hasDetPlusMinusOne_conj`/`discreteTopology_conj`; the 8 codiscrete/`NeBot` lemmas; `MeromorphicNFAt.analyticAt_of_eventually_norm_le`; `cuspFunction_inv`/`_apply_zero_of_tendsto`/`_nat_mul`; `E₂_S_transform`; `Filter.eventually_atImInfty`; `ForMathlib_Cusps`; `coeff_invOfUnit_one_succ`; `Complex.im_tsum_eq_zero_of_forall`.
- **Generalise-then-PR**: Dedekind ψ + Γ₀ index; `PowerSeries.lifts`; conjugate-counting pair; `analyticTaylor_comp_pow`; `PowerSeries.map_frobenius_expand`; `substMonomial`; `PeriodPair` scaling/`j` + `WeierstrassCurve` bridge; Bivariate swap lemmas; `hasProd_le_nonneg`; `meromorphicAt_of_comp_pow`.
- **Two small PRs that unblock deletions here**: publicise `hasFPowerSeriesOnBall_update`; move the `E2/Transform` δ-block under `public section`.
- **One scoping decision unblocks eight verdicts**: rank-n HNF.
- **Run the full `/mathlibable` loop** on the ≈ 45 LIKELY-YES declarations (not the 1,088) once the `chatgpt-math` server is back.

---

## Historical records

The July 2026 overview (scope: everything except `Modularforms/`), the 2026-09-21 structural pass, and the 2026-09-21
proof-cleanup pass are preserved verbatim in `.mathlib-quality/overview/PROJECT_OVERVIEW-archive-2026-09-21.md`; their
per-file evidence remains in `.mathlib-quality/overview/{inventory,analysis,mathlibable}/` and `.mathlib-quality/proof-cleanup/`.
Their metrics and open-item labels are superseded by this document.
