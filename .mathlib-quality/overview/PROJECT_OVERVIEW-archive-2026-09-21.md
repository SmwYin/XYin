# Current proof-cleanup overview — 2026-09-21

The follow-up proof-focused pass inspected all 83 Lean files, changed 56, and shortened
353 existing theorem/lemma bodies. Source lines decreased from 23,837 to 19,649 (net −4,188).
Existing public signatures and mathematical definitions are preserved; the new modular-function
field API remains in use throughout Cox.

- Reused mathlib and shared project APIs for series, derivatives, dimension formulas, j, and Cox proofs.
- Filled 14 existing admissions: the active `sorry` count is now **1**, in `dim_gen_cong_levels`.
- Full `lake build`: **PASS**, 3,917 jobs. Independent review: no unresolved findings.
- Compiled axiom audit: 2,461 project theorem constants checked; only the one retained admission
  uses an axiom beyond `propext`, `Classical.choice`, and `Quot.sound`.

See the [per-file cleanup summary](.mathlib-quality/proof-cleanup/summary.md) and
[verification receipt](.mathlib-quality/proof-cleanup/verification.md). The structural and July
records below are historical; their metrics and unresolved-item labels are not current status.

---

# Earlier structural pass — 2026-09-21

The requested overview → split-file → decompose-proof → cleanup pass is complete.
The survey covered all 78 original Lean modules, including `PhD/Modularforms/`.

- Split the 1763-line summability module into Basic, Reciprocal, and QExpansion, retaining the old import path.
- Split Cox modular-function cusp data and level transforms from level-one rationality; the new bundled modular-function API is preserved.
- Reused existing HNF and differentiation helpers and mathlib's weight-two/q-expansion theorems.
- Full build: **PASS**, 3916 jobs. Active `sorry` count: **19 → 15**; source lines: **24,194 → 23,837**.

See [the current structural report](.mathlib-quality/overview/structural-refactor-2026-09-21.md) for selected and deferred candidates, file inventory, proof sizes, review, performance, and validation evidence.
This is a structural maintainability pass, not a restart or completion of the older exhaustive mathlib-suitability assessment.

The July overview below is preserved as historical evidence; its scope, metrics, and open-item labels are not the current repository status.

---

# Project Overview: XYin (excluding `PhD/Modularforms/`)

Generated: 2026-07-17/18 · mathlib pin 2026-05-28 · branch `PhD_Experiment`

Scope: everything except `XYin/PhD/Modularforms/`. Detailed evidence lives under
`.mathlib-quality/overview/` — per-declaration inventories in `inventory/`, the five
deep-analysis reports in `analysis/`, per-declaration mathlibable reports in `mathlibable/`.

> **Status note.** After the analysis phases completed, an overview-driven cleanup pass was
> executed over `IntegralPowerSeries/`, `jFunction/`, `LaurentQExpansion/`, and
> `qExpansion_tactic/` (12 worker passes, all builds green). Findings in Parts 3–7 that were
> already applied are marked ✅ DONE; unmarked items remain open. The Step 9 mathlibable
> assessment is **paused at 13 of 595** candidates.

## Executive Summary

The project is a substantially complete, essentially sorry-free formalization of Cox,
*Primes of the form x²+ny²*, Chapter 11 §§B–C: the j-invariant classification of ℂ-lattices
(via a self-contained proof that a lattice is determined by g₂, g₃), the theory of level-one
and Γ₀(m) modular functions (j generates the function field — Thm 11.9), the modular
polynomial Φ_m (construction, interpolation, irreducibility, integral descent — Thm 11.18,
with the explicit Φ₃ of eq. 11.22 certified by kernel computation), cyclic sublattices and
their classification by Cox matrices (Thm 11.23), the Kronecker congruence
Φ_p(X,X) ≡ (X^p−X)²... route (Thm 11.18(v)), and integrality of singular moduli (Thm 11.23/
Lemma 11.24 route). Supporting this is a reusable analytic infrastructure: Laurent
q-expansions of meromorphic-at-∞ functions on ℍ, integral power series, a rank-two Hermite
normal form theory, and a `native_decide`-certified q-expansion coefficient calculator.

The mathematics is in good shape: 44 files, ~15.5k lines, roughly 1,240 declarations, and
after cleanup **zero sorries** in scope. The main structural findings: (1) the analytic
Laurent-at-the-cusp layer is genuinely novel relative to mathlib (mathlib's meromorphic API
has no Laurent-series link) and is the project's strongest upstream candidate along with the
lattice-uniqueness theorem and the HNF development; (2) before cleanup there was significant
internal duplication (35 verified pairs) and dead speculative API (~34 declarations), most of
which is now removed in the four cleaned folders but **remains open in `Cox/`**; (3) a
handful of definitions should ride richer mathlib API (`Polynomial.evalEval` family,
`HahnSeries.ofSuppBddBelow`, `Matrix.adjugate`, `Finset.gcd`, Lagrange nodal API) — partially
applied in the cleaned folders, open in `Cox/`.

## Statistics

- Files: 44 in scope (~15,469 lines after cleanup; 16,034 before)
- Declarations: ~1,246 inventory entries (≈663 lexically public)
- Sorries: **0** (the single pre-existing sorry was dead code, deleted)
- Moral duplications found: 35 pairs — 14 DELETE-ONE, 6 UNIFY, 4 DERIVE, 6 EXTRACT-HELPER, 5 DISTINCT (most non-Cox ones now fixed)
- Generalization opportunities: 24 (13 Low / 7 Medium / 4 High), 4 refuted
- Missing-API items: 11 helper lemmas, 5 simp clusters, 4 instance gaps, 13 long proofs mapped to collapsing lemmas
- Junk: 84 entries — 25 REMOVE (✅ applied in cleaned folders), 1 INLINE, 4 REPLACE, 54 KEEP
- Mathlibable (partial, 13/595): 1 YES-add-as-is · 2 YES-but-generalise-first · 2 NO-composable · 8 BORDERLINE · 51 pre-filtered SKIP (21 test-file, 10 anonymous, 20 name-collision)

---

## Part 1: Declaration Inventory

Full per-declaration inventories (Type/What/How/Hypotheses/Uses/Used-by per entry) are in
`.mathlib-quality/overview/inventory/<Module.Path>.md`, one file per module. Per-file
highlights:

| File | Decls | Character |
|---|---|---|
| `uniqueness.lean` | 16 | Lattice determined by (g₂,g₃); Laurent recursion + identity theorem. Sorry-free, self-contained over mathlib |
| `IntegralPowerSeries/IntegralPowerSeries.lean` | ~26 | ℤ-integrality predicates for power series (`HasCoeffsIn`, `IsIntegralPowerSeries`) |
| `LaurentQExpansion/LaurentQExpansion.lean` | ~45 | `poleOrder`, `poleRemoved`, `to_qExpansion`, `laurentqExpansion` — Laurent expansion at the cusp for meromorphic-at-∞ functions |
| `LaurentQExpansion/Algebra.lean` | ~23 | Ring operations on Laurent q-expansions (`mul`, `add`, `nat_mul` rescaling) |
| `jFunction/Deltaqexpansions.lean` | ~35 | Integral q-expansions of E₄, E₆, Δ; `ramanujanTau` |
| `jFunction/jfunction.lean` | ~60 | The j-function, `qj`, `qjCoeffs`; integrality of j's Laurent coefficients |
| `jFunction/jLevelN.lean` | 16 | `jN` (j(Nτ)) and its cusp behavior |
| `jFunction/jInvariantLink.lean` | 10 | Bridge PeriodPair → mathlib `WeierstrassCurve` (c₄/c₆/Δ/j identities) |
| `jFunction/qexp_coeffs.lean` | 23 | Explicit coefficient values: τ(1..3), Δ-coeffs, j-coeffs (documentation-grade API) |
| `qExpansion_tactic/Qj.lean` | ~32 | `native_decide` coefficient calculator (σ_k sums, array convolution, series inversion) |
| `qExpansion_tactic/link.lean` | ~34 | Soundness: arrays compute the true analytic q-expansions |
| `Tactic2/qexp_simp.lean` + attr + tests | 47 | `qexp_simps` simp set + `qexp_simp` macro + test files |
| `Cox/HermiteNormalForm.lean` | 24 | Rank-two column HNF over ℤ: existence, uniqueness, index=\|det\|, cyclic-quotient criterion |
| `Cox/LatticeJ.lean` | 55 | `PeriodPair.j`, homothety, `j_surjective`, `j_eq_iff_exists_sl2_smul_eq` |
| `Cox/ModularFunction.lean` | 55 | `IsGamma0ModularFunction`, level-one functions are rational in j (Thm 11.9(i)) |
| `Cox/CoxMatrices/Basic.lean` | 79 | `CoxMatrix` structure, reduction, right-coset equivalence |
| `Cox/CoxMatrices/Cardinality.lean` | 22 | \|C(m)\| = m·∏(1+1/p) (= Dedekind ψ) |
| `Cox/CoxMatrices/LaurentExpansion.lean` | 25 | Cox eq. 11.13: Laurent expansion of j∘σ; Galois reindexing (Thm 11.18(i)) |
| `Cox/FormalCoxProduct.lean` | 15 | Formal product over Cox matrices; coefficient integrality |
| `Cox/UpperHalfPlaneFunctionField.lean` | 30 | `HolomorphicFunction`/`FunctionField` subrings of functions on ℍ; `ratFuncEvalJ` |
| `Cox/ModularPolynomial/{Construction, AnalyticSupport, Interpolation, Irreducibility, IntegralDescent}` | 122 | Φ_m: `BivariatePolynomial`, existence/uniqueness, interpolation (Thm 11.9(ii)), irreducibility, ℤ-descent |
| `Cox/{LaurentPolynomialEvaluation, DiagonalLaurent, SymmetricCubicLaurent}` | 68 | Laurent-series evaluation ring homs; Φ_m(X,X) leading-coefficient analysis; bidegree-≤3 detection |
| `Cox/{Kronecker, KroneckerFrobenius}` | 76 | Mod-p Laurent series, Frobenius/expand; Thm 11.18(v) |
| `Cox/LevelThree.lean` | 108 | Explicit Φ₃ (Cox eq. 11.22) via `decide +kernel` jet computations (only 2 public decls) |
| `Cox/{CyclicSublattice, CyclicSublattice/Classification}` | 100 | Cyclic sublattices, dual lattice, classification by Cox matrices (Thm 11.23) |
| `Cox/{Arithmetic, SingularModuli, ModularFunctionField}` | 50 | Thm 11.18(i,ii,iv), Φ₃ example, singular moduli are algebraic integers, Thm 11.9(ii) field version |

## Part 2: Cross-File Dependencies

Full graph: `.mathlib-quality/overview/inventory/_import-graph.md`. Shape: a clean DAG in
five layers — (0) `uniqueness`, `HermiteNormalForm`, `IntegralPowerSeries`; (1)
`LaurentQExpansion` → `jfunction` → `LatticeJ`/`jLevelN`; (2) `ModularFunction` →
`CoxMatrices/*`; (3) `ModularPolynomial/*` → `DiagonalLaurent`/`Kronecker`/`LevelThree` →
`Arithmetic`; (4) `SingularModuli`/`ModularFunctionField` → umbrella `Section11BC`.
Everything is reachable from the root `XYin.lean`. Notes: `uniqueness.lean` sits oddly at
`XYin/` root (move under `PhD/`?); test files are imported by the library root (mathlib
convention would separate them); `LatticeJ.lean` depends on the excluded
`Modularforms/ForMathlib_Cusps`.

## Part 3: Mathlib API Audit (most important)

Reports: `analysis/step4-{qexpansion,lattice,coxmatrices,computation}.md`. Highlights:

**Replace with mathlib (verified exact/near matches)**
1. ✅ DONE `analyticAt_hasFPowerSeriesAt_taylor` = `AnalyticAt.hasFPowerSeriesAt` — deleted.
2. ✅ DONE `powerSeriesMapAlgHom` = `PowerSeries.mapAlgHom (Algebra.ofId R A)` — redefined.
3. ✅ DONE `invFn`/`qoverDelta_mul_eq_one` → `PowerSeries.invOfUnit`/`mul_invOfUnit`.
4. ✅ DONE `sigmaPow_eq_sigma` inner bijection = `Nat.filter_dvd_eq_divisors`.
5. OPEN `not_isSquare_of_between_sq_aux` (SingularModuli) = `Nat.not_exists_sq` — delete aux.
6. OPEN `eval_derivative_prod_X_sub_C_at` (Interpolation) = `Lagrange.eval_nodal_derivative_eval_node_eq` ∘ `Lagrange.eval_nodal` — delete.
7. OPEN `bivariateLaurentEvalHom`/`bivariateLaurentEval` + `bivariateLaurentEval_map` (SymmetricCubicLaurent/LevelThree) → mathlib `Polynomial.evalEval`/`aevalAeval`/`map_mapRingHom_evalEval` (Bivariate.lean).
8. OPEN 4 anonymous Hahn-series constructions in Kronecker.lean → `HahnSeries.ofSuppBddBelow` (~40 lines of PWO plumbing).
9. OPEN `dualMatrix` (CyclicSublattice) is `Matrix.adjugate` of the HNF matrix — redefine to unlock `mul_adjugate`/`det_adjugate`.
10. OPEN `rankTwoContent` → respell via `Finset.gcd` (verified 1-call composition); `carrierEquiv` machinery → `Submodule.equivMapOfInjective` (~28 lines).

**Confirmed design issues**
11. ✅ DONE Instance diamond: global `Module R (ModularForm Γ k)` collided with mathlib's ℝ/ℂ instances — now scoped.
12. ✅ DONE (by deletion) `HasIntegralQExpansion` hard-coded e^{2πiz} against period-h `qExpansion` — the whole dead file was retired.
13. OPEN `IsColumnHermiteNormalForm` should expose `Matrix.BlockTriangular` so `Matrix.det_of_upperTriangular` replaces three ad-hoc determinant computations.
14. OPEN Two evaluation conventions coexist (`BivariatePolynomial.eval` arg-flip vs mathlib `evalEval`) — standardize on `evalEval`.

**Verified genuine mathlib gaps (keep; these are PR candidates)**: the entire
Laurent-at-cusp layer (mathlib Meromorphic API has no LaurentSeries link),
`meromorphicAt_of_comp_pow`, `analyticTaylor_comp_pow`, `laurentSeriesMapRingHom`
(→ `HahnSeries.mapRingHom`), HNF (nothing in mathlib), lattice-j/uniqueness theory, binary
quadratic forms, Dedekind ψ, `coeff_invOfUnit_one_succ` (new, from cleanup), plus
`HahnSeries.leadingCoeff_pow`, `PowerSeries.map_frobenius_expand`. Refuted leads are listed
per report (e.g. `BivariatePolynomial` ↛ `MvPolynomial`, jets ↛ `PowerSeries.trunc`,
`qexp_simps` design is correct, matrixStar ≠ adjugate).

## Part 4: Moral Duplications

Report with 35-row pairwise table: `analysis/step5-duplications.md`. Status: rows touching
the four cleaned folders are ✅ DONE (exact-duplicate lemma pairs in LaurentQExpansion,
E4/E6 mirror unification, Qj Δ-table ×3 and `foo`-quadruplet, dead re-proofs in jfunction).
Remaining OPEN (all in `Cox/`):
- **A12**: 7 private lemmas re-proved char-for-char across Cox files because originals are `private` (`complex_mobius_scale_eq_affine`, `periodic_comp_ofComplex_of_vadd`, `rankTwoContent_*` ×3, `j_periodic_aux`, …) — publicize one copy each, ~120 lines deleted, zero risk.
- **A9**: three parallel "integer coefficients of j" notions (`jIntCoeff` / `qjCoeffs` / `qjCoeffInt`) — make `jIntCoeff` canonical, publish the hidden bridge.
- **A13**: 7 width-m vs h=1 Laurent-of-j lemma pairs (DiagonalLaurent vs IntegralDescent) — keep general, derive specials via `simpa using X 1`.
- **A15**: near-verbatim level-one-descent pipelines in Construction vs Interpolation — one shared helper.
- CoxMatrices/Basic: `exists_coxMatrix_reduction` duplicates `exists_coxMatrix_of_isColumnHermiteNormalForm_aux` (~30 lines) — refactor former to use latter.
- SymmetricCubicLaurent: `symmetricCubicExpansion_coeff_*` verbatim quadruplet.
- DiagonalLaurent:258–339 re-proves LaurentPolynomialEvaluation's generic lowest-coefficient lemma at K=ℂ (~80 lines) — instantiate instead.

## Part 5: Generalization Opportunities

Report: `analysis/step6-generalization.md` (24 findings, 4 refuted). Top items:
1. **Laurent-at-cusp layer** (High): restate as "Laurent expansion of a meromorphic germ" — the prime mathlib-shaped restructure; do it upstream-first, not in-project.
2. **HNF → rank-n over Bézout/PID** (High): what mathlib would want; rank-2 is a pilot. (This is also the blocking question for the whole Step 9 HNF BORDERLINE family.)
3. **`symmetric_bidegree_three_eq_zero_of_laurent_coeff`** (High): parametrize bidegree ≤n with a weight-injectivity hypothesis — needed anyway for higher Φ_m.
4. **`coxDivisorSum` = Dedekind ψ** (Medium): name it `ArithmeticFunction.dedekindPsi`, get ℕ-valued `card_coxMatrix = ψ m`.
5. Low-hanging: three `Field K` files weaken to `IsDomain`; `HasCoeffsIn` → mirror `Polynomial.lifts` as `PowerSeries.lifts`; Irreducibility's two conjugate-counting lemmas are already fully general — extract + PR.
Refuted: comp-pow descent beyond ℂ; uniqueness beyond ℂ; ℤ→CommRing for the compute layer; composite-m prime Cox equivalence.

## Part 6: API Improvements

Report: `analysis/step7-api.md`. ✅ DONE in cleanup: the 6-site "F 0 = limUnder" glue
(`cuspFunction_apply_zero_eq` + `analyticAt_cuspFunction_of_eventuallyEq`), `poleOrder`
readers (`poleOrder_eq_of_meromorphicOrderAt_eq`, …), `shiftedLaurent_mul/add`,
`cuspFunction_const`, jfunction's `cuspFunction_apply_zero_of_tendsto`, link.lean cast
helpers. Remaining OPEN:
- `laurentqExpansion_pow` / `_polynomial_eval₂` — IntegralDescent.lean:24–68 and DiagonalLaurent.lean:164–216 are near-verbatim ~40-line inductions.
- One canonical `jIntCoeff` + a LaurentSeries-integrality layer (the missing `laurentSeriesMapRingHom_ofPowerSeries` square) — 6 files affected.
- `@[ext] CoxMatrix.ext` + `CoxMatrix.ofColumnHNF` — 4 hand-rolled injectivity proofs and the duplicated σ-construction block.
- Simp coverage is thin project-wide (53 `@[simp]` in 15k lines; core Laurent files near zero) — add `_zero/_one/_add/_mul` simp families for `poleOrder`/`laurentqExpansion`/`BivariatePolynomial` ops.
- Long-proof collapse map for the remaining Cox giants (`columnHNF_eq_of_mul` 61, `exists_coxMatrix_reduction` 59, `poleOrder_coxAction_aux` 54, `laurentqExpansion_coxAction_coeff_aux` 90, …).

## Part 7: Junk / Removable

Report: `analysis/step8-junk.md` (84 entries). ✅ DONE in cleanup: all REMOVE items in the
four folders (dead `HasIntegralQExpansion.lean` incl. the sorry, `hello`, speculative
IntegralPowerSeries submodule layer, LaurentQExpansion dead wrappers/notation, duplicate
test, `Delta_qExpansion_coeff_zero_aux`, `#min_imports`, linter escapes). Remaining OPEN:
- `ScratchGS.lean` (orphan scratch file) and empty `XYin/PhD/ModularFunctions/Basic.lean` + its root import — **deletion still pending** (files outside the four cleaned folders).
- `invariantsDetermineLattice` (uniqueness.lean:328, stale docstring citing nonexistent talk4.lean).
- Cox-side REMOVEs: `jIntegralLaurentSeries_map_complex`, `specializeJMod_varX`, `transformedJSeries_one_sigmaZero_eq_primeLower_pow`, `cyclicSublattice_hnf_matrix`, `ratFuncEvalJ_injective`, `transportedBasis_apply_coe`, DiagonalLaurent's duplicated copyright header.
- KEEP verdicts (all with named call sites or documentation value) are recorded per entry — notably the 13 explicit-coefficient lemmas, `Submodule.hermiteNormalForm`, `gamma0RightCosetsFintype`.

## Part 8: Mathlibable Assessment (partial — 13/595, paused)

Per-decl reports: `.mathlib-quality/overview/mathlibable/<decl>.md`; running tally in
`inventory/_step9-verdicts.tsv`; dispatch queue in `inventory/_step9-dispatch-list.tsv`
(595 candidates after pre-filtering 663 public decls: 21 test-file, 10 anonymous, 20
name-collision SKIPs; 24 junk-REMOVE names pruned).

| # | Declaration | Verdict | One-line rationale |
|---|---|---|---|
| 1 | `card_coxMatrix` | YES-but-generalise-first | Count is Dedekind ψ (absent from mathlib); ship as `Fintype.card = ArithmeticFunction.dedekindPsi` |
| 2 | `…HNF.index_eq_natAbs_det` | NO-composable | `AddSubgroup.index_eq_natAbs_det` + `Basis.det_apply` compose (verified compiles) |
| 3 | `…HNF.quotient_isAddCyclic_iff…` | BORDERLINE | Content absent, but naive rank-n gcd form is FALSE for n≥3; scope questions |
| 4 | `Submodule.exists_hermiteNormalForm` | BORDERLINE | Genuine gap; rank-2/ℤ vs rank-n/Bézout literature standard — scoping decision |
| 5 | `Submodule.hermiteNormalForm` | BORDERLINE | Clean SNF-style chooser; fate coupled to #4 |
| 6 | `laurentSeriesMapRingHom` | YES-but-generalise-first | Upstream as `HahnSeries.mapRingHom` (verified compiles at Hahn generality) |
| 7 | `lattice_eq_of_g₂_eq_of_g₃_eq` | **YES-add-as-is** | Uniqueness half of uniformization at literature-standard generality; fills mathlib's explicit TODO |
| 8 | `Matrix.IsColumnHermiteNormalForm` | BORDERLINE | No HNF predicate in mathlib; ships only with rank-n development |
| 9 | `Matrix.exists_right_mul_isColumnHermiteNormalForm` | BORDERLINE | Closest mathlib relative (`FixedDetMatrices.reduce_mem_reps`) not convertible |
| 10 | `Matrix.isColumnHermiteNormalForm_fin_two` | BORDERLINE | Definitional unpacking; inherits predicate's fate |
| 11 | `Matrix.rankTwoContent` | NO-composable | 1-call `Finset.gcd` composition (verified); general `Matrix.content` separate future PR |
| 12 | `Module.Basis.HermiteNormalForm` | BORDERLINE | SNF-templated bundle; square/rank-2-only vs rectangular SNF precedent |
| 13 | `…HNF.bN_eq` | BORDERLINE | Accessor transport; inherits parent |
| 14 | `…HNF.matrix_eq` | (interrupted — retry pending) | |

**Emerging picture**: the HNF file resolves as ONE user decision (commit to rank-n/rectangular
redesign before PR, or keep project-local); the confirmed upstream winners so far are the
uniformization-uniqueness theorem, `HahnSeries.mapRingHom`, and `ArithmeticFunction.dedekindPsi`.
582 declarations remain unassessed — resuming the loop is a multi-day background run; a
cheaper path is to assess only the ~30 decls the audits flagged as gap-fillers (Part 3 list).

---

## Recommended Action Plan

### Priority 1: Quick wins (mostly ✅ done for the four cleaned folders)
- ✅ Junk removal, duplicate deletion, linter-escape removal, import fixes, sorry eliminated.
- OPEN: delete `ScratchGS.lean`, empty `ModularFunctions/Basic.lean` (+ root import), `invariantsDetermineLattice`; apply the 7 Cox-side REMOVE verdicts; fix DiagonalLaurent's double header; swap `not_isSquare_of_between_sq_aux` → `Nat.not_exists_sq`; delete `eval_derivative_prod_X_sub_C_at` for the Lagrange composite.

### Priority 2: API improvements (significant impact, `Cox/` focus)
- Publicize the 7 privately re-proved lemmas (A12) and delete the copies.
- `@[ext] CoxMatrix.ext` + `ofColumnHNF`; `laurentqExpansion_pow`/`_polynomial_eval₂`; canonical `jIntCoeff`; simp families for the core Laurent defs.
- Ride mathlib: `evalEval` family, `HahnSeries.ofSuppBddBelow`, `Matrix.adjugate` for `dualMatrix`, `Finset.gcd` for content, `Submodule.equivMapOfInjective`.

### Priority 3: Generalizations (mathematical thought)
- Dedekind ψ extraction; `PowerSeries.lifts`; Field→IsDomain weakening; bidegree-≤n symmetric detection (needed for higher levels).

### Priority 4: Structural changes
- A13 width-m/h=1 consolidation; A15 descent-pipeline helper; DiagonalLaurent generic-lemma instantiation; decompose the remaining >50-line Cox proofs.

### Priority 5: Mathlib contributions
- **Ready now**: `lattice_eq_of_g₂_eq_of_g₃_eq` (YES-add-as-is — mathlib's Weierstrass file has the explicit TODO it fills).
- **Generalise-then-PR**: `HahnSeries.mapRingHom`; `ArithmeticFunction.dedekindPsi` + `card_coxMatrix`; `meromorphicAt_of_comp_pow`, `analyticTaylor_comp_pow`; `coeff_invOfUnit_one_succ`; Irreducibility's conjugate-counting pair; Lagrange/`HahnSeries.leadingCoeff_pow`/`PowerSeries.map_frobenius_expand` small lemmas.
- **One scoping decision unblocks six verdicts**: rank-n HNF (questions consolidated in the `mathlibable/*.md` HNF reports).
- **Long-term flagship**: the meromorphic-germ ↔ Laurent-series bridge (the whole LaurentQExpansion layer, restructured at mathlib generality).
