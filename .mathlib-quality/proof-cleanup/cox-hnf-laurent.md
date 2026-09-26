# Cox HNF and Laurent proof cleanup

Scope: `XYin/PhD/Cox/HermiteNormalForm.lean` and
`XYin/PhD/Cox/CoxMatrices/LaurentExpansion.lean`. Baseline is the source snapshot in
`/tmp/xyin-proof-cleanup-before/XYin`, after the preceding structural refactor.
Both files were read in full. This is a proof-focused pass: public statements, data,
namespace boundaries, attribution, and mathematical documentation are preserved.

## Results

| File | Before | After | Reduction |
|---|---:|---:|---:|
| HermiteNormalForm | 473 | 408 | 65 |
| LaurentExpansion | 438 | 354 | 84 |
| Total | 911 | 762 | 149 |

HNF adds the direct `Mathlib.Tactic.LinearCombination` import used by the new algebra
proofs. No new helper declarations, axioms, local limits, or admissions were introduced.
The `reindex` data fields are unchanged; only its primitive-content proof was simplified.

## HNF declaration audit

| Declaration / group | Action and reason |
|---|---|
| `IsColumnHermiteNormalForm`, `rankTwoContent`, `HermiteNormalForm`, `hermiteNormalForm` | Data unchanged; these definitions encode the intended fixed-basis HNF. |
| `rankTwoContent_dvd_entry`, `dvd_rankTwoContent` | Retained the small gcd-divisibility chains. They provide the explicit content API used by both multiplication directions. |
| `rankTwoContent_dvd_mul_right`, `rankTwoContent_dvd_mul_left` | Retained: direct application of divisibility to the two entry products; no repeated large argument. |
| `isColumnHermiteNormalForm_fin_two`, `exists_unit_mul_pos_aux` | Retained finite-index and sign cases; already short and deterministic. |
| `hnf_transform_det_aux` | Replaced the polynomial calc and substitution by `linear_combination s * h`. |
| `hnf_transform_mul_aux` | Each entry is handled directly after matrix reduction. Three hypothesis-dependent entries now use explicit linear combinations; removed nested calc and manual rewriting. 22 → 13 lines. |
| `exists_hnf_transform` | Bezout normalization and pivot determinant use linear combinations; determinant nonvanishing uses `left_ne_zero_of_mul`; removed duplicated algebraic calc. 61 → 50 declaration-block lines. |
| `exists_right_mul_isColumnHermiteNormalForm` | Uses existing `Matrix.eta_fin_two` rather than rebuilding the same matrix equality by four cases. |
| `repr_apply`, `matrix_mul_toMatrix_eq`, `reduced_eq_of_eq_add_mul` | Retained: short matrix API / remainder uniqueness applications. |
| `range_toLin_matrix_eq` | Matrix composition and `LinearEquiv.range_comp` replace a matrix-equality scaffold and a manual two-direction range witness proof. 28 → 15 lines. |
| `matrix_eq` | Extracts each needed matrix entry once, simplifies the seven equations together, then uses the same positive-divisibility and remainder argument. Removes repeated extraction/simplification at each diagonal comparison. 60 → 40 lines. |
| `bN_eq` | Retained: injectivity of coordinates is the appropriate proof and exposes its mathematical reason. |
| `index_eq_natAbs_det` | Reuses `repr_apply` directly under determinant/natAbs congruence, replacing a fresh inclusion-matrix equality proof. |
| `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` | Simplified Smith diagonal computation; retained the two content divisibilities and quotient equivalences. They are the substantive invariant argument and no matching direct mathlib result was found. |
| `quotient_isAddCyclic_iff_rankTwoContent_eq_one` | Retained direct specialization. |
| `exists_hermiteNormalForm` | Uses existing determinant/ker/injectivity equivalences directly; basis change and its matrix relation retained. |

The two largest proof reductions reuse existing facts rather than introducing more private
lemmas or hiding the same argument behind automation. No generalization is made: user asked
to preserve statements, and rank-two finite arithmetic is intrinsic to these statements.

## Laurent declaration audit

| Declaration / group | Action and reason |
|---|---|
| `zeta`, `jIntCoeff`, `transformedJSeries`, `coxPhaseAux` | Data definitions preserved; support lower-bound proof remains explicit. |
| `zeta_isPrimitiveRoot`, `jIntCoeff_neg_one`, `transformedJSeries_coeff` | Retained direct existing cyclotomic/q-expansion API or definitional equality. |
| `jIntCoeff_spec`, `coxPhase_ne_zero_aux` | Removed redundant tactic wrappers; secondary cosmetic improvement only. |
| `qParam_coxAction_aux` | Retained determinant substitution and nonzero-denominator field arithmetic. |
| `cuspFunction_coxCompose_aux`, `cuspFunction_coxAction_aux`, `cuspFunction_coxAction_eventuallyEq_aux` | Retained the q-coordinate inverse and punctured-neighborhood argument; existing API already used and no repeated large proof. |
| `cuspFunction_coxAction_meromorphicAt_aux` | Direct `MeromorphicAt.comp_analyticAt` plus germ congruence replaces temporary analytic/composition assertions. |
| `poleOrder_coxAction_aux` | Computes monomial analytic order directly, removing several intermediate function equalities. Uses `poleOrder_eq_toNat_neg_meromorphicOrderAt` instead of unfolding poleOrder and proving the sign of a WithTop coercion. 57 → 43 lines. |
| `poleRemoved_coxAction_aux` | Retained the direct q-parameter and pole-order identity. |
| `to_qExpansion_coxAction_aux` | Retained: PowerSeries expand/rescale algebra already used; the HasSum reindexing is necessary to connect the formal substitution with the analytic series. Local mathlib search found coefficient API, but no analytic HasSum substitution theorem eliminating this argument. |
| `inv_mul_pow_toNat_add_one_aux`, `coxPhase_zpow_aux` | Retained focused integer-exponent conversion, needed at the coefficient bridge. |
| `laurentqExpansion_coxAction_coeff_aux` | Uses existing `coeff_of_qExpansion` for the cutoff, and substitutes `k = r*t` immediately in the divisible branch. Reuses `Int.natCast_dvd_natCast` and `dvd_add_self_right` for the nondivisible branch. Removes custom divisibility witnesses and layered bound conversions. 95 → 46 lines. |
| `laurentqExpansion_coxAction` | Retained coefficient extensionality wrapper. |
| `reindex` | Primitive-content field now uses the directed gcd recurrence and coprime cancellation; removed a six-step gcd calc. Data fields identical. 29 → 17 lines. |
| `reindex_bijective` | Retains the modular cancellation proof; constructor equality follows directly by cases and proof irrelevance rather than nested product/Fin encoding extensionality. 33 → 27 lines. |

A separate generic monomial-substitution helper was considered but not added: the existing
`PowerSeries.expand`, rescale coefficients, and Laurent cutoff API give a shorter direct
proof here without growing a single-use abstraction.

## Search and unsuccessful trials

Local primary-source search covered PowerSeries Expand/Basic, Analytic Order, Meromorphic
Order, LaurentQExpansion, matrix ToLin/Notation, LinearMap/Submodule range, and PID Smith
normal-form APIs. Public mathematical statements were not changed, so this pass did not
introduce claims needing a new literature citation.

- `simp [Nat.gcd_rec]` was rejected after a recursion-depth failure; the final code uses a
  directed `rw` sequence and no limit increase.
- Definitional `change` from basis coordinates to `LinearMap.toMatrix` was rejected; the
  existing `repr_apply` theorem supplies the short proof correctly.
- The function passed to meromorphic composition is explicit, avoiding Lean inferring just
  multiplication by the phase rather than the entire monomial.
- Coefficients normalize casts of natural powers before substituting the divisible exponent.
  This is needed to avoid syntactically different quotient denominators.
- Whole-file `grind`, blanket terminal simp changes, and broad new generalizations were not
  used: they would obscure constructive matrix/analytic proofs or change the requested API.

## Verification and performance

Both final files passed direct Lean elaboration with zero errors and zero warnings:

```
lake env lean -Dprofiler=true -Dprofiler.threshold=100 XYin/PhD/Cox/HermiteNormalForm.lean
lake env lean -Dprofiler=true -Dprofiler.threshold=100 XYin/PhD/Cox/CoxMatrices/LaurentExpansion.lean
```

Logs are `/tmp/xyin-hnf-cleanup-profile-after.log` and
`/tmp/xyin-laurent-cleanup-profile-after.log`. Before logs use corresponding `-before.log`
paths and compile snapshots of the old source. All four commands exited 0. Earlier Laurent
checks briefly encountered a missing dependency olean while other workers refreshed caches;
this was resolved and is not counted as a source failure or a passing gate.

Single-run profiler comparison (not a statistically stable benchmark):

| File | Cumulative tactic before → after | Typeclass inference before → after |
|---|---:|---:|
| HNF | 471 → 362 ms | 661 → 601 ms |
| Laurent | 394 → 353 ms | 719 → 641 ms |

No proof exceeded one second; one final Laurent rewrite was reported at 113 ms.
`git diff --check` passes. Source scan finds no sorry/admit/new axiom/limit raise. Existing
public statements and namespaces are preserved. Parent reviews actual diffs and owns the
cumulative `lake build`; that project-wide check is separate from these direct elaboration
receipts.

Nine final-source axiom checks also passed (source copies with `#print axioms`, not older
oleans): the six public HNF construction/range/uniqueness/index/cyclic-quotient results and
`Cox.laurentqExpansion_coxAction`, `Cox.reindex`, `Cox.reindex_bijective` depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Logs:
`/tmp/xyin-hnf-cleanup-axioms.log`, `/tmp/xyin-laurent-cleanup-axioms.log`.
