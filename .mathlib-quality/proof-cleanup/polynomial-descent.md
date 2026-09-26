# Polynomial descent and diagonal proof cleanup

Baseline: `/tmp/xyin-proof-cleanup-before/XYin`. Scope: proof-focused shortening with definitions, exact signatures, and documentation preserved. All declarations in all four files were read. Definition redesign, generalization, renaming, and unrelated cosmetic rewrites were out of scope.

## File accounting

- `AnalyticSupport.lean`: 106 → 96 lines; 2 of 5 theorem/lemma proofs changed, all declarations inspected.
- `IntegralDescent.lean`: 372 → 305 lines; 5 retained proofs changed and 2 unused private proofs removed, from 22 original proofs, all declarations inspected.
- `Irreducibility.lean`: 158 → 141 lines; 3 of 9 theorem/lemma proofs changed, all declarations inspected.
- `DiagonalLaurent.lean`: 370 → 293 lines; 7 retained proofs changed and 1 unused private proof removed, from 20 original proofs, all declarations inspected.

## Changes and source-backed reuse

- Analytic support: `coxLinearFactor_coeff_cuspMeromorphicAt` uses the existing `meromorphicAt_cuspFunction_mul` instead of reproducing its punctured-neighborhood proof. The finite-product coefficient base case uses `Polynomial.coeff_one` directly.
- Integral descent: `laurentqExpansion_polynomialIn_j_aux` composes the Laurent addition/multiplication identities with polynomial evaluation directly. `eval₂_laurentqExpansion_j_coeff_neg_natDegree_aux` now applies the existing `Cox.polynomial_eval₂_laurentSeries_coeff` with width one; its power-order and power-leading-coefficient wrappers use the corresponding general Laurent helpers. Integer constants use root-level `intCast_mem`; erasing the lead uses `Polynomial.self_sub_monomial_natDegree_leadingCoeff`; bivariate lifts use `Polynomial.mem_lifts` and `lifts_iff_coeff_lifts` without requesting unused support data.
- Irreducibility: `modularPolynomialFunctionField_eq_map` compares coefficients directly; `minpoly_aeval_rightCosetRoot` simplifies the existing algebra-hom root identity directly; the cardinal bound removes a temporary mapped polynomial and its repeated degree/monic facts, preserving the same root-count argument.
- Diagonal Laurent: `transformedJSeries_order` compares ordinary orders using a nonzero coefficient, avoiding an orderTop/coercion round-trip. `cox_diagonal_factor_leadingCoeff_pow` uses `Even.neg_pow` and `pow_mul`. Polynomial evaluation is shortened in parallel with descent. Its extreme coefficient and the power order/leading-coefficient wrappers now use the existing general lemmas from `Cox/LaurentPolynomialEvaluation.lean` at width `m`. Both affected files add explicit imports of that mathlib-only module, with no import cycle and no changes to the general module. The leading coefficient is read directly from `orderTop`, and the product power statement uses `Finset.prod_induction` with an explicit predicate instead of a bespoke Finset induction helper.

The Hasse strong induction and local integer-coefficient subring definition were inspected and retained. No direct existing API removes the mathematical need for descending the leading coefficient. Existing short quotient/evaluation, holomorphic, and integral-descent wrapper proofs remain unchanged. No new helper declarations were necessary.

## Verification

All four ordinary direct source compiles passed with exit 0 and no diagnostics on their worker-handoff revisions, before the supervisor's subsequent removal of three unused private wrappers:

| File | Command | Wall time |
|---|---|---:|
| AnalyticSupport | `lake env lean XYin/PhD/Cox/ModularPolynomial/AnalyticSupport.lean` | 31.51 s |
| IntegralDescent | `lake env lean XYin/PhD/Cox/ModularPolynomial/IntegralDescent.lean` | 9.59 s |
| Irreducibility | `lake env lean XYin/PhD/Cox/ModularPolynomial/Irreducibility.lean` | 7.26 s |
| DiagonalLaurent | `lake env lean XYin/PhD/Cox/DiagonalLaurent.lean` | 9.21 s |

The long AnalyticSupport wall time occurred during concurrent dependency work (user 1.83 s, system 2.63 s); it is not a performance regression measurement. Transient missing Delta/Reciprocal object-file errors were resolved by the supervising agent's serialized dependency rebuild, without worker Lake builds or LSP. A deprecated `coeff_order_ne_zero` trial was replaced by `coeff_order_eq_zero.not.mpr`; no new warning remains.

Exact declaration-header/docblock checks passed at worker handoff. The supervisor subsequently removed three unused private declarations after independent review; all retained declaration signatures and documentation are unchanged. Definitions and attributes were preserved. No `sorry`, new axiom, `native_decide`, limit increase, or source profiling scaffold was introduced. The supervisor owns the cumulative build and independent review.

## Paired proof-cost measurements

Baseline/current scratch copies were compiled with `-DElab.async=false -Dprofiler=true -Dprofiler.threshold=100` and `#count_heartbeats in` wrappers. Scratch copies only remove comments/add wrappers; attributes remain intact. Ordinary source checks above passed with unchanged limits. Raw sources/logs: `/tmp/xyin-descent-profile/{before,after}-{AnalyticSupport,IntegralDescent,Irreducibility,DiagonalLaurent}.{lean,log}`. Wall times are not compared because cache/import/concurrent-process effects dominate.

| Changed proof | Before heartbeats | After heartbeats |
|---|---:|---:|
| `AnalyticSupport.coxLinearFactor_coeff_cuspMeromorphicAt` | 1341 | 1117 |
| `AnalyticSupport.polynomial_prod_coeff_cuspMeromorphicAt` | 683 | 613 |
| `IntegralDescent.laurentqExpansion_polynomialIn_j_aux` | 2258 | 1288 |
| `IntegralDescent.laurentqExpansion_j_pow_order_aux` | 376 | 572 |
| `IntegralDescent.laurentqExpansion_j_pow_leadingCoeff_aux` | 309 | 208 |
| `IntegralDescent.eval₂_laurentqExpansion_j_coeff_neg_natDegree_aux` | 4415 | 640 |
| `IntegralDescent.intCast_C_mem_integerCoeffLaurentSeries` | 883 | 452 |
| `IntegralDescent.eraseLead_integer_laurent_aux` | 2195 | 2058 |
| `IntegralDescent.bivariate_exists_of_coeff_lifts` | 228 | 106 |
| `Irreducibility.modularPolynomialFunctionField_eq_map` | 2202 | 1039 |
| `Irreducibility.minpoly_aeval_rightCosetRoot` | 1410 | 1374 |
| `Irreducibility.card_le_minpoly_natDegree_of_injective_roots` | 937 | 915 |
| `DiagonalLaurent.transformedJSeries_order` | 1480 | 519 |
| `DiagonalLaurent.cox_diagonal_factor_leadingCoeff_pow` | 794 | 506 |
| `DiagonalLaurent.laurentqExpansion_polynomialIn_j_widthM` | 2500 | 1432 |
| `DiagonalLaurent.laurentqExpansion_j_pow_order_widthM` | 489 | 308 |
| `DiagonalLaurent.laurentqExpansion_j_pow_leadingCoeff_widthM` | 417 | 224 |
| `DiagonalLaurent.eval₂_laurentqExpansion_j_coeff_widthM` | 5321 | 476 |
| `DiagonalLaurent.eval₂_laurentqExpansion_j_leadingCoeff_widthM` | 1114 | 1012 |
| `DiagonalLaurent.diagonal_cox_product_leadingCoeff_pow` | 1560 | 624 |

Changed-proof measurements are recorded above, including the six wrappers as checked at worker handoff. The supervisor later removed the now-unused `IntegralDescent.laurentqExpansion_j_pow_order_aux`, `IntegralDescent.laurentqExpansion_j_pow_leadingCoeff_aux`, and `DiagonalLaurent.laurentqExpansion_j_pow_leadingCoeff_widthM`; their rows remain historical measurements of the checked intermediate revision. The two coefficient wrappers and the width-`m` order wrapper remain. The width-one power-order wrapper costs an extra 196 heartbeats (376 → 572) for specialization of the shared theorem; that declaration was subsequently removed as unused. All other changed proofs improve. The supervisor identified the shared Laurent coefficient API during independent review; the duplicated coefficient proofs and four power wrappers were subsequently replaced and recompiled successfully. Mathlib-only probes independently checked subring integer membership, polynomial lifting, even powers, leading-coefficient extraction, and finite-product induction. The initial implicit `Finset.prod_induction` failed to infer its property; the final source supplies that predicate explicitly.

## Simplify receipt

Reuse, proof structure, source cleanliness, and cost review are complete for this bounded worker batch. Existing public APIs and documentation are preserved; the three private removals are recorded above. Cumulative build and independent review remain the supervisor's final integration gates.
