# Polynomial proof cleanup

Baseline: `/tmp/xyin-proof-cleanup-before/XYin`. Scope: substantive proof shortening, with definitions, exact declaration signatures, and documentation preserved. All declarations in both files were read. Design/generalization/renaming were out of scope.

## Changes

- `Interpolation.lean`: 649 → 498 lines; 10 of 31 theorem proof bodies changed.
- `Construction.lean`: 445 → 379 lines; 7 of 30 theorem proof bodies changed.
- Exact declaration header and docblock comparisons passed. No definitions changed. No new axioms, `sorry`, `native_decide`, source profiling scaffolding, or raised limits.

Interpolation uses `Lagrange.eval_nodal_derivative_eval_node_eq` (explicit new Lagrange import) to replace custom root-product differentiation. Recovery applies the numerator/denominator product identities directly. `Finset.sum_equiv`/`prod_equiv` replace nested reindexing calculations. Direct analytic coefficient results simplify meromorphic closure, and direct degree and rational-function identities remove redundant equations.

Construction uses `Polynomial.Bivariate.aevalAeval_swap`, coefficient extensionality for map/swap, `Equiv.prod_comp` for Cox reindexing, `Polynomial.Monic.as_sum` for candidate specialization, and `Monic.natDegree_map` for degree preservation. The symmetric-sum MDifferentiable proof was inspected and retained: no already-available generic analytic coefficient API was found, and the finite-product argument is needed.

## Verification

Ordinary direct source compiles completed exit 0, no diagnostics:

- `lake env lean XYin/PhD/Cox/ModularPolynomial/Interpolation.lean`: 6.16 s wall.
- `lake env lean XYin/PhD/Cox/ModularPolynomial/Construction.lean`: 7.28 s wall.

Standalone probes validated the reused polynomial APIs. Repository LSP was discontinued after its auto-build behavior interfered with dependency restoration. The supervisor owns cumulative builds and independent review; these direct checks do not imply the cumulative build is finished.

Paired scratch copies were compiled with `-DElab.async=false -Dprofiler=true -Dprofiler.threshold=100` and mathlib's `#count_heartbeats in` wrapper. Scratch copies remove comments and insert command wrappers while preserving attributes. Its internal measurement option is confined to scratch; ordinary source compilation above passed without raised limits. Logs/sources: `/tmp/xyin-polynomial-profile/{before,after}-{interpolation,construction}.{lean,log}`. Wall times are not compared because imports/cache state and concurrent work dominate.

| Changed theorem | Before heartbeats | After heartbeats |
|---|---:|---:|
| `Interpolation.interpolationAt_eq_cosets_aux` | 1402 | 1449 |
| `Interpolation.interpolationAtCosets_smul_aux` | 9369 | 2433 |
| `Interpolation.polynomial_prod_coeff_mdifferentiable_aux` | 1348 | 1086 |
| `Interpolation.interpolation_coeff_meromorphicOnH_aux` | 1629 | 727 |
| `Interpolation.eval_derivative_prod_X_sub_C_at` | 2989 | 1406 |
| `Interpolation.eval_interpolation_sum_at` | 2772 | 2333 |
| `Interpolation.recoveryFormula` | 3773 | 597 |
| `Interpolation.interpolationAt_natDegree_lt` | 1656 | 1062 |
| `Interpolation.modularDerivativeHolomorphic_apply` | 2517 | 1436 |
| `Interpolation.rationalInTwo_of_interpolation_coeff_rational` | 507 | 260 |
| `Construction.BivariatePolynomial.eval_swap` | 164 | 136 |
| `Construction.BivariatePolynomial.map_swap` | 3804 | 344 |
| `Construction.BivariatePolynomial.diagonal_swap` | 1907 | 1754 |
| `Construction.coxPhiAtJ_eq_rightCosetProduct` | 1330 | 277 |
| `Construction.coxPhiAtJ_sl2_smul` | 4947 | 2256 |
| `Construction.modularPolynomialCandidateAux_specializeY` | 1641 | 1394 |
| `Construction.modularPolynomialC_natDegree` | 174 | 93 |

The reindexing change from 1,402 to 1,449 adds only 47 heartbeats while making the argument substantially more direct. Other changed proofs improve. No changed proof approaches the standard heartbeat limit. An initial candidate with unrestricted `congr 1` in coset equivariance hit 200,000 heartbeats and was replaced with explicit `congrArg₂`/`congrArg`. Failed scratch syntax experiments were discarded before paired measurements; no scaffolding remains in source.

## Simplify receipt

- Reuse: source-backed nodal, evaluation, monic and reindexing APIs replace bespoke arguments.
- Structure: intermediate equalities and nested calculations removed; necessary quotient and analytic arguments retained.
- Quality: mathematical declarations and documentation preserved; no unrelated edits.
- Efficiency: ordinary compiles passed; heartbeat costs recorded and the one immaterial increase explained.
- Pending: supervisor cumulative build and final independent review.
