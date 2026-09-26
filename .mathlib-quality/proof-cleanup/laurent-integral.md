# Laurent and integral power-series proof cleanup

Baseline: `/tmp/xyin-proof-cleanup-before/XYin`. Scope is substantive proof shortening. All 1,501 original lines and all declarations were read. Definitions, exact mathematical signatures, attributes, and documentation are preserved; redesign/generalization/renaming were out of scope.

## File accounting

- `Algebra.lean`: 451 → 439 lines; 5 of 26 lemma/theorem proofs changed. All declarations inspected.
- `LaurentQExpansion.lean`: 810 → 706 lines; 9 of 45 lemma/theorem proofs changed. All declarations inspected.
- `IntegralPowerSeries.lean`: 240 → 229 lines; 1 of 18 lemma/theorem proofs changed. All declarations inspected.

## Per-proof changes

- `shiftedLaurent_add` and `shiftedLaurent_mul`: replace elementary ring normalization inside function extensionality with explicit distributivity and multiplication identities.
- `laurentqExpansion_const`: derive the constant q-expansion directly from `qExpansion_smul` with the function argument explicitly fixed to `1`; remove a three-step equality chain.
- `laurentqExpansion_neg`: apply Laurent multiplicativity with the constant `-1`, retaining a small explicit constant-series bridge and the existing ring normalization required for efficient elaboration.
- `to_qExpansion_nat_mul`: apply analytic composition directly instead of naming a power-map proof and its transported basepoint separately.
- `meromorphicOrderAt_cuspFunction_nat_mul`: calculate the analytic order of the power map once and reuse it in the nonconstant and composition arguments.
- `poleOrder_nat_mul`: use the existing positive-part formula for pole order and mathlib's `WithTop.untopD_zero_mul`, replacing a large three-case order analysis with an integer nonnegativity split.
- `cuspFunction_qpow_mul_eq`: directly simplify the two cusp-function evaluations using the inverse q-parameter identity.
- `analyticAt_cuspFunction_iff_poleOrder_eq_zero`: reuse the existing pole-order nonnegativity lemma in the forward implication.
- `laurentqExpansion.coeff_neg_poleOrder_add` and `coeff_of_geq`: read the coefficient directly from `PowerSeries.coeff_coe`; the latter transports the nonnegative index from `natAbs` to `toNat` explicitly.
- `laurentqExpansion.ne_zero`: use its known nonzero coefficient rather than prove both factors nonzero and invoke embedding injectivity.
- `laurentqExpansion.eq_qExpansion_iff`: compare the negative-index coefficient directly, removing duplicate coefficient equations and redundant pole-removed q-expansion intermediates.
- `qExpansion_coeff_eq_circleIntegral_of_differentiableOn`: reuse the algebraic normalization already used by mathlib's `UpperHalfPlane.qExpansion_coeff_eq_circleIntegral` (QExpansion.lean:284ff), applied to the file's weaker differentiability hypothesis; remove the custom long contour-integral calculation.
- `IsIntegralPowerSeriesmod`: use `Int.modEq_zero_iff_dvd` and coefficient transport directly, removing a sign/divisibility detour and five-step scalar calculation.

The remaining short power-series closure/lift API, the substantive meromorphy descent through a power map, pole removal, and contour vanishing proofs were inspected and retained where no shorter source-backed replacement was found. No helper declarations were added. `LaurentQExpansion.lean` no longer imports Eisenstein: a complete direct check passes using only its existing mathlib imports. The supervisor still owns downstream cumulative validation of this dependency reduction.

## Verification

Final ordinary direct source checks passed, exit 0 and no diagnostics:

- `lake env lean XYin/PhD/LaurentQExpansion/Algebra.lean`: 5.82 s wall.
- `lake env lean XYin/PhD/LaurentQExpansion/LaurentQExpansion.lean`: 7.44 s wall, with Eisenstein import removed.
- `lake env lean XYin/PhD/IntegralPowerSeries/IntegralPowerSeries.lean`: 4.77 s wall.

Exact declaration headers/docblocks were compared to the baseline and preserved. Definitions and attributes remain unchanged. No `sorry`, new axioms, `native_decide`, limit increases, or source profiling scaffolding. Mathlib-only probes validated the integer positive-part multiplication identity before integrating it. Only the supervisor runs Lake builds; this worker used direct Lean and scratch files, with no repository LSP.

Two proof trials exposed costly elaboration: implicit `qExpansion_smul` hit the ordinary 200,000-heartbeat limit until its `h`/`f` arguments were supplied; directly normalizing Laurent multiplication by `-1` via a generic theorem caused another definitional-equality timeout. The final proof retains the small `ring` step from the original proof and compiles under unchanged limits. These failed candidates are absent from source.

## Paired cost measurements

Scratch copies use `-DElab.async=false -Dprofiler=true -Dprofiler.threshold=100` and `#count_heartbeats in`; copies remove comments/add wrappers while preserving attributes. The measurement wrapper stays out of source. Ordinary compiles above use the unchanged project limit. Raw files/logs: `/tmp/xyin-descent-profile/{before,after}-{Algebra,LaurentQExpansion,IntegralPowerSeries}.{lean,log}`. Wall times are not used for comparisons because imports/caches/concurrent processes vary.

| Changed proof | Before heartbeats | After heartbeats |
|---|---:|---:|
| `Algebra.shiftedLaurent_add` | 2005 | 1955 |
| `Algebra.shiftedLaurent_mul` | 1757 | 1713 |
| `Algebra.laurentqExpansion_const` | 499 | 403 |
| `Algebra.laurentqExpansion_neg` | 1855 | 1825 |
| `Algebra.to_qExpansion_nat_mul` | 1010 | 1157 |
| `LaurentQExpansion.meromorphicOrderAt_cuspFunction_nat_mul` | 5966 | 4811 |
| `LaurentQExpansion.poleOrder_nat_mul` | 2036 | 837 |
| `LaurentQExpansion.cuspFunction_qpow_mul_eq` | 596 | 154 |
| `LaurentQExpansion.analyticAt_cuspFunction_iff_poleOrder_eq_zero` | 501 | 245 |
| `LaurentQExpansion.laurentqExpansion.coeff_neg_poleOrder_add` | 790 | 700 |
| `LaurentQExpansion.laurentqExpansion.coeff_of_geq` | 904 | 523 |
| `LaurentQExpansion.laurentqExpansion.ne_zero` | 1305 | 176 |
| `LaurentQExpansion.laurentqExpansion.eq_qExpansion_iff` | 1509 | 594 |
| `LaurentQExpansion.qExpansion_coeff_eq_circleIntegral_of_differentiableOn` | 11625 | 1112 |
| `IntegralPowerSeries.IsIntegralPowerSeriesmod` | 3318 | 618 |

The analytic composition change costs an extra 147 heartbeats while reducing a redundant intermediate proof; its total remains only 1,157. All other changed proofs improve, notably the Cauchy coefficient formula (11,625 → 1,112) and divisibility descent (3,318 → 618).

## Simplify receipt

Source-backed reuse, proof structure, exact-API preservation, and cost review completed for this bounded batch. Final cumulative build, downstream import validation, and independent review remain the supervisor's integration gates.
