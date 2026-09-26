# j-function proof cleanup

Baseline: `/tmp/xyin-proof-cleanup-before/XYin`. All 1,151 original lines and all declarations in the three assigned files were read. Scope is substantive proof simplification. Existing declaration headers, definitions, attributes, and documentation are unchanged. The supervisor requested one documented shared `j_mdifferentiable` lemma after identifying three copies of its quotient proof. Definition redesign/generalization and unrelated style rewrites were out of scope.

## File accounting

- `Deltaqexpansions.lean`: 337 → 300 lines; 8 of 33 existing proofs changed.
- `jfunction.lean`: 602 → 504 lines; 12 of 59 existing proofs changed; one documented shared lemma added.
- `jLevelN.lean`: 212 → 193 lines; 2 of 12 existing proofs changed.

## Per-proof changes

Deltaqexpansions:

- `E4_qExpansion_coeff_aux`, `E6_qExpansion_coeff_aux`: normalize the Bernoulli coefficient formula once instead of separately proving the zero and nonzero coefficient branches.
- `coeff_mul_dvd_aux`: use `Finset.dvd_sum` and `mul_dvd_mul` directly, eliminating explicit divisibility witnesses and ring normalization.
- `eisenstein_difference_modEq_linear_aux`: apply the coefficient additive hom to the existing polynomial identity with `map_sub`/`map_neg`, eliminating a separate coefficient identity.
- `linear_coeff_eq_aux`: recognize numeral multiplication as `PowerSeries.C` multiplication and apply `coeff_C_mul` directly, removing the auxiliary coefficient bridges.
- `eisenstein_difference_coeff_dvd_aux`: use `mul_dvd_mul_left` directly instead of constructing and normalizing a divisibility witness.
- `map_integralE4_pow_three_sub_integralE6_pow_two`: map subtraction/powers first and apply the existing modular-form q-expansion subtraction law to the two bundled products, removing the function equality bridge chain.
- `Delta_qExpansion_eq_smul_eisenstein_difference`: replace the final scalar q-expansion equality chain with its direct rewrite.

jfunction:

- `j_slash_invariant`: bundle `E4³` as a weight-twelve form, apply `div_slash_SL2`, and reuse the two slash-invariance proofs. This removes explicit denominator powers, inverses, and repeated ring normalization.
- `deltaOverQ_ne_zero`: use the already proved quotient/product formula and nonvanishing of each factor.
- `E4_pow_three_mul_qOverDelta_eq_qj`: simplify the inverse product and normalize the resulting elementary product, removing unnecessary nonzero hypotheses and an intermediate quotient identity.
- `qOverDelta_isIntegralPowerSeries_aux`: map the integral unit and use `Units.inv_eq_of_mul_eq_one_right`, removing a hand-written uniqueness-of-inverse calculation.
- `qj_vadd_one_aux`: directly simplify the translated exponential using `Complex.exp_add` and its known period after the modular-form periodicity equations.
- `qj_periodic`: reuse the established upper-half-plane translation equality directly, removing a redundant intermediate calculation.
- `qj_differentiableAt_of_im_pos`: compose `Complex.differentiable_exp` with `UpperHalfPlane.mdifferentiable_coe`, multiply by `j_mdifferentiable`, and use `mdifferentiableAt_iff`. No manual neighborhood comparison is needed.
- `qj_isBoundedAtImInfty`: rewrite by the existing product identity and apply the product bound directly.
- `qjCoeffs_tsum_div_qParam_aux`: split off the zero summand, distribute division through the sum, and simplify `pow_succ`; this replaces the long four-step series calculation.
- `qj_qExpansion_coeff_zero`: work with the constant-coefficient ring hom, so multiplicativity/powers are automatic and duplicate coefficient identities disappear.
- `j_poleOrder`: apply the inverse-order formula to `id` directly and use multiplication commutativity at function type.
- `j_laurentQExpansion_isIntegral`: directly rewrite the Laurent coefficient through the pole-removed q-expansion and use the coefficient cast lemma.
- New `j_mdifferentiable`: the existing quotient proof is now shared by `qj` and level-`N` differentiability. The supervisor also changed the existing qualified `ModularFunction.j_mdifferentiable` to a wrapper, preserving that API.

jLevelN:

- `qjN_isBoundedAtImInfty_aux`: directly compose the imaginary-part projection with positive constant multiplication; eliminate a separately proved function equality.
- `jN_differentiableAt`: use shared `j_mdifferentiable`, compose by scalar multiplication, and reuse `natCast_mul_ofComplex_coe_aux` for the neighborhood comparison. Repeated E4/Delta differentiability and denominator-nonzero subproofs are removed.

All remaining proofs were inspected. In particular, the discriminant divisibility arguments, shifted q-series analyticity from a power series, and level-N cusp-parameter calculation were retained where their mathematical work was still necessary. Existing short transport/closure lemmas were left alone. `qexp_coeffs` and `jInvariantLink` were outside this batch, as directed by the supervisor.

## Verification

Final ordinary direct checks pass with exit 0 and no diagnostics:

- `lake env lean XYin/PhD/jFunction/Deltaqexpansions.lean`: 6.19 s wall.
- `lake env lean XYin/PhD/jFunction/jfunction.lean`: 11.47 s wall during profiling/build overlap.
- `lake env lean XYin/PhD/jFunction/jLevelN.lean`: 6.70 s wall after the updated jfunction object was available.

Existing declaration headers, all definitions, attributes, and original docblocks were compared to the baseline and match exactly. Only the shared holomorphy lemma/documentation is new. `git diff --check` passes. No `sorry`, new axiom, `native_decide`, raised limits, or source profiling scaffolding. This worker used direct Lean and scratch files only; the supervisor owns the full Lake build and final axiom scan.

## Paired proof-cost measurements

Scratch copies use `-DElab.async=false -Dprofiler=true -Dprofiler.threshold=100` and `#count_heartbeats in`. Measurement wrappers stay out of source; normal checks retain the ordinary project limits. Raw files/logs: `/tmp/xyin-descent-profile/{before,after}-{Deltaqexpansions,jfunction,jLevelN}.{lean,log}`. Wall-clock times are not treated as performance comparisons because concurrent compilation and import caches vary.

| Changed proof | Before heartbeats | After heartbeats |
|---|---:|---:|
| `Deltaqexpansions.E4_qExpansion_coeff_aux` | 1109 | 1005 |
| `Deltaqexpansions.E6_qExpansion_coeff_aux` | 1089 | 995 |
| `Deltaqexpansions.coeff_mul_dvd_aux` | 443 | 355 |
| `Deltaqexpansions.eisenstein_difference_modEq_linear_aux` | 3735 | 1639 |
| `Deltaqexpansions.linear_coeff_eq_aux` | 3998 | 1617 |
| `Deltaqexpansions.eisenstein_difference_coeff_dvd_aux` | 557 | 522 |
| `Deltaqexpansions.map_integralE4_pow_three_sub_integralE6_pow_two` | 6114 | 4402 |
| `Deltaqexpansions.Delta_qExpansion_eq_smul_eisenstein_difference` | 2781 | 2609 |
| `jfunction.j_slash_invariant` | 4871 | 2424 |
| `jfunction.deltaOverQ_ne_zero` | 524 | 198 |
| `jfunction.E4_pow_three_mul_qOverDelta_eq_qj` | 2301 | 860 |
| `jfunction.qOverDelta_isIntegralPowerSeries_aux` | 1415 | 493 |
| `jfunction.qj_vadd_one_aux` | 1793 | 854 |
| `jfunction.qj_periodic` | 614 | 557 |
| `jfunction.qj_differentiableAt_of_im_pos` | 2536 | 1161 |
| `jfunction.qj_isBoundedAtImInfty` | 609 | 228 |
| `jfunction.qjCoeffs_tsum_div_qParam_aux` | 3212 | 1355 |
| `jfunction.qj_qExpansion_coeff_zero` | 5354 | 2404 |
| `jfunction.j_poleOrder` | 1485 | 1023 |
| `jfunction.j_laurentQExpansion_isIntegral` | 881 | 358 |
| `jfunction.j_mdifferentiable` (new shared lemma) | — | 748 |
| `jLevelN.qjN_isBoundedAtImInfty_aux` | 355 | 222 |
| `jLevelN.jN_differentiableAt` | 2509 | 5072 |

The broad AC-simplification trial for `E4_pow_three_mul_qOverDelta_eq_qj` used 8,400 heartbeats versus 2,301 before cleanup. Narrowing the simplifier and keeping explicit algebra normalization reduced the final proof to 860. Similarly, direct fixed-constant divisibility avoids an unnecessary general simplifier invocation. The table includes the one-time cost of the new shared holomorphy lemma, rather than hiding it inside its shorter callers. `jN_differentiableAt` is the one cost tradeoff: 2,509 → 5,072 heartbeats, still well below the unchanged project limit. Its source shrinks substantially and now shares the holomorphy proof with both other callers; the extra 2,563 heartbeats is explicitly retained as the cost of that shorter, shared structure. Every other changed proof in this batch uses fewer heartbeats.

## Simplify receipt

Source-backed API reuse, full-file inspection, unchanged mathematical contracts, proof structure, and paired elaboration cost were checked. The supervisor reviewed the actual diffs and requested the shared holomorphy extraction. The supervisor reports independent review complete with no unresolved findings and the unified build already past these three modules. Completion of the full integration build and latest axiom scan remain the supervisor's gates.
