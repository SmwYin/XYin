# Reciprocal and Fourier summability proof cleanup

## Scope and baseline

Worker-owned files `XYin/PhD/Modularforms/Summability/{Reciprocal,QExpansion}.lean`.
The supervisor's baseline is `/tmp/xyin-proof-cleanup-before/XYin`.
Both files were read in full and every nontrivial proof was assessed.

| File | Before | After | Reduction |
| --- | ---: | ---: | ---: |
| Reciprocal.lean | 688 | 297 | 391 |
| QExpansion.lean | 748 | 296 | 452 |
| Total | 1436 | 593 | 843 |

## Source-backed mathematical changes

- `EisensteinSeries/E2/Summable.lean` provides
  `summable_left_one_div_linear_sub_one_div_linear`, replacing the separate rational
  denominator argument for `summable_pain` and positive/negative integer splitting for
  `summable_diff_right`. The natural-index theorem is its restriction.
- `EisensteinSeries/Summable.lean` provides `linear_right_summable`,
  `summable_linear_left_mul_linear_left`, `isBigO_linear_add_const_vec`, and
  `summable_of_isBigO_rpow_norm`. These replace the hand-built asymptotics of shifted
  reciprocals, powers, and the two-dimensional cubic correction series.
- `Trigonometric/Cotangent.lean` provides `summable_cotTerm` for all complex numbers
  outside the integers. This removes `summable_diff`'s unnecessary upper/lower-half-plane
  case split. The upper-half-plane instance is just a specialization.
- `r_mul_max_le` and `norm_le_pi_norm` prove the reciprocal square estimate without
  separating zero denominators. The fixed-coordinate lattice majorant only excludes
  zero in the comparison variable, instead of excluding an interval and proving exact
  eventual equality of the vector norm with a coordinate norm.
- `Summable.tsum_prod` and `Summable.tsum_comm` use the already available product
  summability to avoid reproving every fiber's summability. The finite-support delta
  correction uses cofinite equality, preserving the exact public definition of delta.
- `Monotone.map_max`, `le_mul_inv_iff₀`, and `div_le_iff₀` replace ad hoc power/max
  and reciprocal inequalities. The unused positivity requirement and the single-use
  private `aux` disappear; no new helper declaration replaces it.
- `EisensteinSeries/QExpansion.lean` provides
  `iteratedDerivWithin_tsum_cexp_eq`, `contDiffOn_tsum_cexp`, and
  `qExpansion_identity_pnat`. These replace the exponential derivative induction,
  a repeated smoothness argument, and the main q-expansion scalar-cancellation proof.
- `Trigonometric/Cotangent.lean` provides local uniform summability and differentiability
  of the iterated cotangent summands, so the reciprocal derivative interchange uses
  `iteratedDerivWithin_tsum` directly. Reciprocal-series smoothness follows from its
  equality with cotangent minus the inverse, and its full integer derivative series
  is exactly `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow`.
- `summable_pow_mul_geometric_of_norm_lt_one` and
  `tsum_prod_pow_eq_tsum_sigma` replace the expanded norm manipulation and repeated
  product/Fubini arguments. Compact majorants use `Real.summable_nat_pow_inv` directly;
  the empty compact-set case was unnecessary.
- The existing `sub_bound` and `add_bound` now normalize the existing mathlib vertical
  strip estimate directly. `Real.rpow_neg_natCast` performs this conversion without
  inventing extra nonnegativity hypotheses or forcing a fresh estimate.

All searches inspected the pinned local mathlib sources with `rg` and source reads.

## Declaration audit

All 60 public theorem/lemma/definition signatures are byte-equivalent after whitespace
normalization. Definitions, including `δ`, are unchanged. The only removed declaration
is the private, single-use, redundantly constrained `aux` described above.
Proof-line figures omit blank lines; surrounding comments/attributes can affect old counts.

| Declaration | Before proof lines | After proof lines |
| --- | ---: | ---: |
| `upp_half_not_ints` | 3 | 2 |
| `aus` | 3 | 2 |
| `pnat_inv_sub_squares` | 15 | 8 |
| `upper_half_plane_ne_int_pow_two` | 13 | 4 |
| `upbnd` | 26 | 12 |
| `lhs_summable` | 30 | 3 |
| `neg_div_neg_aux` | 2 | 2 |
| `summable_diff` | 33 | 8 |
| `arg1` | 1 | 1 |
| `sum_int_pnat3` | 17 | 8 |
| `pow_max` | 11 | 2 |
| `extracted_abs_norm_summable` | 42 | 15 |
| `summable_hammerTime_nat` | 6 | 3 |
| `summable_diff_denom` | 19 | 3 |
| `summable_pain` | 24 | 2 |
| `vector_norm_bound` | 55 | 24 |
| `G_2_alt_summable` | 52 | 5 |
| `δ` | 1 | 1 |
| `δ_eq` | 1 | 1 |
| `δ_eq2` | 1 | 1 |
| `δ_neq` | 2 | 2 |
| `G_2_alt_summable_δ` | 25 | 14 |
| `G2_prod_summable1` | 5 | 5 |
| `G2_prod_summable1_δ` | 5 | 5 |
| `G2_alt_indexing_δ` | 15 | 3 |
| `G2_alt_indexing2_δ` | 25 | 6 |
| `summable_1` | 26 | 4 |
| `summable_2` | 16 | 4 |
| `summable_3` | 20 | 7 |
| `G2_summable_aux` | 6 | 3 |
| `auxf` | 2 | 2 |
| `summable_diff_right_a` | 8 | 3 |
| `summable_diff_right` | 11 | 2 |
| `sum_int_pnatt` | 27 | 27 |
| `sum_int_pnat2_pnat` | 3 | 3 |
| `summable_iter_derv'` | 21 | 4 |
| `exp_series_ite_deriv_uexp2` | 39 | 3 |
| `exp_series_ite_deriv_uexp''` | 5 | 3 |
| `exp_series_ite_deriv_uexp'''` | 3 | 2 |
| `tsum_uexp_contDiffOn` | 31 | 3 |
| `iter_der_within_add` | 14 | 6 |
| `iter_exp_eqOn` | 3 | 2 |
| `summable_iter_aut` | 19 | 4 |
| `sub_bound` | 27 | 11 |
| `add_bound` | 28 | 11 |
| `aut_bound_on_comp` | 39 | 19 |
| `diff_on_aux` | 6 | 6 |
| `diff_at_aux` | 9 | 5 |
| `aut_series_ite_deriv_uexp2` | 48 | 16 |
| `tsum_ider_der_eq` | 5 | 2 |
| `auxp_series_ite_deriv_uexp'''` | 7 | 2 |
| `tsum_aexp_contDiffOn` | 50 | 10 |
| `aux_iter_der_tsum` | 54 | 5 |
| `aux_iter_der_tsum_eqOn` | 9 | 4 |
| `pos_sum_eq` | 11 | 4 |
| `cot_series_repr` | 7 | 3 |
| `EisensteinSeries_Identity` | 5 | 2 |
| `q_exp_iden''` | 24 | 9 |
| `q_exp_iden` | 70 | 4 |
| `t9` | 49 | 11 |

## Rejected approaches and helper hygiene

- No new public or private helper APIs were needed. Existing mathlib supplies the useful
  abstraction boundaries; this avoids retaining homemade smooth-series machinery.
- A shorter `sum_int_pnatt` proof using direct subtype congruence produced opaque cast
  normalization goals under the module system. The existing explicit restriction proof
  is retained instead of adding cast helpers solely for this one use.
- General simplification with `mul_inv_rev` plus reassociation was expensive in a scalar
  summability expression. The final proof normalizes once with `simp only` and applies
  the real p-series summability theorem directly.
- The vertical-strip estimate's real exponent is converted using
  `Real.rpow_neg_natCast`; `Real.rpow_neg` alone requires extra side conditions and was
  not a useful simplification in this context.
- Applied direct `exact`/`simpa`, `omega`, `ring`, `field_simp`, norm inequalities,
  cofinite congruence, `Summable` restriction, and existing derivative APIs. No new
  sorries/axioms, resource-limit changes, opaque helper axioms, or `native_decide`.

## Verification

`lake env lean XYin/PhD/Modularforms/Summability/Reciprocal.lean` exited 0 with no
warnings/errors; log `/tmp/xyin-cleanup-reciprocal.log`.
The first direct QExpansion pass against existing dependencies validated all but the
subsequently repaired norm estimates. Once the supervisor's failed intermediate build
removed the Reciprocal olean, a proof-identical temporary combined module compiled both
final files together, exit 0/no diagnostics:

```
lake env lean /tmp/xyin-summability-combined.lean
```

Log `/tmp/xyin-summability-combined.log`. After the supervisor restored the Reciprocal
olean, the actual `lake env lean XYin/PhD/Modularforms/Summability/QExpansion.lean`
command also exited 0 with no diagnostics; log `/tmp/xyin-cleanup-summability-q.log`.
The final subsequent edits only wrapped three long lines, preserving proof terms.
The supervisor owns the cumulative build gate.

Profiler/axiom command:

```
lake env lean -Dprofiler=true -Dprofiler.threshold=100 /tmp/xyin-summability-profile-axioms.lean
```

Log `/tmp/xyin-summability-profile-axioms.log` (results appended below).
Final source scanning found no `sorry`, `admit`, `axiom`, `native_decide`, resource-limit
settings, or profiling scaffolding in either file.

Independent simplify review and cumulative `lake build` are the supervisor's remaining
gates. Both source files are frozen for integration.

Final performance/axiom result: the command exited 0. All 60 public declarations use
only a subset of `propext`, `Classical.choice`, and `Quot.sound`. The only reported
individual proof operation at the 100 ms threshold is `simp took 122ms`; no operation
crosses the 1000 ms optimization budget. Aggregate simp time is 2.04s across 60
public declarations; imports account for 3.97s and are not declaration-proof costs.
No performance limitation was worked around by raising a resource limit.
