# Independent review of the broader proof-shortening pass

Reviewed on 2026-09-21 by the `final_proof_shortening_review` agent. Lean sources were read-only
throughout this review. The comparison baseline was `/tmp/xyin-proof-cleanup-before/XYin`,
which includes the previously completed modular-function migration and structural cleanup;
this review does not mistake that earlier work for this pass's changes.

**Result: no unresolved findings.** Five minor redundancy findings were reported to the
coordinator, removed, and checked again in the final sources. No correctness, public-API,
definition-data, documentation, or source-level trust regression was found.

## Scope and method

- Inspected changed statements and proof bodies in all 56 changed Lean files. Read the full
  diffs for all 21 root-owned files listed in `/tmp/xyin-root-files.json`, the field-of-functions
  files, shared Cox Laurent APIs and their callers, Cox matrix/classification changes,
  `DimensionFormulas`, `ResToImagAxis`, and the final three-file `j` holomorphy consolidation.
  The remaining files were reviewed using changed-body/context views and source audits.
- Compared declaration signatures after stripping comments and whitespace. The lexical
  comparison finds **zero changed signatures**. Its limitations are addressed by manually
  inspecting the changed definition bodies and surrounding declarations.
- Inspected deleted comments and documentation. Deletions are obsolete failed-proof attempts
  or implementation commentary tied to superseded proofs. The mathematical explanation of
  the Fourier decay estimate in `ResToImagAxis` remains beside its shorter replacement.
- Scanned added source lines for `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
  `set_option`, `implemented_by`, and `extern`: **no additions**.
- Checked private-helper references and attributes after the shared-API replacements.

The complete reviewed-file list and SHA-256 hashes of the frozen sources are recorded in
[`independent-review-source-audit.json`](independent-review-source-audit.json).

## Resolved findings

These private wrappers lost their last caller when longer coefficient/span proofs were
replaced with shared APIs. They had no automation attributes and therefore served no
remaining purpose:

| Severity | File | Removed declaration |
| --- | --- | --- |
| P3 | `Cox/CyclicSublattice.lean` | `coe_carrier_add` |
| P3 | `Cox/CyclicSublattice.lean` | `coe_carrier_zsmul` |
| P3 | `Cox/DiagonalLaurent.lean` | `laurentqExpansion_j_pow_leadingCoeff_widthM` |
| P3 | `Cox/ModularPolynomial/IntegralDescent.lean` | `laurentqExpansion_j_pow_order_aux` |
| P3 | `Cox/ModularPolynomial/IntegralDescent.lean` | `laurentqExpansion_j_pow_leadingCoeff_aux` |

The width-`m` order wrapper in `DiagonalLaurent` remains used and was correctly retained.
`CyclicSublattice.hermite_repr_apply` has a `[simp]` attribute and remains useful despite
having no explicit textual caller; it too was correctly retained. The sixth removed
declaration in the source audit, `Summability/Reciprocal.aux`, was an already redundant
private helper removed by the implementation pass.

## Definitions and proof organization

The changed bodies of the following eight definitions alter only proof fields or proof
arguments; their mathematical data and executable maps are preserved:

- `CoxMatrices/Basic`: `act`, `rightCosetTranslate`, `rightCosetMul`.
- `CoxMatrices/LaurentExpansion`: `reindex`.
- `CyclicSublattice/Classification`: `toCoxMatrix`, `inclusionHermiteNormalForm`.
- `Modularforms/DimensionFormulas`: `CuspForms_iso_Modforms`.
- `Modularforms/Eisensteinqexpansions`: `gammaSetN_Equiv`.

The new shared helpers have actual callers. In particular, the generic Laurent coefficient
lemma replaces the two specialized leading-term arguments; the imaginary-axis helpers
replace repeated unfolding in realness/positivity proofs; and the limit-of-arguments helper
supports both index filters. The final global `j_mdifferentiable` lives next to the definition
of `j`, supports `qj` and `jN`, and retains the existing qualified
`ModularFunction.j_mdifferentiable` wrapper for compatibility. The final
`E4_pow_three_mul_qOverDelta_eq_qj` uses explicit `simp only` followed by `ring`, avoiding the
temporary broad AC simplification noted during implementation.

The completed `E4E6_coeff_zero_eq_zero` proof uses analyticity and the q-expansion
smul/sub/pow APIs. Its theorem statement and the data of `Delta_E4_E6_aux` are unchanged.
The dimension-formula replacements invoke mathlib's level-one rank theorems with explicit
transport of the determinant-one subgroup instance; they do not weaken the original claims.

## Verification boundary

This was an independent source review, not a second concurrent build. No build or Lean
environment was reset by this reviewer. The coordinator owns the cumulative `lake build`,
profiling evidence, and compiled axiom audit. Source-level absence of new trust mechanisms
is not claimed to replace those final checks, and pre-existing project warnings or the
remaining general-level dimension `sorry` are not claimed to be eliminated by this review.
