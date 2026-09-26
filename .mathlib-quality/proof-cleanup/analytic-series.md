# Analytic-series proof cleanup

## Scope and baseline

Exclusive worker scope: `iteratedderivs.lean`, `eta.lean`, `Eisensteinqexpansions.lean`,
`exp_lems.lean` in `XYin/PhD/Modularforms`. Baseline snapshots are under
`/tmp/xyin-proof-cleanup-before/XYin`; the supervisor established the project baseline and
owns cumulative `lake build`. This is a proof-focused cleanup, preserving the public
statements, mathematical definitions, and mathematical documentation.

| File | Before | After | Delta |
| --- | ---: | ---: | ---: |
| iteratedderivs.lean | 169 | 72 | -97 |
| eta.lean | 172 | 81 | -91 |
| Eisensteinqexpansions.lean | 343 | 155 | -188 |
| exp_lems.lean | 36 | 29 | -7 |
| Total | 720 | 337 | -383 |

## Source-backed reuse search and mathematical changes

All four files were read in full, and every nontrivial proof was considered.

- `IteratedDeriv/WithinZpow.lean` supplies `iteratedDerivWithin_one_div`;
  `IteratedDeriv/Lemmas.lean` supplies translation and addition of iterated derivatives.
  The 63-line reciprocal derivative induction is replaced by these APIs. Rewriting
  the exponent before simplifying avoids premature integer normalization; `simp only`
  preserves the expression that `zpow_neg` needs.
- `Complex/UpperHalfPlane/Exp.lean` supplies exactly `norm_exp_two_pi_I_lt_one`.
  The project theorem is now a compatibility wrapper. The periodicity proof directly
  applies `exp_periodic.nat_mul` and checks the parameter identity with `ring`.
- `Calculus/LogDeriv.lean`, `Complex/LogDeriv.lean`, `Trigonometric/Deriv.lean`, and the
  existing `E₂_S_transform` supply the eta proof. The square-root logarithmic derivative
  is computed by the logarithmic chain rule for exp and the derivative of log; this
  replaces cancellation of several exponential factors. Composition and product
  differentiability prove the hypotheses of `logDeriv_eqOn_iff` directly.
- `EisensteinSeries/QExpansion.lean` supplies
  `summable_prod_eisSummand`, `tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow`,
  `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`, and
  `EisensteinSeries.q_expansion_riemannZeta`. The existing finite-vector/product and
  exponential/power presentations are reconciled at the theorem boundary.
- `nsmul_right_injective` and `gammaSetN_map_eq` replace the repeated choice-witness
  reconstruction in `gammaSetN_Equiv.right_inv`. Only the proof field changed;
  its `toFun`, `invFun`, and all other public data definitions are unchanged.

Searches were source-based `rg` inspections of the pinned mathlib checkout. No claim
of an independent literature or remote-search pass is made.

## Per-declaration audit and result

Proof lengths include `by`; adjacent historical comments may contribute to old counts.

| Declaration | Before | After | Disposition |
| --- | ---: | ---: | --- |
| upper_ne_int | 6 | 3 | Take imaginary parts directly |
| aut_iter_deriv | 63 | 8 | Existing higher reciprocal derivative + translation |
| aut_iter_deriv' | 7 | 2 | Substitute negative shift |
| aut_contDiffOn | 13 | 4 | Direct division API |
| iter_div_aut_add | 26 | 5 | `iteratedDerivWithin_fun_add` and the two existing formulas |
| exp_iter_deriv_within | 8 | 4 | Open-domain and exponential derivative APIs |
| eta_logDeriv_eql | 70 | 27 | Chain rule + existing E₂ transformation |
| eta_logderivs | 4 | 1 | Pointwise theorem directly |
| eta_logderivs_const | 50 | 14 | Direct differentiability compositions |
| eta_equality | 19 | 9 | Evaluate at i and cancel nonzero eta(i) |
| gammaSet_top_mem | 5 | 2 | Existing gcd and subsingleton facts |
| gammaSetN_map_eq | 6 | 6 | Retained: specification of the exact public choice construction |
| gammaSetN_eisSummand | 6 | 6 | Retained: short scalar-power algebra, no duplicate useful API found |
| gammaSetN_Equiv.right_inv | 24 | 3 | Cancel multiplication by nonzero N |
| q_exp_iden_2 | 61 | 9 | Existing Eisenstein summability and even integer summation |
| EQ0 | 5 | 3 | Existing equivalence tsum identity |
| EQ1 | 39 | 3 | Existing mathlib Fourier formula |
| EQ22 | 48 | 3 | Existing mathlib primitive-vector decomposition |
| EQ2 | 9 | 3 | Simplify `EQ22` (old count includes adjacent historical comment) |
| E_k_q_expansion | 34 | 4 | Existing normalized Eisenstein q-expansion |
| exp_upperHalfPlane_lt_one | 5 | 1 | Exact mathlib theorem |
| exp_upperHalfPlane_lt_one_nat | 5 | 5 | Retained: direct norm-exp formula and positivity already concise |
| exp_periodo | 8 | 4 | Direct periodicity application |

`standardcongruencecondition`, `E`, `gammaSetN`, `gammaSetN_map` and the data of
`GammaSet_one_Equiv` are retained. Replacing the latter by a different mathlib equivalence
would change public data; its existing integer gcd cancellation proofs remain appropriate.

## Rejected alternatives and proof hygiene

- No new single-use helpers were introduced: the correct reusable results already exist.
- A fresh induction for reciprocal derivatives was rejected in favor of the library API.
- GammaSetN cancellation retains the public equivalence construction instead of changing
  its chosen representative. No new definitions or instances were introduced.
- Direct rewriting of pointwise function products failed in the eta proof; one explicit
  definitional function equality is retained for `logDeriv_mul`.
- Unrestricted simplification of the reciprocal exponent destroyed the needed zpow shape;
  the final successful proof uses explicit exponent rewriting and `simp only`.
- The old Lean-4.29 alpha-equivalence workaround comments were removed together with the
  obsolete workaround proof, now replaced by the mathlib q-expansion theorem. Mathematical
  and normalization comments are preserved.
- Tried and retained: `simpa`, `fun_prop`, `lia`, `ring`, direct term-mode APIs, cancellation,
  positivity. No unnecessary automation chains, helper extraction, public renames, new
  axioms, sorries, or resource-limit changes were added.

## Verification

Actual commands run on all four final repository files:

```
lake env lean XYin/PhD/Modularforms/iteratedderivs.lean
lake env lean XYin/PhD/Modularforms/exp_lems.lean
lake env lean XYin/PhD/Modularforms/eta.lean
lake env lean XYin/PhD/Modularforms/Eisensteinqexpansions.lean
```

All exited 0 with no diagnostics. Logs are `/tmp/xyin-cleanup-iterated.log`,
`/tmp/xyin-cleanup-exp.log`, `/tmp/xyin-cleanup-eta.log`, and
`/tmp/xyin-cleanup-eisenstein-q.log`. Earlier failed checks were corrected before freezing.
The q-expansion file was first checked against an independent mathlib-only source copy,
then against its actual project imports once the supervisor restored dependency oleans.

A mechanical comparison found identical normalized signatures for all 28 public
lemma/theorem/def declarations. Only one definition's proof field changed, as described
above. `git diff --check` passed. Source scan found no `sorry`, `admit`, axioms,
`native_decide`, raised limits, or profiling scaffolding in these four files.

All 28 declarations were checked with `#print axioms` in proof-identical temporary source
copies. Every result uses only a subset of `propext`, `Classical.choice`, `Quot.sound`.
This includes all four eta results and every public q-expansion identity.

## Performance pass

Outcome: FAST-BOARD. Actual profiled source compilations exited 0:

```
lake env lean -Dprofiler=true -Dprofiler.threshold=100 /tmp/xyin-proof-cleanup-profile-<file>.lean
```

Logs: `/tmp/xyin-proof-cleanup-profile-{iteratedderivs,exp_lems,eta,Eisensteinqexpansions}.log`.
The first three have no reported proof operation at the 100ms threshold. The q-expansion
file reports two simp operations at 199ms and 153ms, both well below the 1000ms budget;
its cumulative tactic execution is 73.5ms and cumulative simp time 652ms. Import times
(2.47–3.61s) are dependency loading and were not treated as slow proof declarations.
No limit raises, profiling scaffolding, performance deferrals, or unmeasured performance
improvement claims are present.

## Consolidation and remaining integration gates

Proof structure/reuse was reviewed locally after all edits: no duplicate new helpers or
new API surface. Final independent simplify review and cumulative `lake build` belong to
the supervisor; this worker has not independently labeled those pending gates passed.
All four source files are frozen for those integration checks.
