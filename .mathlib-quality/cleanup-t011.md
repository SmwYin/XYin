# Cleanup record: T011

## Baseline and scope

- Target: `levelOne_exists_polynomial_clearing_poles` in
  `XYin/PhD/Cox/ModularFunction.lean`.
- The construction now clears every finite upper-half-plane singularity orbit by a nonzero
  polynomial in `j`.
- Focused and full-repository `lake build` both pass.

## API and mathematical audit

- Meromorphicity at the level-one cusp and `qParam_tendsto` imply that `f` is
  complex-differentiable sufficiently high in the upper half-plane.
- The standard truncated fundamental domain is compact.  The analytic locus of a meromorphic
  function is codiscrete, so its complement in that compact truncation is finite.
- The finite set deliberately consists of all points where `f` is not complex-differentiable,
  rather than only points of negative meromorphic order.  This includes removable singularities
  whose stored point value disagrees with the limiting germ.
- If `(z - x)^n F z` is analytic and `J` is analytic with `J x = 0`, the dslope identity factors
  `J z = (z - x) * dslope J x z`.  Consequently `J^(n+1) F` is analytic, and the extra power
  forces its actual value at `x` to agree with the zero germ.
- Multiplying the finitely many factors `(X - C (j τ))^(nτ+1)` therefore repairs every bad
  representative.  Invariance of both `j` and `f`, together with
  `ModularGroup.exists_smul_mem_fd`, transports differentiability from the fundamental domain to
  all of `ℍ`.

## Cleanup and simplify

- Kept the cusp cutoff, compactness, local dslope, polynomial differentiability, and pullback
  lemmas private.
- Replaced the source-level ordinary/elliptic point case split by the stronger uniform extra-power
  argument.  This avoids any false assumption that `j'` is nonzero at elliptic points.
- The empty bad-set case yields `P = 1`; `Finset.prod_ne_zero_iff` proves nonvanishing uniformly.
- Updated the theorem docstring to explain the non-normalized point-value issue precisely.
- All newly added lines are at most 100 characters; `git diff --check` passes.

## Validation

- `/tmp/T011Validation.lean` instantiates the theorem at `f = j`.
- `levelOne_exists_polynomial_clearing_poles` depends only on `propext`, `Classical.choice`, and
  `Quot.sound`; no `sorryAx` is present.
- Focused and 3872-job repository builds pass.  Independent review checked the cusp cutoff,
  compact/codiscrete finiteness, dslope factorization, finite product, empty-product case, and
  invariant pullback.

## Buzz

- Outcome: FAST-BOARD.  The profiled public validation elaborates in about 0.017 seconds, well
  below the 1000 ms declaration budget.
- No heartbeat override, profiler scaffold, native-decision axiom, or deferral remains.

## Phase checklist

- [x] Doctor
- [x] Prepare and read references
- [x] Style/API audit
- [x] File-level import audit
- [x] Per-declaration golf and generality audit
- [x] Non-rename refactoring
- [x] Rename pass
- [x] Final diagnostics and gates
- [x] Simplify pass
- [x] Buzz pass
- [x] Report
