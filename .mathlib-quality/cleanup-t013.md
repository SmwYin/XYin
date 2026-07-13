# Cleanup record: T013

## Baseline and scope

- Targets: the elementary `CoxMatrix` arithmetic, HNF, finite-encoding, `sigmaZero`, and
  `j_act_sigmaZero` declarations in `XYin/PhD/Cox/CoxMatrices.lean`.
- The representative type now has a complete finite basic API and the distinguished
  `diag(m,1)` representative is executable.
- Focused and full-repository `lake build` both pass.

## API and mathematical audit

- Positivity of `d` follows from `a*d=m>0`; the positive complementary factor then gives both
  `a≤m` and `d≤m`.
- The inclusion matrix is deliberately `!![d,b;0,a]`, not the Möbius matrix
  `!![a,b;0,d]`.  Its column-HNF conditions reduce exactly to `d>0`, `a>0`, and `0≤b<d`.
- Its determinant is `d*a=a*d=m`, while its rank-two content is the primitive condition
  `gcd (gcd a b) d = 1` after gcd associativity and commutativity.
- Equality of bounded encodings recovers `a`, `b`, and `d` separately; proof irrelevance then
  closes equality of the bundled structures.  This supports the existing `DecidableEq` and
  `Fintype` instances.
- `sigmaZero m` has Möbius matrix `diag(m,1)` and inclusion matrix `diag(1,m)`, so its action is
  `τ ↦ mτ` and `j_act_sigmaZero` has the same direction as `levelJ m`.

## Cleanup and simplify

- Reused `Matrix.isColumnHermiteNormalForm_fin_two` and `Matrix.rankTwoContent` rather than
  reproving matrix-coordinate facts locally.
- Made `sigmaZero` computable and expressed it with structure-update syntax; no unnecessary
  `noncomputable` marker remains.
- Kept the finite encoding faithful to the existing three-coordinate definition.
- All newly added lines are at most 100 characters; `git diff --check` passes.

## Validation

- `/tmp/T013Validation.lean` structurally enumerates
  `C(1)={(1,0,1)}`, `C(2)={(2,0,1),(1,0,2),(1,1,2)}`, and
  `C(3)={(3,0,1),(1,0,3),(1,1,3),(1,2,3)}` without relying on the later cardinality theorem.
- Independent action tests give `2τ, τ/2, (τ+1)/2` and
  `3τ, τ/3, (τ+1)/3, (τ+2)/3`; the small Euler-product values are `1,3,4` as expected.
- Every T013 target is free of `sorryAx`; axiom output contains only standard axioms, with
  `d_le` requiring none.
- Focused and 3872-job repository builds pass.  Independent reviews checked arithmetic bounds,
  HNF orientation, determinant/content, encoding injectivity, small-level enumeration, and the
  action direction.

## Buzz

- Outcome: FAST-BOARD.  A threshold-100 ms profiled `j_act_sigmaZero` validation emits no
  slow-declaration entry; all targets are below the 1000 ms budget.
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
