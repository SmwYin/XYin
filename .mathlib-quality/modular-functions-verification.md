# Modular functions verification

Date: 2026-09-21. Scope: nine Lean modules under `XYin/PhD/ModularFunctions`, plus
its import in `XYin.lean`. All new statements implement the user's authorized request.

## Definition and sources

`ModularFunction Γ` extends `SlashInvariantForm Γ 0` and adds exactly two Prop fields:
canonical membership in the meromorphic function field, and exponential growth at each cusp.
The growth bound is uniform in the real part and uses the existing `atImInfty` filter.

The ambient field is the codiscrete germ quotient from Stefan Kebekus's ProjectVD,
commit `9c218722ad71e9bd2ba357892bc835c8c648aaa8`, `VD/Field`. Source attribution and
Apache 2.0 header are preserved in `MeromorphicField.lean`. Canonical normal forms remove
arbitrary point values; this matters for the pointwise growth condition. This construction
has genuine `Field` and `Algebra ℂ` instances, verified by typeclass synthesis.

The cusp proof implements the exponential-growth/q-coordinate argument from the user's
linked “Meromorphic Functions Growth Rate” conversation. It reuses mathlib's removable
singularity, meromorphic-order, normal-form, slash-action, and cusp-width APIs. The existing
`j_slash_invariant` and `j_cuspFunction_meromorphicAt` supply the j-function application.

## Mathematical and code review

An independent read-only reviewer checked all nine modules, then rechecked the final
`Basic`, `Cusps`, and `JInvariant` integration. No actionable mathematical issue remained.
In particular:

- The quotient and canonical representative map distinguish field equality from arbitrary
  pointwise representatives, including values at poles.
- Growth implies eventual holomorphy for normal meromorphic representatives; it is not
  assumed as an additional structure field.
- Weight-zero slash transport handles both determinant signs in `GL₂(ℝ)`.
- The local cusp equivalence accepts any given positive period. The all-cusp equivalence
  derives positive periods for discrete groups with determinant in `{±1}`.
- `jModularFunction` covers every level-one cusp using its `SL₂(ℤ)` orbit description.

Simplify result: **ISSUES-FOUND-AND-FIXED** during integration. Replaced a reference to an
unavailable Cox helper with a direct use of `SlashInvariantFormClass.periodic_comp_ofComplex`;
made the `SL₂`/`GL₂` coercion explicit before rewriting j's slash invariance; used explicit
canonical-field `toFun` applications to avoid reducible-subtype field-notation ambiguity.
Added source headers. The final independent review passed. No statement weakening or
new axiom was used to complete proofs, and no option/linter suppression was introduced.

## Build and trust checks

- Baseline full build: passed (3908 jobs).
- Final full `lake build`: passed (3916 jobs); existing project warnings remain outside
  the new modules. Final log: `/tmp/xyin-modular-final-build.log`.
- All nine new modules also compiled separately with profiling enabled.
- `git diff --check`: passed. All new Lean lines are at most 100 characters.
- New-module scan: no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, or
  `set_option` found.
- A standalone import of `JInvariant` audited 12 principal declarations with `#print axioms`.
  Every result contains only `propext`, `Classical.choice`, and `Quot.sound`.
  The same file successfully synthesizes `Field UpperHalfPlane.MeromorphicField` and
  `Algebra ℂ UpperHalfPlane.MeromorphicField` in a noncomputable section.

Audited declarations:

1. `MeromorphicOn.GermRing.instField`
2. `UpperHalfPlane.MeromorphicField.toFun_injective`
3. `UpperHalfPlane.MeromorphicField.meromorphicNFOn_iff_exists`
4. `UpperHalfPlane.isOfExponentialGrowth_iff_meromorphicAt_cuspFunction`
5. `UpperHalfPlane.meromorphicNFOn_slash_zero`
6. `SlashInvariantForm.exists_pos_period_at_cusp`
7. `OnePoint.isOfExponentialGrowthAt_iff_isMeromorphicAt`
8. `SlashInvariantForm.exponential_growth_at_cusps_iff`
9. `ModularFunction.toMeromorphicField_injective`
10. `ModularFunction.meromorphic_at_cusps`
11. `jModularFunction`
12. `coe_jModularFunction`

Axiom log: `/tmp/xyin-modular-axioms.log` (successful final run).

## Performance

Command for each module: `lake env lean -Dprofiler=true -Dprofiler.threshold=100 FILE`.
All runs succeeded. No individual declaration crossed the 100 ms reporting threshold;
only import events were reported above threshold. No optimization was justified.
Cumulative categories below are Lean profiler measurements, not whole-file elapsed time.

| Module | Import | Elaboration total | Tactic execution total |
| --- | ---: | ---: | ---: |
| Basic | 3.16 s | 25.7 ms | 2.66 ms |
| CuspGrowth | 3.03 s | 15.0 ms | 56.9 ms |
| CuspPeriod | 3.17 s | 13.9 ms | 16.8 ms |
| Cusps | 3.20 s | 15.9 ms | 5.47 ms |
| GrowthAtCusp | 3.10 s | 14.5 ms | 23.1 ms |
| JInvariant | 3.65 s | 16.8 ms | 42.5 ms |
| MeromorphicField | 3.30 s | 315 ms | 157 ms |
| NormalFormGrowth | 3.01 s | 5.44 ms | 26.1 ms |
| NormalFormSlash | 3.01 s | 15.5 ms | 63.6 ms |

Logs: `/tmp/xyin-modular-profile-*.log`. Temporary verification sources and profiling
options are not part of the Lean source tree.
