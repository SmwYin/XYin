# Cleanup record: T037

## Scope

- Target: final cleanup, mathematical review, regression testing, public-axiom audit, and full
  build for the elliptic-`j`, singular-moduli, and bundled-function-field extension.
- Lean surface: `jInvariantLink.lean`, `CoxMatrices/Basic.lean`,
  `ModularPolynomial/Interpolation.lean`, `ModularFunctionField.lean`, `SingularModuli.lean`,
  `Section11BC.lean`, and the `XYin` umbrella.
- Public endpoints audited: `PeriodPair.weierstrassCurve_j`,
  `UpperHalfPlane.ellipticCurve_j`, `Cox.exists_sl2_mul_eq_coxMatrix`,
  `Cox.theorem_11_9_ii`, `Cox.isIntegral_j_of_isImaginaryQuadratic`, and
  `Cox.singularModulus_isIntegral`, together with their principal construction lemmas.

## API and proof cleanup

- `jInvariantLink.lean` now contains the normalized short Weierstrass model and removes the old
  exploratory `#check` commands.  Its two final bridge theorems retain focused `[simp]` tags.
- The general Cox-representative reduction in `CoxMatrices/Basic.lean` is split into two private
  HNF helpers and one documented public theorem; the file remains below 1000 lines.
- The parity argument and matrix-action computation in `SingularModuli.lean` are factored into
  private helpers.  All public fields and endpoints have stable names and source-facing docs.
- The old pointwise Theorem 11.9(ii) is preserved under the explicit name
  `theorem_11_9_ii_pointwise`; the canonical root name now denotes the requested intermediate-
  field equality.
- `Section11BC.lean` imports both new Cox modules, so the public results are available through
  the project umbrella without introducing an import cycle.

## Independent mathematical review

- The Mathlib normalization was rechecked: the coefficients `-g₂/4` and `-g₃/4` give
  `c₄=12g₂`, `c₆=216g₃`, and `Δ=g₂³-27g₃²`, hence Mathlib's `j` is the project's normalized
  lattice invariant including the factor `1728`.
- The singular-moduli proof follows Report Theorem 5.9.  Both parity branches produce a positive
  determinant strictly between consecutive squares, HNF preserves primitivity and action
  orientation, and the diagonal modular polynomial (or its negation) is an explicit monic
  integral witness.
- The fraction-field representation relation permits isolated denominator zeros but excludes an
  identically zero denominator.  Uniqueness follows from no zero divisors for holomorphic
  functions, so CM branch points do not create a point-evaluation gap.
- Both inclusions in bundled Theorem 11.9(ii) were reviewed separately.  The common base is the
  repository's existing `RatFunc ℂ = ℂ(j)` embedding, and the right side adjoins only `j_N`.

## Validation and quality gates

- Strict focused compilation with `-DwarningAsError=true` passes for every touched target and
  for `Section11BC.lean`.
- Target-module linting reports no findings in the new files; nonzero aggregate linter exits are
  solely from pre-existing transitive-import findings.
- Direct scans find no `sorry`, `admit`, resource-limit override, `native_decide`, unsafe
  declaration, debug command, TODO, or FIXME in the touched Lean files.  The Cox subtree has no
  direct `sorry` or `admit`.
- The regression file checks `τ=i`, the odd-linear-coefficient point
  `τ=(-1+i√3)/2`, both integrality paths, the explicit nonsquare determinant construction, and
  the level-one bundled field equality; strict compilation passes.
- The nine audited endpoints depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- Profiling found no touched declaration above one second.  Long-line and `git diff --check`
  scans pass.
- Final `lake build` succeeds for all 3909 jobs.  Replayed warnings and sorries are confined to
  unrelated pre-existing modules.

## Phase checklist

- [x] Source-route and normalization review
- [x] Public API and import-DAG cleanup
- [x] Whole-file cleanup of all new proof modules
- [x] Independent mathematical/API review
- [x] Strict focused compilation
- [x] Target linter and forbidden-source scans
- [x] Concrete CM-point regressions
- [x] Public endpoint axiom audit
- [x] Full repository build
