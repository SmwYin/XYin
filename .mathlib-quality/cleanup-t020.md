# Cleanup record: T020

## Baseline and scope

- Targets: the Hasse q-expansion principle, coefficientwise descent of the complex modular
  polynomial to `ℤ[Y][X]`, the chosen integral polynomial's comparison theorem, and Cox
  Theorem 11.18(i).
- The Hasse statement is the specialized coefficient form needed here: it assumes all Laurent
  coefficients of a given `P(j)` are integers. This is stronger in its coefficient hypothesis
  and narrower in its input than Cox Exercise 11.12, but proves the exact descent required for
  Theorem 11.18(i).
- Focused builds and the 3888-job full-repository build pass. Remaining sorries in the touched
  files belong to T018, T021, and later arithmetic tickets.

## Triangular q-expansion argument

- Laurent q-expansion is shown to commute with evaluating a complex polynomial at `j`, using
  the finite-sum/product algebra from T019.
- The series of `j` has order `-1` and leading coefficient `1`. Hence the coefficient of
  `q^(-natDegree P)` in `P(j)` is exactly `P.leadingCoeff`; all lower-degree monomials vanish at
  that exponent.
- Integer-coefficient Laurent series form a subring, and the Laurent series of `j` lies in it.
  Therefore subtracting an integral leading monomial preserves coefficientwise integrality.
- Strong induction strips `P.eraseLead`, whose degree is strictly smaller away from the constant
  case, and reconstructs an integer polynomial one leading monomial at a time.
- The public induction proof is under the cleanup size budget; leading-coefficient extraction and
  preservation under `eraseLead` are separate private leaves.

## Bivariate descent

- Specializing the inner variable of `modularPolynomialC` at `j(τ)` and comparing outer
  coefficients identifies `polynomialIn ((modularPolynomialC m).coeff n) j` with the corresponding
  Cox-product coefficient.
- T019 supplies integer Laurent coefficients for that function, so Hasse descends every outer
  coefficient to a polynomial in `ℤ[Y]`.
- `Polynomial.lifts_iff_coeff_lifts` and `exists_support_eq_of_mem_lifts` assemble these lifts into
  one polynomial in `ℤ[Y][X]`. The import of `Mathlib.Algebra.Polynomial.Lifts` is explicit.
- `modularPolynomial_map_complex` is the defining witness projection, and `theorem_11_18_i` is its
  named arithmetic wrapper.

## Validation

- `/tmp/T020Audit.lean` checks all four public targets: each depends only on `propext`,
  `Classical.choice`, and `Quot.sound`, and all enabled linters pass.
- The audit covers the zero and nonzero constant Hasse cases, nested polynomial-map injectivity,
  the generic comparison theorem, and levels `m = 1, 2, 3`.
- Independent scratch proofs checked both manual finite-support assembly and the shorter
  `Polynomial.lifts` route, including the outer-`X`/inner-`Y` variable direction.
- `git diff --check` passes; all touched source lines are at most 100 characters; no T020 proof
  contains `sorry`, a heartbeat override, native decision code, or profiler scaffolding.

## Buzz

- Outcome: FAST-BOARD. The threshold-1000 ms profile reports no T020 declaration above the
  one-second budget; threshold-100 ms profiling found only bounded elaboration work.

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
