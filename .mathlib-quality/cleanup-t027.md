# Cleanup record: T027

## Scope

- Target: Cox Theorem 11.18(v), Kronecker's congruence.
- Main declarations: `primeCoxMatrixEquiv`, `jLaurentSeriesMod`,
  `jUnitLaurentSeriesMod_pow_prime`, `specializeJMod_injective`,
  `cyclotomicDescent_polynomialLaurentSeries`,
  `specializeJMod_modularPolynomial_eq_formal`, `kronecker_after_specializeJ`, and
  `theorem_11_18_v`.
- Supporting modules: `XYin/PhD/Cox/LaurentPolynomialEvaluation.lean`,
  `XYin/PhD/Cox/Kronecker.lean`, `XYin/PhD/Cox/KroneckerFrobenius.lean`, and the generic
  coefficient lemma added to `XYin/PhD/LaurentQExpansion/Algebra.lean`.

## Prime representatives and local parameters

- For prime `p`, `primeCoxMatrixEquiv` explicitly enumerates `C(p)` by `Fin (p + 1)`: the first
  `p` entries are `(1,i;0,p)` and the last is `sigmaZero p = (p,0;0,1)`.
- The integral unit-step Laurent series has coefficient `jIntCoeff n` at exponent `n`.  Its
  width-`p` version is supported on `pℤ`, has order `-p`, and has leading coefficient one.
- The complex and modulo-`p` base-change squares commute coefficientwise.  The width theorem
  uses the generic nondivisible-coefficient vanishing lemma in `LaurentQExpansion/Algebra.lean`.

## Cyclotomic descent and Exercise 11.13

- `phasePolynomial` lifts each phase exponent to an integral polynomial.  Evaluation at
  `ζ_p` recovers the complex transformed series, while reduction modulo `p` followed by
  evaluation at one recovers its phase-one reduction.
- If an integral phase polynomial agrees with a constant at `ζ_p`, divisibility by the prime
  cyclotomic polynomial gives divisibility by `Φ_p(1) = p` after evaluation at one.  This is
  applied first to each Laurent coefficient and then to each outer polynomial coefficient.
- Consequently, specializing the reduction of the canonical modular polynomial at the
  width-`p` `j`-series agrees with the phase-one formal Cox product.

## Hasse injectivity

- `LaurentPolynomialEvaluation.lean` proves a generic lowest-term theorem for evaluating a
  polynomial at any Laurent series of negative order and unit leading coefficient.
- The coefficient at `natDegree(P) * order(J)` is the leading coefficient of `P`, so the
  specialization map `Y ↦ jLaurentSeriesMod p` is injective.  No analytic identity principle is
  hidden in this step.

## Frobenius factorization

- After `ζ_p ↦ 1`, the `p` lower Cox roots are the same unit-step series.  Frobenius gives its
  `p`-th power as the width-`p` series.
- The `sigmaZero` root is the `p²`-th power of a lower root, equivalently the `p`-th power of the
  width-`p` series.  Reindexing the explicit finite product therefore yields
  `(X^p - J) * (X - J^p)`.
- Injectivity of specialization transfers this identity back to the bivariate polynomial and
  gives exactly `(X^p - Y) * (X - Y^p)` modulo `p`, including the boundary prime `p = 2`.

## API and cleanup

- Generic Laurent polynomial evaluation and base-change lemmas live in their own supporting
  module; Cox-specific cyclotomic and Frobenius details remain separated into two modules.
- The power-series coefficient proof is decomposed into lower-support, below-support, divisible,
  and nondivisible helpers.  All proof bodies satisfy the beastmode length gate.
- The internal unit power series was generalized from fields to rings.  Process-oriented
  docstrings were replaced by mathematical statements, and internal normal forms remain private.

## Validation and quality gates

- `/tmp/T027Audit.lean` passes under `-DwarningAsError=true`.  It instantiates the full congruence
  at `p = 2` and `p = 3`, checks the explicit enumeration and Frobenius identities, and exercises
  Hasse injectivity.
- Every audited target depends only on `propext`, `Classical.choice`, and `Quot.sound`; none
  depends on `sorryAx`.
- All three new Cox modules pass direct warning-as-error compilation.  Threshold-1000 ms profiles
  report no target declaration over one second.
- `git diff --check`, the 100-character gate, forbidden-code scans, focused builds, independent
  mathematical/API reviews, and the 3895-job full repository build pass.

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
