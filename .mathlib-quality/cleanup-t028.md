# Cleanup record: T028

## Scope

- Target: Cox equation (11.22), the explicit level-three modular polynomial.
- Main declarations: `modularPolynomialThreeExplicit`,
  `symmetric_bidegree_three_eq_zero_of_laurent_coeff`,
  `modularPolynomial_three_of_complex_swap`, and `modularPolynomial_three`.
- Supporting modules: `XYin/PhD/Cox/SymmetricCubicLaurent.lean` and
  `XYin/PhD/Cox/LevelThree.lean`.

## Finite Laurent certificate

- The explicit expression is expanded into its 25 bidegree slots.  Its displayed final term is
  exactly `-2 ^ 31 * 5 ^ 6 * 22973 * X * Y`, as in Cox.
- The integral `j`-series coefficients through index 12 are certified with `decide +kernel`.
  No native-code proof oracle is used.  The width-three and width-nine power series model
  `j(q^(1/3))` and the `sigmaZero` transformed root respectively.
- Multiplication by `q^36` clears every nonzero monomial of the explicit polynomial.  The ten
  needed coefficients are evaluated by finite convolutions and proved to vanish in the kernel.
  The largest numerical certificate was split by rows so that every declaration profiles below
  one second.

## Symmetric cubic detector

- A symmetric bivariate polynomial of bidegree at most three has ten coefficient orbits.  Their
  distinct leading weights against Laurent orders `-9` and `-3` are
  `0, 9, 12, 18, 21, 24, 27, 30, 33, 36`.
- `SymmetricCubicLaurent.lean` reconstructs the ten-orbit normal form and eliminates its
  coefficients by reverse triangular induction.  An independent audit checked that omitting the
  weight 12 would be false, with `X * Y` as the boundary counterexample.
- The reusable coefficient identity for a swapped bivariate polynomial was promoted to
  `BivariatePolynomial.coeff_coeff_swap`; three local copies were removed.

## Identification with the canonical polynomial

- The formal Cox product has the `sigmaZero` transformed series as an actual root.  Therefore the
  canonical `modularPolynomialC 3` vanishes after Laurent specialization.
- Both the canonical and explicit polynomials are monic of outer degree four.  Their difference
  consequently has outer degree at most three; symmetry gives the same inner bound.
- The ten certified coefficients and the symmetric cubic detector make this difference zero over
  `ℂ`.  Injectivity of the two coefficient maps `ℤ → ℂ` descends the identity to `ℤ`.
- The symmetry input comes from Theorem 11.18(iii), whose proof uses Theorem 11.23, dual cyclic
  sublattices, and irreducibility.  It does not depend on equation (11.22), so the argument is not
  circular.

## Validation and quality gates

- `/tmp/T028Audit.lean` checks the explicit symmetry, Kronecker factorization modulo three, and
  the distinguished analytic root.  It also audits all three public T028 declarations.
- The public theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`; it has no
  `sorryAx` or generated native axiom.
- Direct warning-as-error compilation passes for `ModularPolynomial.lean`,
  `SymmetricCubicLaurent.lean`, `LevelThree.lean`, and `Arithmetic.lean`.
- Threshold-1000 ms profiles have no slow declaration.  The detector's longest proof body is 27
  lines, and `LevelThree.lean` has no proof body over 30 lines.
- `git diff --check`, the 100-character gate, forbidden-code scans, API privacy checks, and an
  independent mathematical review pass.  The full repository build is recorded with T029.

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
