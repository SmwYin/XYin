# Cleanup record: T026

## Scope

- Targets: Cox equation (11.19) and Theorem 11.18(iv).
- Main declarations: `modularPolynomialDiagonal_leadingCoeff_pow_two_mul`,
  `modularPolynomialDiagonal_leadingCoeff_isRootOfUnity`,
  `theorem_11_18_iv_leadingCoeff`, and `theorem_11_18_iv_degree`.
- Supporting module: `XYin/PhD/Cox/DiagonalLaurent.lean`.

## Laurent leading terms

- In the width-`m` local parameter `t = q^(1/m)`, the Laurent expansion of `j` has order
  `-m` and leading coefficient one.
- The transformed Cox root indexed by `σ` has order `-σ.a ^ 2` and leading coefficient
  `ζ_m ^ (-σ.a * σ.b)`.  The order and leading-coefficient API was generalized to every field
  and every nonzero phase, rather than being tied to the complex root of unity.
- If `m` is nonsquare, `m ≠ σ.a ^ 2`.  The leading term of `j - j ∘ σ` is therefore either
  `1` or `-ζ_m ^ (-σ.a * σ.b)`, according to which exponent is smaller.  Its `2m`-th power is
  one, and multiplicativity gives the same result for the full finite Cox product.

## Formal/analytic bridge and integer descent

- Laurent expansion at width `m` commutes with evaluating an arbitrary polynomial in `j`.
  Coefficientwise use of the existing Cox-product expansion identifies
  `formalCoxPolynomial m (zeta m)` with the result of substituting the Laurent series of `j`
  into the coefficient variable of `modularPolynomialC m`.
- The generic lemmas `BivariatePolynomial.diagonal_map` and `diagonal_eval₂` make simultaneous
  substitution in both variables explicit.  They identify the diagonal series with the product
  of the factors above without exposing any private cusp-meromorphic implementation lemma.
- The leading coefficient of a polynomial evaluated at the width-`m` `j`-series is recovered at
  exponent `-m * natDegree`.  This transfers the product calculation to the complex diagonal.
- Injectivity of `ℤ → ℂ`, together with `diagonal_map`, descends the explicit identity
  `leadingCoeff ^ (2m) = 1` to the integral diagonal.  The integral root-of-unity classification
  then gives exactly `leadingCoeff = 1 ∨ leadingCoeff = -1`.

## Degree

- At `τ_m = i / sqrt(m)`, multiplication by `m` agrees with the modular `S`-action.  Hence
  `j(m τ_m) = j(τ_m)`, and the diagonal polynomial has a complex root.
- The root-of-unity result makes the diagonal polynomial nonzero, so this root excludes degree
  zero.
- T025 symmetry identifies the two off-axis linear coefficients of the bivariate polynomial.
  Consequently the coefficient of `X` after diagonal specialization is twice an integer.
  If the diagonal had degree one, this coefficient would also be its leading coefficient, which
  cannot be `±1`.  Thus its degree is greater than one.

## API and cleanup

- `j_periodic` is now public; this removes a third local reconstruction of a basic analytic API.
- `modularPolynomialC_coeff_polynomialIn` is public because the formal Cox-product bridge is a
  genuine downstream consumer.
- The exact Cox factor lemmas use theorem-style snake-case names.  Unused opens and scopes were
  removed, the explicit integer exponent theorem was exposed, and internal coefficient/product
  machinery remains private.
- The width-`m` polynomial leading-term engine parallels a private width-one proof in
  `ModularPolynomial.lean`.  Extracting their common Hahn-series core is recorded as T029
  cross-file cleanup debt; keeping the two specialized proofs now avoids destabilizing integral
  descent.

## Validation and quality gates

- `/tmp/T026Audit.lean` passes under `-DwarningAsError=true`.  It checks nonsquare levels
  `2`, `3`, and `5`, the square boundary `4`, the generic transformed-series theorem over `ℚ`,
  both leading-term branches at level two, and the three public conclusions.
- Every audited target depends only on `propext`, `Classical.choice`, and `Quot.sound`; none
  depends on `sorryAx`.
- `DiagonalLaurent.lean`, `ModularPolynomial.lean`, and `ModularFunction.lean` pass direct
  warning-as-error compilation.  The final threshold-1000 ms profile has no slow declaration in
  the T026 implementation.
- `git diff --check`, the 100-character gate, forbidden-code checks, focused builds, two
  independent mathematical/API reviews, and the 3892-job full repository build pass.

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
