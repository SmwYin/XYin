# Actual source-j polynomial leaf: independent read-only review

This reviews root's retained `AINTLIBDrafts/YZeroCoarseSourceJPolynomial.lean`.
The reviewer authored and compiled the preceding `ModelGeometricJ` and
`YZeroCoarseSourceJSurjective` leaves; the polynomial leaf itself is root's code,
read independently here, with no reviewer edit or competing build.

Final reviewed source: 90 lines, sha256
`544862a397e5cc6fb79643414f3de4daaed5ece4fee7b7ef8b9906f09be0ece5`.
Root confirmed strict direct compiler process 78504 exited 0. The reviewer read
`/private/tmp/xyin-y0-source-j-polynomial-check.log`: three axiom declarations,
all `[propext, Classical.choice, Quot.sound]`, no warnings or errors. The earlier
`Set.setOf_true` deprecation was replaced by `Set.ofPred_true` in the final source.
This direct check did not emit an olean; root's cumulative build owns artifact
emission and downstream checks. No unchecked artifact claim is made here.

The scalar instance is exactly
`yZeroInvariantCoefficientHom ... |>.toAlgebra`, via `yZeroInvariantAlgebra`.
It agrees with the scalar dictionary in the actual `yZeroComplexAlgebraPoint`.
`sourceJ_polynomial_eval` uses the actual categorical constant formula
`yZeroJPolynomial_C`, evaluated at each `z : ℂ`, and the actual variable formula
`yZeroJPolynomialHom_X`. Thus its use of `φ.commutes z` refers to the original
coarse structure morphism's coefficients, rather than an unrelated algebra
structure on the fixed subring. `Polynomial.ringHom_ext` then proves the full
evaluation equality on every polynomial.

For injectivity, equal images give equal evaluations at any complex number:
the proved actual invariant-j value surjectivity supplies a complex algebra
point realizing that number, and the full evaluation formula applies.
`Polynomial.eq_of_infinite_eval_eq` uses the domain structure of **ℂ** and its
infinite set of values. No domain assumption on the invariant coefficient ring
is introduced or inferred. The zero-iff corollary applies this injection to the
zero polynomial, using the actual hom's `map_zero` law in both directions.
The level-three sanity directly instantiates that same zero-iff theorem.

No mathematical issue or required repair was found. The result is a verified
injection of the actual one-coordinate polynomial homomorphism. It does not
establish a two-coordinate modular-polynomial relation, finiteness over the
j-line, normality, a domain structure on the actual invariant ring, or a
function-field identification.
