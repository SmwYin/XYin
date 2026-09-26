# Formal Cox product, Laurent evaluation and arithmetic cleanup

Full-file/full-proof review of `Arithmetic.lean`, `FormalCoxProduct.lean`, and
`LaurentPolynomialEvaluation.lean`. Baseline is
`/tmp/xyin-proof-cleanup-before/XYin`; public and private declarations, mathematical
statements, definitions, documentation and imports remain unchanged.

| File | Before | After | Reduction |
|---|---:|---:|---:|
| Arithmetic | 359 | 346 | 13 |
| FormalCoxProduct | 272 | 228 | 44 |
| LaurentPolynomialEvaluation | 176 | 151 | 25 |

## Arithmetic audit

- Basic theorem wrappers retained. Zero-locus symmetry factors its common dual-inclusion
  implication once, eliminating the copied reverse-direction construction.
- `aeval_base_eq_zero_of_forall_eval_eq_zero`: polynomial coefficient extensionality and
  `ratFuncEvalJ_algebraMap` replace a separate ring-hom composition equality plus two map
  compositions. Existing `eval₂_evalRingHom` is rewritten directly instead of applying
  congrFun twice. Pointwise evaluation and the meromorphic-field embedding stay explicit.
- Divisibility by the swapped polynomial: retained the minpoly argument, monicity, and
  injective coefficient-change descent; these are necessary mathematical steps.
- Antisymmetry exclusion: degree transport uses the monic map degree equality directly.
  The diagonal-root contradiction and irreducibility argument remain unchanged.
- Associated integer polynomials and symmetry: retained the unit classification, while
  the second divisibility uses the involutive swap simplification directly.
- Diagonal leading coefficient: coefficient transport uses `leadingCoeff_map_of_injective`
  without a temporary equality and symmetry step. Root-of-unity/sign consequences retained.
- Coefficient-one diagonal calculation, imaginary fixed point, degree > 1 and the explicit
  level-three consequence: checked all proofs and retained their finite polynomial,
  square-root and parity arguments; no matching stronger API eliminated the actual work.

## FormalCoxProduct audit

- Laurent map and integral subring: retained coefficientwise map and ring-closure proofs;
  the finite convolution sum is the appropriate integrality argument.
- Integrality of transformed j coefficients: retained power-integrality of roots of unity.
  Integral product coefficients now rewrite the subring polynomial map directly and use
  the coefficient's property, deleting a fresh coefficient comparison theorem.
- `transformedJSeries_pow_eq_reindex`: retained primitive-root exponent divisibility,
  but the cast of `Nat.mod_add_div` is combined with the determinant identity by an
  explicit `linear_combination`. Removed a temporary difference identity and three-step
  polynomial calc. The casted remainder identity now suffices directly.
- `formalCoxPolynomial_pow_eq`: rewrites factors once and applies the existing bijection's
  `prod_comp`, replacing product congruence scaffolding.
- Galois-fixed coefficients: updates the existing polynomial map theorem using the
  primitive-root automorphism exponent and reindexing result. Removed a duplicate
  anonymous Laurent ring-hom type and its repeated structural fields.
- Fixed-field descent to Q then integral descent to Z: retained standard Galois/integrally
  closed APIs and their necessary algebra instances.
- Cyclotomic field/root construction retained. The final complex coefficient bridge uses
  the existing coefficient map equality and integer witness directly, eliminating a second
  named bridge and three-step calc.

## LaurentPolynomialEvaluation audit

- The bundled Laurent coefficient map and specialization definitions retained.
- Polynomial evaluation commutes with mapping by `Polynomial.hom_eval₂` followed by the
  coefficient-map and input equalities; removed the expanded evaluation calc.
- Bivariate map compatibility and pointwise wrapper retained.
- Power order and leading coefficient lemmas retained: mathlib has order_pow and
  leadingCoeff_mul, but no imported leadingCoeff_pow lemma replacing the short induction.
- Lowest coefficient: `Finset.sum_eq_single` exposes the leading-degree summand directly;
  no outer calc is needed. Lower summands vanish by order, and positive integer comparison
  is cast from `Nat.mul_lt_mul_of_pos_left`. The actual lowest-term argument is unchanged.
- Injectivity: existing `injective_iff_map_eq_zero` reduces to one polynomial with zero
  evaluation. Its leading coefficient is zero by the preceding coefficient theorem,
  avoiding an extra P-Q definition and contradiction setup.

No generic wrappers, definitions, axioms, admissions, or local limit changes were added.
Source searches covered HahnSeries coefficient/order/leading coefficient, polynomial
hom_eval₂/map/eval, ring-hom injectivity, primitive roots and Galois fixed-field APIs.
No generalization was made because the task preserves signatures. Final simplify pass
reviewed reuse, mathematical visibility and elaboration of every changed proof.

## Final validation

All three final sources pass direct Lean/profile checks with zero diagnostics. Baseline
profiles also exit 0. Final-source axiom checks cover four Arithmetic theorems (swap
divisibility/symmetry, degree and level-three polynomial), formal product integrality, and
three Laurent base-change/lowest-coefficient/injectivity results. All depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

| File | Cumulative tactic before → after | Typeclass inference before → after |
|---|---:|---:|
| Arithmetic | 396 → 534 ms | 963 ms → 1.77 s |
| FormalCoxProduct | 406 → 544 ms | 1.57 → 1.67 s |
| LaurentPolynomialEvaluation | 66.8 → 90.8 ms | 415 → 372 ms |

These are single concurrent-run measurements, not a stable speed benchmark or a claimed
runtime improvement. No individual reported proof operation exceeded one second. Logs:
`/tmp/xyin-{arithmetic,formal,evaluation}-profile-{before,after}.log`.
Arithmetic/Formal final profiles include the final-source axiom checks; Laurent's are in
`/tmp/xyin-evaluation-cleanup-axioms.log`.

Failed temporary attempts were removed: ring-hom coefficients require Polynomial.ext
without recursively extending subtypes, and the final cyclotomic coefficient bridge must
rewrite coeff_map before changing the anonymous ring-hom application. Full final checks
were rerun after fixing these. Dependency-cache misses during parent integration were
recorded separately and were not counted as proof results. No admissions, new axioms or
limit changes appear in the files. Parent owns cumulative project builds and actual-diff
review. The final simplify pass retains mathematical arguments and replaces only their
redundant scaffolding.
