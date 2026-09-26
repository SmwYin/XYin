# Cox matrix, counting and sublattice classification cleanup

All three files were read fully, including every proof. Baseline:
`/tmp/xyin-proof-cleanup-before/XYin`. Definitions, statements, documentation,
namespace boundaries, imports and declaration names are preserved; only proofs change.

| File | Before | After | Reduction |
|---|---:|---:|---:|
| CoxMatrices/Basic | 897 | 822 | 75 |
| CoxMatrices/Cardinality | 299 | 278 | 21 |
| CyclicSublattice/Classification | 423 | 370 | 53 |

## Basic audit

- Cox matrix positivity/bounds, HNF inclusion, finite encoding, distinguished matrix and
  finite cosets: checked all proofs. `act` uses existing `Complex.div_natCast_im` simp
  behavior instead of recomputing division via the norm square. Other short constructions
  remain explicit.
- Matrix-star identities and Cox input: retained entrywise computations; multiplication
  reverses order, so the finite ring calculations express the required anti-involution.
- `rankTwoContent_mul_sl` now cancels the inverse in the existing divisibility theorem
  directly, deleting the temporary cancellation theorem.
- `columnHNF_eq_of_mul` extracts seven entries once, simplifies them together, then uses
  positive divisibility and reduced-remainder uniqueness. Removed repeated extraction
  and simplification inside each diagonal comparison. Its overlap with HNF `matrix_eq`
  is reported to the parent as a potential future public matrix API; dependency edits were
  outside this batch's ownership.
- Right-relation/matrix equivalence and existence of SL2 HNF: retained the determinant,
  divisibility, and sign arguments. Conversion to Cox data uses `congrArg Int.natAbs`
  for the determinant and `Int.natAbs_lt_natAbs_of_nonneg_of_lt` for the residue bound.
- Reduction uniqueness and `rightRel_iff_coxRepresentative_eq`: direct association and
  inverse cancellation replace nested matrix `calc` blocks. Local choices and witnesses
  are unchanged.
- Primitive row/Smith normalization: retained the constructive prime-factor product and
  Bezout column arguments. The two intermediate determinant proofs collapse to one
  directed `det_mul` rewrite. Surjectivity cancels the normalization matrices directly.
- Quotient bijection and quotient construction: retained the explicit representative
  induction. `rightCosetTranslate` gets representative independence from its invariant
  equality in one group simplification. Inverse laws for `rightCosetMul` rewrite equality
  of representatives instead of reproving the quotient relation of equal matrices.
- Affine Möbius identity, normalization of levelJ, and final public action results:
  retained their focused field/ring computations. No new generalized wrapper is needed.

## Cardinality audit

- `card_filter_range_coprime_mul_aux`: replaces a disjoint Ico union and cardinality
  calculation by `Nat.count_add'` and coprimality periodicity. The induction now has one
  mathematical step rather than auxiliary interval/disjointness propositions.
- Fibers, divisor sigma equivalence, and counting: retained the explicit finite type
  correspondence; removed duplicate goal changes and a temporary rewritten cardinality
  assertion in `card_coxFiber_aux`.
- Divisor-term multiplicativity: retained coprime gcd factors and totient multiplicativity.
  Divisor-sum multiplicativity uses `Finset.sum_attach` directly, deleting an intermediate
  identical sum and its transitivity proof.
- Prime-power terms and their divisor sum: retained the half-exponent case split, totient
  prime-power formula, and sum_totient. These are the substantive arithmetic proof.
- Arithmetic-function and factorization product: retained existing multiplicative API.
  `cast_prime_pow_add_aux` uses `eq_div_iff` and `pow_sub_one_mul` directly instead of a
  separate two-step quotient calc. Final Euler product and cardinality bridge retained.

## Classification audit

- `toCoxMatrix`: determinant natAbs follows directly from the HNF index formula;
  positivity and residue bound use existing Int APIs. Data fields are unchanged.
- HNF/inclusion matrix equality: all four entries share the same simplification instead
  of four copies of almost the same simp list.
- Inclusion map injectivity: determinant nonvanishing is converted by the existing
  determinant/ker and ker/injectivity equivalences. Inclusion HNF uses the definitional
  composition of `LinearEquiv.ofInjective`; removed its local extensionality lemma.
- Cox/sublattice inverse laws: use inclusion-matrix injectivity and HNF uniqueness directly,
  dropping two intermediary equalities. The converse range proof is retained.
- Sublattice generators: `map_span`, basis `span_eq`, and `Set.range_comp` replace both
  directions of two image/range membership proofs. The explicit generator-coercion proof
  is retained after standard simp lemmas failed on its dependent submodule type. The Fin 2 range uses
  `Matrix.range_cons_cons_empty`.
- Scaled complex lattice identity: rewrites equal generators at the span level, eliminating
  a pointwise membership/extensionality detour. Its denominator computation stays explicit.
- Analytic j values, root classification, and Cox theorem 11.23: retained. These already use
  the established HNF bijection, dual/scaling machinery, and j-surjectivity without repeated
  proof scaffolding.

## Searches, rejected trials and scope

Inspected mathlib Complex division, quotient lift, Nat count/totient, Finset sums,
Submodule maps, finite vectors, determinant and kernel APIs. No statement generalization
or new helper declaration was added. Broad simp of SL2 determinants was rejected because
it unfolded matrix inverses into adjugates; final code uses directed determinant rewrites.
The representative-uniqueness call explicitly fixes its second SL2 witness before rewriting.
No arbitrary time/recursion/heartbeat limits were added.

## Final validation

All three final sources pass direct Lean with zero errors and warnings. Their baseline and
final profiled elaborations also exit 0. The Basic algebraic prefix was additionally checked
independently while analytic caches were rebuilding. Final-source axiom checks cover the
right-coset equivalence/action and representative reduction (five results), cardinality,
and the classification/lattice/root equivalence (three results). All depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

| File | Cumulative tactic before → after | Typeclass inference before → after |
|---|---:|---:|
| Basic | 581 → 604 ms | 2.31 → 2.62 s |
| Cardinality | 178 → 161 ms | 131 → 101 ms |
| Classification | 344 → 447 ms | 925 ms → 1.38 s |

Single runs were measured under concurrent project work; these are proof-size improvements,
not a claim of runtime improvement. No reported individual proof operation exceeded one
second. Logs: `/tmp/xyin-{matrices,cardinality,classification}-profile-{before,after}.log`;
Basic/Cardinality final-source axiom logs are matching `-cleanup-axioms.log`, while
Classification's final profile includes its three axiom checks. No admissions/axioms/limits
were added. The changed files pass whitespace checks. Earlier missing Delta, Reciprocal,
LaurentQExpansion or ResToImagAxis oleans were parent-owned dependency rebuilds; final
receipts above were collected after those dependencies had been restored. Parent owns the
cumulative project build and independently reviews the actual diffs.
