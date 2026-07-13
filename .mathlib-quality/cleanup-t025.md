# Cleanup record: T025

## Scope

- Targets: `modularPolynomial_dvd_swap` and Cox Theorem 11.18(iii).
- Supporting APIs: semantic evaluation under variable swap, coefficient maps commuting with
  swap, diagonal invariance, monicity of the integral modular polynomial, and a two-element
  lower bound for `C(m)` when `m > 1`.

## Geometric symmetry and divisibility

- Theorem 11.23 identifies a zero `(S.j,L.j)` with a cyclic inclusion `S ⊂ L`. The T022 dual
  inclusion has invariants `(L.j,S.j)`, proving that the complex zero locus is stable under
  exchanging its coordinates.
- The distinguished root `j(mτ)` is bundled in the function field over `ℂ(j)`. Pointwise
  vanishing is first proved in the holomorphic-function ring and then transported explicitly
  through the fraction-field embedding; no fragile definitional reduction is used.
- T021 identifies the monic irreducible modular polynomial with the minimal polynomial of that
  root. The swapped polynomial has the same root, hence is divisible over `ℂ(Y)`.
- `Polynomial.map_dvd_map` descends divisibility through `ℂ[Y] → ℂ(Y)` and then through
  `ℤ[Y] → ℂ[Y]`. The resulting theorem is stronger than requested: it holds at every positive
  level, including level one.

## Exact sign

- Applying the involutive swap to the divisibility gives mutual divisibility. Associated units
  in `ℤ[Y][X]` are reduced through two instances of `Polynomial.isUnit_iff` and
  `Int.isUnit_iff`, leaving exactly the alternatives `swap Φ = Φ` and `swap Φ = -Φ`.
- In the negative branch the diagonal specialization vanishes, so `X - Y` divides the complex
  modular polynomial. After mapping to `ℂ(Y)[X]`, irreducibility forces its root-variable degree
  to be at most one.
- For `m > 1`, `diag(1,m)` and `diag(m,1)` are distinct Cox representatives. Thus
  `|C(m)| > 1`, contradicting the modular-polynomial degree formula and excluding the sign.
- The monic antisymmetric polynomial `X - Y` is retained as an adversarial level-one model: it
  divides its swap but is not symmetric, confirming that the final hypothesis is essential.

## API and cleanup

- `BivariatePolynomial.eval_swap`, `map_swap`, `diagonal_eval`, and `diagonal_swap` are generic
  commutative-semiring lemmas placed with the foundational bivariate API.
- `modularPolynomial_monic` records that integral descent preserves the chosen normalization;
  `one_lt_card_coxMatrix` is reusable by the next diagonal-degree ticket.
- A final golf pass shortened `map_swap` without weakening its type. The existing files above
  1000 lines are pre-existing cross-ticket split debt reserved for the final T029 cleanup.

## Validation and quality gates

- `/tmp/T025Audit.lean` checks zero-locus symmetry, divisibility at arbitrary level, Theorem
  11.18(iii) at `m = 2`, the Cox-cardinality lower bound, and the level-one antisymmetric model
  under `-DwarningAsError=true`.
- All eight audited public declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`; none depends on `sorryAx`.
- `ModularPolynomial.lean` and `CoxMatrices.lean` pass direct warning-as-error builds. The
  focused 3871-job build and post-integration 3891-job full repository build succeed; warnings
  in `Arithmetic.lean` belong only to T026–T029.
- `git diff --check`, the 100-character gate, forbidden-code checks, threshold-1000 ms profiles,
  level-one and level-two regressions, and independent mathematical/API review all pass.

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
