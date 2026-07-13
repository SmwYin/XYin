# Cleanup record: T019

## Baseline and scope

- Target: integer Laurent coefficients of every coefficient of the Cox product, the arithmetic
  core of Theorem 11.18(i).
- The proof separates the formal cyclotomic descent from the analytic Laurent expansion bridge.
- Focused builds and the 3888-job full-repository build pass. Remaining sorries in
  `ModularPolynomial.lean` belong to T018 and T020--T021.

## Formal product and Galois descent

- `formalCoxPolynomial` is the Cox product formed from the formal transformed `j`-series.
- Coefficientwise algebraic integrality is packaged as a Laurent-series subring and propagated
  through the finite product.
- A cyclotomic Galois automorphism sends the primitive root to a coprime power. The existing Cox
  reindexing equivalence then permutes all roots and fixes every coefficient.
- Fixed-field descent first puts each coefficient in `ℚ`; algebraic integrality then identifies
  it with the image of an integer. The argument is carried out in the concrete field
  `ℚ(zeta_m) ⊆ ℂ` and mapped back to `ℂ`.

## Analytic/formal Laurent bridge

- The Laurent q-expansion layer now provides closure under constants, negation, finite sums, and
  finite products. Multiplication clears arbitrary common pole shifts, so it does not assume the
  generally false equality of pole orders.
- Substitution `τ ↦ mτ` is proved by composing the pole-removed Taylor expansion with
  `q ↦ q^m`; its coefficient theorem records the exact exponent scaling.
- Each analytic Cox root is matched with its formal transformed `j`-series. Finite-product
  compatibility identifies a Cox coefficient's analytic Laurent series with the corresponding
  formal coefficient.
- Width `m` eliminates fractional exponents: the analytic coefficient at exponent `k` is the
  formal coefficient at exponent `m*k`, which the Galois argument proves integral.

## Validation

- `/tmp/T019Audit.lean` checks the formal theorem, Laurent closure/scaling API, and analytic bridge:
  all declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; all enabled
  linters pass.
- Independent instances cover levels `m = 1, 2, 3`, and a separate check verifies that the formal
  product is monic.
- Both new files pass `-DwarningAsError=true`; `git diff --check` passes; no T019 proof contains
  `sorry`, a heartbeat override, native decision code, or profiler scaffolding.

## Buzz

- Outcome: FAST-BOARD. Threshold-1000 ms profiles of the formal, Laurent-algebra, and modular
  polynomial files found no T019 declaration over the one-second budget.

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
