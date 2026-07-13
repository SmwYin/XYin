# Cleanup record: T015

## Baseline and scope

- Target: `card_coxMatrix` in `XYin/PhD/Cox/CoxMatrices.lean`.
- The proof is independent of the right-coset equivalence: it counts the defining HNF triples
  directly and then evaluates the resulting multiplicative divisor sum.
- Focused and full-repository `lake build` both pass.

## API and mathematical audit

- Fixing `d | m` forces `a = m / d`.  The primitive condition becomes
  `Coprime (gcd (m/d) d) b` for `0 ≤ b < d`.
- These residues form the private fiber `CoxFiber_aux m d`.  Periodicity of coprimality on
  blocks of length `g = gcd (m/d) d` gives its cardinality
  `(d/g) * φ(g)`.
- An explicit equivalence identifies `CoxMatrix m` with the sigma type of these fibers over
  `d ∈ m.divisors`, including both inverse laws.  Hence its cardinality is the corresponding
  divisor sum.
- The divisor summand and sum are multiplicative on coprime inputs.  The proof reindexes
  divisors of `mn` by mathlib's structured `Nat.Coprime.divisors_mul`, factors the two gcds,
  and applies multiplicativity of Euler's totient.
- At `p^e`, every proper-power summand is `φ(p^i)` and the final summand is `p^e`.
  `Nat.sum_totient` therefore gives `p^e + p^(e-1)`.
- Packaging the sum as an `ArithmeticFunction ℕ` permits direct use of
  `multiplicative_factorization`; casting each local factor to `ℚ` gives
  `p^e (1 + 1/p)`, and the factorization product reconstructs `m`.

## Cleanup and simplify

- All counting, fiber, equivalence, arithmetic-function, and prime-power declarations are
  private `_aux` implementation details; only Cox's requested cardinal formula is public.
- The fixed-fiber cardinality was generalized to all `d`, since the formula also handles
  `d = 0`; the divisor hypothesis is needed only by the sigma equivalence.
- Imports are explicit and ordered: divisor finsets, totient, arithmetic functions, then the
  pre-existing cyclotomic dependency.
- All new lines are at most 100 characters and `git diff --check` passes.

## Validation

- `/tmp/T015Validation.lean` checks the public theorem's axioms and proves the cardinalities
  `1, 3, 4, 6, 12` at levels `1, 2, 3, 4, 6` by normalization of the Euler product.
- An independent executable bounded-triple counter verifies levels `1` through `20`, yielding
  `[1,3,4,6,6,12,8,12,12,18,12,24,14,24,24,24,18,36,20,36]`.
- `card_coxMatrix` depends only on `propext`, `Classical.choice`, and `Quot.sound`; no
  `sorryAx` is present.
- Independent reviews checked the fiber equivalence, coprime-product reindexing, prime-power
  telescoping, rational cast, and the direct small-level counter.
- Focused and 3873-job repository builds pass.

## Buzz

- Outcome: FAST-BOARD.  A threshold-100 ms profiled `card_coxMatrix` validation emits no
  slow-declaration entry; the theorem is below the 1000 ms budget.
- No heartbeat override, profiler scaffold, native-decision axiom in the proof, or deferral
  remains.

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
