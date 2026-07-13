# Cleanup record: T012

## Baseline and scope

- Target: Cox Theorem 11.9(i), `theorem_11_9_i`, in
  `XYin/PhD/Cox/ModularFunction.lean`.
- Added reusable closure API for products and polynomial evaluation of `Γ₀(N)`-modular
  functions.
- Focused and full-repository `lake build` both pass.

## API and mathematical audit

- `IsGamma0ModularFunction.mul` proves all three defining conditions: meromorphicity on `ℍ`,
  weight-zero slash invariance, and meromorphicity of the product at every cusp.
- `IsGamma0ModularFunction.polynomialIn` is proved at arbitrary positive level.  Polynomial
  evaluation preserves local meromorphicity by induction on addition and monomials; a
  punctured-neighborhood cusp identity transfers the same induction to every cusp.
- T011 supplies a nonzero `P` for which `P(j)f` is holomorphic on `ℍ`.  The closure API shows
  that this product is still level-one modular, so T010(ii) writes it as `Q(j)`.
- At every point where `P(j)` is nonzero, `eq_div_iff` gives
  `f = Q(j) / P(j)`, exactly matching the guarded `RationalIn` predicate.

## Cleanup and simplify

- Generalized both closure results from level one to arbitrary `Γ₀(N)` rather than adding
  one-off wrappers.
- Made the level parameter implicit and exposed the results as chainable predicate methods:
  `hf.mul hg` and `hf.polynomialIn P`.
- Kept the punctured-cusp congruences and local polynomial-meromorphic induction private.
- The final Cox theorem is a short assembly proof with the numerator/denominator orientation
  made explicit by `eq_div_iff` and one commutativity rewrite.
- All newly added lines are at most 100 characters; `git diff --check` passes.

## Validation

- `/tmp/T012Validation.lean` applies the theorem to `j` and checks guarded rational expressions
  with general denominator `X - c`, including the elliptic values `0` and `1728`.
- Both closure theorems and `theorem_11_9_i` depend only on `propext`, `Classical.choice`, and
  `Quot.sound`; no `sorryAx` is present.
- Focused and 3872-job repository builds pass.  Independent review reproduced the proof and
  checked all three closure conjuncts, absence of circular dependencies, and the division
  orientation.

## Buzz

- Outcome: FAST-BOARD.  A threshold-100 ms profiled validation emits no slow-declaration entry;
  the public theorem is well below the 1000 ms budget.
- No heartbeat override, profiler scaffold, native-decision axiom, or deferral remains.

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
