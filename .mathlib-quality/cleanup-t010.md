# Cleanup record: T010

## Baseline and scope

- Targets: Cox Lemma 11.10(i),(ii) in `XYin/PhD/Cox/ModularFunction.lean`.
- Repaired the pre-existing `j_poleOrder` dependency in
  `XYin/PhD/jFunction/jfunction.lean`; no duplicate local pole-order theorem remains.
- Focused and full-repository `lake build` both pass.

## API and mathematical audit

- Part (i) packages the function as a weight-zero level-one `ModularForm`.  Analyticity of the
  cusp function gives convergence, hence boundedness, at infinity; level-one invariance transports
  this bound to every cusp.  Mathlib's `ModularFormClass.levelOne_weight_zero_const` then applies.
- Part (ii) strongly inducts on `poleOrder 1 f`.  At a positive pole order `m`, the quotient of
  the trailing coefficients of `f` and `j^m` chooses a scalar `a` for which
  `f - a * j^m` has strictly larger meromorphic order and therefore strictly smaller pole order.
- A punctured-neighborhood cusp identity proves that subtraction preserves the full
  `IsGamma0ModularFunction` predicate; upper-half-plane holomorphicity is preserved separately.
- The base case converts pole order zero to cusp analyticity and invokes part (i); the induction
  step adds `a * X^m` to the polynomial returned by the hypothesis.

## Contamination repair

- The old proof of `qj_exp_zero_for_jfunction` obtained the constant coefficient of `E4` from the
  transitive-sorry theorem `E4_q_exp`.
- Replaced that dependency with mathlib's clean
  `EisensteinSeries.E_qExpansion_coeff_zero`.  Consequently the existing public `j_poleOrder`
  now depends only on standard axioms and can be reused directly.
- Independent review confirmed this repair removes roughly ninety lines of duplicated
  `E4`/`qj` limit and pole-order code from `ModularFunction.lean`.

## Cleanup and simplify

- Kept germ normalization, trailing-coefficient cancellation, and cusp arithmetic helpers
  private; the modular-function public API still exposes exactly the two Cox declarations.
- Generalized the arithmetic closure helper internally from level one to arbitrary positive level
  `N`.
- Restricted the final polynomial rewrite to the needed hypothesis and goal rather than using
  `rw ... at *`.
- All newly added lines are at most 100 characters; `git diff --check` passes.

## Validation

- `/tmp/T010Validation.lean` checks constants, `j`, and explicit `j^n + c` polynomial
  representations.
- `levelOne_constant_of_holomorphic`, `levelOne_polynomialInJ_of_holomorphic`, and the repaired
  `j_poleOrder` depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- Focused builds of `jfunction.lean` and `ModularFunction.lean` pass; the full 3872-job repository
  build passes.  The three remaining sorries in `ModularFunction.lean` belong to T011, T012, and
  T018.
- Independent reviews checked the maximum-principle packaging, punctured-cusp congruence,
  equal-order leading-term cancellation, strict pole-order descent, and strong-induction algebra.

## Buzz

- Outcome: FAST-BOARD.  A threshold-100 ms profiled compile reports the two nontrivial new germ
  helpers at about 0.22--0.24 s; neither public T010 target approaches the 1000 ms budget.
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
