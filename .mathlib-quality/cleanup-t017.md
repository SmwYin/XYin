# Cleanup record: T017

## Baseline and scope

- Targets: the complex Cox product, its level-one coefficient theorem, polynomial dependence
  on `j`, and the canonical complex modular polynomial with its product, root, monicity, and
  degree API.
- The implementation follows equations (11.14)--(11.15), with the first polynomial variable
  as the Cox root and the second as the value of `j`.
- Focused builds and the 3885-job full-repository build pass.  Remaining warnings in
  `ModularPolynomial.lean` belong to T018 and later tickets.

## Coset product and analytic coefficients

- Right multiplication by `SL₂(ℤ)` is packaged as an equivalence of the right cosets of
  `Γ₀(m)`, and `rightCosetEval_smul` gives the exact action/reindexing identity.
- The specialized Cox product is monic of degree `|C(m)|`; reindexing its roots proves full
  modular invariance coefficientwise.
- Holomorphy on the upper half-plane is proved from the meromorphicity of `j(mτ)` and the
  finite Vieta formula for product coefficients.
- The width-`m` cusp proof is coefficientwise and uses reusable closure lemmas for finite sums
  and products of cusp-meromorphic functions.  These closure lemmas were moved to the Laurent
  q-expansion layer instead of being duplicated locally.

## Cusp-width descent

- `meromorphicAt_of_comp_pow` proves that meromorphicity descends through the nonzero complex
  power map.  After clearing a pole, the proof uses openness of `z ↦ z^m` for continuity,
  local inverses away from zero for punctured differentiability, and the removable-singularity
  theorem at zero.
- Combining this with the exact cusp-function identity for widths `h` and `m*h` converts the
  width-`m` result to width one.  Full modular invariance then supplies every cusp required by
  `IsLevelOneModularFunction`.
- The long analytic proof was split into a punctured differentiability helper and the public
  descent theorem; neither proof body exceeds the cleanup budget.

## Construction and uniqueness

- Lemma 11.10 turns every Cox-product coefficient into a polynomial in `j`.  The candidate is
  assembled coefficientwise, with the leading `X^|C(m)|` term forced explicitly.
- Specialization at `Y = j(τ)` is identified with the monic Cox product using
  `Polynomial.Monic.as_sum`.  Surjectivity of analytic `j` promotes this pointwise identity to
  uniqueness in `ℂ[Y][X]`.
- Public projections expose monicity, the right-coset product, the distinguished root
  `Φ_m(j(mτ),j(τ)) = 0`, and outer degree `|C(m)|`.
- The unused public bridge `coxPhiFunction_eval_apply` was removed; the smaller map and
  coefficient interfaces are sufficient.

## Validation

- `/tmp/T017AllAxioms.lean` checks all 30 public declarations: every one depends only on
  `propext`, `Classical.choice`, and `Quot.sound`, and all 16 linters report zero errors.
- `/tmp/T017Validation.lean` independently proves at `m=1` that the polynomial is `X-Y`, its
  specialization is `X-C(y)`, its evaluation is `x-y`, its distinguished-root theorem holds,
  and its outer degree is one.
- `/tmp/T017WidthAudit.lean` checks both directions of the power-map meromorphicity bridge.
  Independent reviews also verified variable direction, the two product formulas, the coset
  action, and the import DAG.
- `git diff --check` passes.  There is no heartbeat override, native decision, or profiler
  scaffold in the implementation.

## Buzz

- Outcome: FAST-BOARD.  Threshold-100 ms and threshold-1000 ms focused profiles found no T017
  declaration above the one-second budget.  The only threshold-1000 event in the Laurent file
  is the pre-existing circle-integral coefficient theorem, outside this ticket.

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
