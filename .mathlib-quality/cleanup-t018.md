# Cleanup record: T018

## Scope and mathematical route

- Targets: `interpolation_coeff_isLevelOne`, `recoveryFormula`, and Cox Theorem 11.9(ii).
- The interpolation polynomial is first rewritten over right cosets. Right multiplication by
  `SL₂(ℤ)` simultaneously permutes its weights and roots, proving level-one invariance.
- Meromorphicity is proved coefficientwise on the upper half-plane and at every cusp. The
  width-`m` cusp result descends to width one using period one.
- Evaluating the Lagrange sum at the distinguished root gives equation (11.17), guarded by the
  nonvanishing of the specialized derivative.
- Theorem 11.9(i) writes each interpolation coefficient rationally in `j`; a finite common
  denominator and the derivative factor then give the bivariate rational representation.

## Nonvacuous rational-function interface

- `RationalInTwo` now requires the evaluated denominator
  `τ ↦ Q.evalEval (g τ) (h τ)` to be a nonzero function. The previous condition `Q ≠ 0` was
  insufficient because the nonzero modular polynomial vanishes identically along the modular
  curve and supplied a vacuous witness for every function.
- The final denominator is the product of the common coefficient denominator with
  `(modularPolynomialC m).derivative`.
- Its restriction to `(j(τ), j(mτ))` is nonzero because evaluation at `j` is injective and the
  derivative is the product of pairwise distinct right-coset holomorphic functions.
- Individual branch points may still be zeros of the denominator, which is the intended
  pointwise domain of a rational representation.

## API and dependency cleanup

- `theorem_11_9_ii` lives in `ModularPolynomial.lean`, after `recoveryFormula`, rather than in
  `ModularFunction.lean`; this avoids the `ModularFunction -> CoxMatrices -> ModularPolynomial`
  import cycle.
- `rightCosetTranslate_smul` is a public coset-action lemma in `CoxMatrices.lean` and is reused
  by the interpolation proof.
- All implementation lemmas for analytic regularity, cusp regularity, finite common
  denominators, and derivative nonvanishing remain private.
- The public theorem is a short assembly from the private common-denominator theorem,
  `interpolation_coeff_isLevelOne`, and Theorem 11.9(i).

## Adversarial validation

- `/tmp/T018CMCollision.lean` checks that at `m = 2`, `τ = i`, the distinct representatives
  `(2,0,1)` and `(1,0,2)` have equal analytic `j`-values. This confirms that the derivative guard
  in `recoveryFormula` is mathematically necessary.
- `/tmp/T018Audit.lean` checks the exact public statements, levels `1`, `2`, and `3`, the
  strengthened existential interface, and that the modular polynomial itself is a rejected
  zero-on-the-curve denominator.
- `#print axioms` for all three targets reports only `propext`, `Classical.choice`, and
  `Quot.sound`; there is no `sorryAx`.

## Diagnostics and quality gates

- `ModularPolynomial.lean` passes direct compilation with `-DwarningAsError=true` and no output.
- The threshold-1000 ms profiler reports no T018 declaration above one second.
- The focused target build and the 3889-job full repository build pass. Remaining `sorry`
  warnings are confined to later open tickets.
- `git diff --check`, trailing-whitespace, 100-character line, forbidden-code, public-interface,
  and source-placeholder gates pass for all touched T018 files.
- Independent reviews confirmed the coset reindexing, analytic/cusp proof, common denominator,
  and nonzero-on-curve argument.

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
