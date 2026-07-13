# Cleanup record: T021

## Baseline and scope

- Targets: irreducibility of the complex modular polynomial in the outer variable over
  `ℂ(Y)`, together with the named Theorem 11.18(ii) wrapper.
- The proof follows Cox Exercise 11.10 through a concrete function field: the fraction field of
  holomorphic functions on the upper half-plane.
- The new infrastructure is isolated in `UpperHalfPlaneFunctionField.lean`; the modular
  polynomial file retains only the product and minimal-polynomial argument.

## Function-field realization

- Holomorphic functions on `ℍ` form a domain by the analytic zero-product theorem. Their
  fraction field therefore supplies an ambient field for the conjugates.
- Evaluation `P ↦ P(j)` is injective by surjectivity of the analytic `j`-function. The universal
  property of `RatFunc` extends it to an injective map `ℂ(Y) → FunctionField`.
- Precomposition by `delta : SL₂(ℤ)` extends to a `ℂ(Y)`-algebra automorphism because `j` is
  modular invariant. The raw ring-equivalence implementation is private; the public interface is
  `precompAlgEquiv` and its action on right-coset roots.
- The canonical holomorphy theorem `j_mdifferentiable` is now public in `ModularFunction.lean`
  and reused here. The identity right coset and its orbit-surjectivity theorem live with the
  right-coset action in `CoxMatrices.lean`.

## Distinct conjugates

- The leading exponent of `transformedJSeries` recovers the Cox entry `a`; its leading root-of-
  unity coefficient then recovers `b`, and the determinant recovers `d`.
- Equality of analytic conjugate functions therefore forces equality of Cox representatives.
  Reindexing by `coxMatrixEquivRightCosets` proves that the function-field roots are injective.
- This is intentionally a statement about functions, not values at a fixed `tau`: specialized
  roots can collide at CM points. An adversarial check exhibits the collision at `m = 2`,
  `tau = I`, between the representatives `(1,0,2)` and `(2,0,1)`.

## Minimal-polynomial argument

- The right-coset product formula is bundled first over holomorphic functions and then mapped to
  the function field. Hence the base-coset root annihilates the polynomial over `ℂ(Y)`.
- Right multiplication is transitive from the identity coset, and the corresponding
  `ℂ(Y)`-automorphisms send the base root to every conjugate. Thus all distinct right-coset
  roots annihilate the base root's minimal polynomial.
- The generic root-count lemma is stated over any target commutative domain. It yields
  `card iota ≤ natDegree (minpoly F alpha)`; its irreducibility corollary only assumes
  `p.natDegree ≤ card iota`.
- Cox's degree formula supplies equality with the number of right cosets. Since the minimal
  polynomial divides the monic modular polynomial, the two monic polynomials coincide.

## Validation

- `UpperHalfPlaneFunctionField.lean` and `CoxMatrices.lean` pass
  `-DwarningAsError=true`; the focused and 3889-job full-repository builds pass.
- `/tmp/T021Audit.lean` checks the public function-field chain,
  `modularPolynomialC_irreducibleInX`, and `theorem_11_18_ii`. Every audited declaration depends
  only on `propext`, `Classical.choice`, and `Quot.sound`; all enabled linters pass.
- Exact-type tests cover levels `m = 1, 2, 3`; their Cox cardinalities and polynomial degrees are
  respectively `1`, `3`, and `4`. A separate test checks that every coset root lies in the orbit
  of the base root under a `ℂ(Y)`-algebra automorphism.
- `git diff --check`, trailing-whitespace, 100-character line, proof-size, and forbidden-code
  gates pass. T021 source contains no `sorry`, heartbeat override, native decision code, or
  profiler scaffolding.
- The new file remains in the Cox subtree's legacy module mode because Lean forbids a `module`
  file from importing the legacy `CoxMatrices` module. A subtree-wide module migration is left
  to T029 rather than introducing a partial convention.

## Buzz

- Outcome: FAST-BOARD. Threshold-1000 ms profiles of the function-field and modular-polynomial
  files report no T021 declaration above the one-second budget after splitting the product-map
  and root-count proofs.

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
