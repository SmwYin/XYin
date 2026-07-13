# Cleanup record: T009

## Baseline and scope

- Targets: the modular-function base API in `XYin/PhD/Cox/ModularFunction.lean`.
- Added the generic cusp-width lemma `meromorphicAt_cuspFunction_nat_mul` to
  `XYin/PhD/LaurentQExpansion/LaurentQExpansion.lean` rather than retaining a Cox-local copy.
- Focused and full-repository `lake build` both pass.

## API and mathematical audit

- `periodic_comp_sl2` uses `γ T^N γ⁻¹`; its lower-left entry is
  `-N * (γ 1 0)^2`, hence the conjugate lies in `Γ₀(N)`.
- `cusp_laurent_finitePrincipalPart` chooses the negative cusp pole order, so all lower Laurent
  coefficients vanish.
- Analytic `j` is meromorphic on the upper half-plane, invariant under every `SL₂(ℤ)` element,
  and meromorphic at every width-`N` cusp by the generic natural-width composition lemma.
- For `levelJ N`, left reduction gives
  `δ⁻¹ * diag(N, 1) * γ = [[g, r], [0, s]]` with positive `g,s` and `g*s=N`.
  Thus the transformed function is `j(r/s + (g/s)τ)`, whose cusp coordinate is
  `exp(2πir/s) * q^(g*g)`.  Composition with this analytic map proves meromorphicity at every
  cusp, not only at infinity.

## Cleanup and simplify

- Factored the shared `ofComplex` upper/non-upper-half-plane case split into
  `periodic_comp_ofComplex_of_vadd`.
- Split cusp normalization into first-column gcd reduction, positive upper-triangularization,
  and a short level-specific wrapper.
- Split the Möbius calculation into a pure complex identity, an action-coercion identity, and a
  short matrix-entry bridge.
- Extracted `qParam_affineUpperHalfPlane`; all new proof bodies are below 30 lines and all target
  lines are at most 100 characters.
- Kept implementation-only normalization and action helpers private; generic cusp-width
  meromorphicity is public in the Laurent API.

## Validation

- `/tmp/T009Validation.lean` checks arbitrary-cusp meromorphicity explicitly for `S` and `T`,
  checks period `N` after precomposition by `S`, and audits all five public targets.
- Every public T009 theorem and the new Laurent helper depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
- Independent reviews rechecked the matrix direction, positivity and product `g*s=N`, exponent
  `g*g`, punctured-neighborhood congruence, and absence of circular dependencies.
- `git diff --check`, target no-sorry, width gates, focused build, and the 3867-job full build
  pass.  The five remaining sorries in `ModularFunction.lean` belong to later tickets.

## Buzz

- Outcome: FAST-BOARD.  A threshold-100 ms profiled compile reports the slowest target proof,
  `periodic_comp_sl2`, at about 0.57 s; every declaration is below the 1000 ms budget.
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
