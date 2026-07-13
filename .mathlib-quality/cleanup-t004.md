# Cleanup record: T004

## Baseline and scope

- Target: `periodPair_homothetic_iff_exists_sl2_smul_eq` in
  `XYin/PhD/Cox/LatticeJ.lean`.
- Baseline and final target build: `lake build XYin.PhD.Cox.LatticeJ`.
- Direct diagnostics show only the two planned sorries owned by T005.

## API and mathematical audit

- Ported the axiom-clean historical elementwise change-of-basis proof and re-audited every
  dependency. No shorter `Basis` or `latticeEquivProd` route was found: both would require more
  scalar-cast and submodule-equivalence plumbing.
- In the forward direction, lattice equality gives
  `αz = b + aw` and `α = d + cw`; hence `z = (aw+b)/(cw+d)`.
- The integral change-of-basis determinant is `±1`. Determinant `+1` produces a matrix sending
  `w` to `z`, so its inverse sends `z` to `w`. Determinant `-1` would send `w` to `-z`,
  contradicting positivity of imaginary parts.
- In the reverse direction, if `w = γ • z`, multiplication by `(cz+d)⁻¹` sends the lattice of
  `[1,z]` to the lattice of `[1,w]`, matching the direction of `PeriodPair.Homothetic`.

## Cleanup and simplify

- Kept only two genuine local helpers: normalized-lattice membership and uniqueness of integer
  coordinates. Both private names carry the `_aux` suffix.
- Removed the unused first coordinate equation from the second integer-combination comparison.
- Removed historical narrative comments inside the proof, packed all lines to at most 100
  columns, and retained descriptive public documentation.
- The elementwise proof remains preferable to a longer abstraction layer and exposes both
  integer coefficient transformations needed for review.

## Validation

- Focused file compilation and `lake build XYin.PhD.Cox.LatticeJ` pass.
- `#print axioms periodPair_homothetic_iff_exists_sl2_smul_eq` reports exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- Independent scratch tests construct the `T` homothety with scalar `1` and the `S` homothety
  with scalar `z⁻¹`; a third test checks the orbit conclusion is oriented as `γ • z = w`.
- All three sanity tests have the same standard-axiom set and no `sorryAx`.
- `git diff --check`, naming, line-packing, and no-unowned-sorry gates pass.

## Buzz

- Outcome: FAST-BOARD. A threshold-5 ms profiled compile found no declaration near the 1000 ms
  budget; the largest reported local tactic node was below 40 ms.
- No heartbeat override, profiler scaffold, or deferral remains.

## Phase checklist

- [x] Doctor
- [x] Prepare and read references
- [x] Style/API audit
- [x] Per-declaration golf and generality audit
- [x] Non-rename refactoring
- [x] Rename pass
- [x] Final diagnostics and gates
- [x] Simplify pass
- [x] Buzz pass
- [x] Report
