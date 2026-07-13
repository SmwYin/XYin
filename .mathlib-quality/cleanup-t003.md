# Cleanup record: T003

## Baseline and scope

- Target: discriminant nonvanishing and lattice `j` classification in
  `XYin/PhD/Cox/LatticeJ.lean`.
- Public declarations: `exists_homothetic_periodPair`,
  `PeriodPair.discriminant_ne_zero`, `PeriodPair.j_eq_of_homothetic`,
  `PeriodPair.homothetic_of_j_eq`, and `PeriodPair.j_eq_iff_homothetic`.
- Baseline and final target build: `lake build XYin.PhD.Cox.LatticeJ`.
- Direct diagnostics show only the three planned sorries owned by T004 and T005.

## API and statement audit

- Moved the T003 declarations after `UpperHalfPlane.periodPair` and the T002 invariant bridge;
  their original source order made the intended normalization proof impossible.
- Normalization chooses `ω₂ / ω₁` when its imaginary part is positive and swaps the periods when
  it is negative. Linear independence excludes zero imaginary part.
- Nonvanishing uses the clean eta/discriminant theorem
  `ModularForm.discriminant_ne_zero`; its axiom audit has no `sorryAx`.
- Equal invariants are converted to equal lattices only through the axiom-clean theorem
  `PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq` from `XYin/uniqueness.lean`.
- The public theorem statements retain their planned specificity and argument orientation.

## Cleanup and simplify

- Replaced six one-direction exceptional-case helpers by two reusable iff helpers:
  `j = 0 ↔ g₂ = 0` and `j = 1728 ↔ g₃ = 0`, each under discriminant nonvanishing.
- Kept the three mathematical branches visible: `g₂ = 0`, `g₃ = 0`, and the generic case.
- In the exceptional branches, a sixth or fourth root makes the nonzero invariant agree. In the
  generic branch, a square root of the invariant ratio gives compatible fourth and sixth powers.
- Removed semicolon tactic chains, packed all lines to at most 100 columns, and suffixed private
  helper names with `_aux`.
- No theorem statement, definition body, inequality orientation, or namespace-level API was
  weakened during cleanup.

## Validation

- Focused file compilation and `lake build XYin.PhD.Cox.LatticeJ` pass.
- `#print axioms` for all five public declarations reports exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- Independent scratch tests cover normalization and both exceptional branches (`j = 0` and
  `j = 1728`) without invoking the public hard-direction theorem.
- `git diff --check`, naming, line-packing, forbidden-tactic, and no-unowned-sorry scans pass.

## Buzz

- Outcome: FAST-BOARD. A threshold-1 ms profiled compile found no declaration near the 1000 ms
  budget; the largest reported local tactic nodes were below 40 ms.
- No heartbeat override, profiler scaffold, or deferral remains.

## Phase checklist

- [x] Doctor
- [x] Prepare and read references
- [x] Style/API audit
- [x] File-level declaration-order fix
- [x] Per-declaration golf and generality audit
- [x] Non-rename refactoring
- [x] Rename pass
- [x] Final diagnostics and gates
- [x] Simplify pass
- [x] Buzz pass
- [x] Report
