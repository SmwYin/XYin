# Cleanup record: T022

## Scope

- Targets: canonical period pairs for cyclic sublattices, their HNF, scaling, and the
  dual-isogeny operation.
- Supporting APIs: `PeriodPair.smulLatticeEquiv` and an arbitrary-basis form of the rank-two
  primitive-matrix/cyclic-quotient criterion.

## Canonical period pair

- A direct `Mathlib.GroupTheory.IndexNSmul` import supplies the finite-index rank theorem.
  The carrier therefore has rank two, so the existing Smith-style HNF choice applies.
- The two HNF basis columns are expanded in `L.latticeBasis`. Positive diagonal entries and
  the zero lower-left entry make the resulting complex periods real-linearly independent.
- `toPeriodPair_lattice` is proved in both directions by expanding elements in the HNF basis;
  the chosen period pair spans exactly `S.carrier.map L.lattice.subtype`.
- Consequently the lattice and its `j`-invariant depend only on the carrier, not on proof fields
  stored in the cyclic-sublattice structure.

## Scaling

- `PeriodPair.smulLatticeEquiv` restricts multiplication by a complex unit to the original and
  scaled period lattices, with simp lemmas for it and its inverse.
- `scale` maps the carrier through that equivalence. `AddSubgroup.index_map_equiv` preserves the
  index, while `Submodule.Quotient.equiv` transports cyclicity of the quotient.
- The embedded scaled carrier is multiplication by the same unit in `ℂ`. Hence its canonical
  period lattice is the lattice of `a • S.toPeriodPair`, and `j_scale` follows from `j_congr`
  and `j_smul`.

## Dual inclusion

- The canonical equivalence from `S.carrier` to `S.toPeriodPair.lattice` sends the map
  `x ↦ m • x` to a full-rank submodule. Its range is the carrier of `S.dual`.
- If the original HNF matrix is `!![d,b;0,a]`, the dual inclusion matrix in transported bases is
  its adjugate `!![a,-b;0,d]`.
- The determinant remains `ad = m`, so the dual index is `m`. The four-entry content is unchanged;
  since the original quotient is cyclic, the generalized primitive-matrix theorem proves that
  the dual quotient is cyclic as well.
- `dual_carrier_map_subtype` and `dual_toPeriodPair_lattice` identify the dual carrier and its
  period lattice with `mL`. This gives `dual_sub_j`; `dual_base_j` is definitional.

## Generalized HNF support

- `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` states the T008 content criterion for
  any ambient and submodule bases. The existing HNF theorem is retained as a short corollary, so
  no prior call site changes.
- The proof still uses arbitrary Smith coefficients only as a decomposition tool and makes no
  invariant-factor normalization assumption.

## Validation and quality gates

- `/tmp/T022Audit.lean` checks all public statements, scaling by `2` and `I`, carrier-only lattice
  and `j` invariance, the dual `j` identity, and the top/diagonal level-one inclusion.
- All audited declarations, including the new lattice equivalence and generalized content
  theorem, depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- The focused build and the 3890-job full repository build pass. Remaining `sorry` warnings in
  `CyclicSublattice.lean` belong only to T023 and T024.
- `git diff --check`, trailing-whitespace, 100-character line, forbidden-code, and public API
  gates pass.
- The first threshold-1000 ms profile exposed three expensive private coordinate proofs. They
  were split into fixed-coordinate lemmas and narrowed to `simp only`; the final profile reports
  no T022 declaration above one second.

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
