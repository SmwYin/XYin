# Cleanup record: T024

## Scope

- Targets: the normalized product-root classification and Cox Theorem 11.23.
- Supporting API: transport cyclic sublattices along arbitrary lattice linear equivalences and
  along equality of the underlying complex lattices.

## Proof architecture

- `CoxMatrix.toCyclicSublattice_j` combines the exact T023 lattice identity, invariance under
  unit scaling, and the analytic/lattice `j` bridge.
- The normalized theorem rewrites the specialized modular polynomial to its finite product and
  identifies its roots directly with the two round trips of the T023 equivalence.
- The global forward direction chooses an upper-half-plane preimage by surjectivity of analytic
  `j`. The reverse direction normalizes the ambient period pair, transports the sublattice by
  the same scaling unit, and preserves both index and cyclicity through quotient equivalences.
- The root order is explicitly `(u,v) = (S.j,L.j)`. An adversarial scale-by-two test confirms
  that the reverse construction uses `S.scale a`, not `a⁻¹`.

## API and file cleanup

- The general `CyclicSublattice.map` centralizes index and cyclic-quotient transport; `scale` and
  `ofLatticeEq` are thin specializations rather than duplicate constructions.
- The former 1076-line file was split into a 674-line reusable core and a 426-line
  `CyclicSublattice/Classification.lean`. The core no longer imports the modular-polynomial
  layer, and the import graph remains acyclic.
- A final golf pass shortened the subgroup-index transport and both target proofs while keeping
  the semantic bridge and public transport API explicit.

## Validation and quality gates

- Both split files pass direct `-DwarningAsError=true`; threshold-1000 ms profiling reports no
  slow declaration.
- `/tmp/T024Audit.lean` checks normalized roots, both global directions, transport preservation,
  and the exact `(u,v)` order. An independent adversarial audit covers `m = 1`, the non-diagonal
  `m = 2` representative, and nontrivial scaling.
- All audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; none
  depends on `sorryAx`.
- The 3891-job full build, `git diff --check`, the 100-character gate, strict source builds,
  independent structural/mathematical reviews, and post-golf audit all pass.

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
