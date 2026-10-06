# Cumulative47 receipt: independent provenance audit

Audit date: 2026-10-04. **PASS for the exact 47-module checkpoint.** This is
a source/output/setup/artifact provenance audit, not a fresh mathematical
review of every declaration. The reviewer started no compiler or build.

## Checkpoint

Root's cumulative driver **49724 closed with exit 0**. The actual receipt
`/private/tmp/xyin-y0-aintlib-work/yzero-bridge-receipt.json` records
`2026-10-04T03:08:48.089600+00:00`, 47 modules, 418 axiom-print checks,
77 examples, and zero diagnostics, source drift, inventory drift, module
failures, `sorryAx`, or unexpected axioms. The actual build log ends with
`Build completed successfully (9477 jobs).`

Receipt SHA-256:
`431f42363d61a96c149635059290ef3e58e72d52289c34e97206d10af7de9269`.
Build-log SHA-256:
`acf3707351754855f5f980164cb2cba82a7db94aa2ebddd57d7edb5fdb922b1e`.

The receipt pins are AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
The actual isolated AINTLIB and mathlib Git HEAD values were checked against
their recorded revisions; no environment or model settings were changed.

## Independent checks performed

The small script `/private/tmp/VerifyCumulative47.py` verifies the receipt's
explicit 47-file subset and writes
`/private/tmp/Cumulative47IndependentAudit.json`.

- All 47 current retained source hashes match the receipt, and every isolated
  source copy is byte-equal. Targets, source-hash keys, and per-module receipt
  inventories agree exactly.
- All 47 actual Lake `.trace` files were read. Their exact axiom-print counts,
  declaration-name sets, axiom-free declarations, and axiom unions agree with
  each per-module receipt. Every printed dependency set is contained in the
  standard three axioms; there are no own warnings/errors or `sorryAx`.
- Source inventories independently contain exactly 418 axiom-print statements
  and 77 examples for the checkpoint subset. These agree with the observed
  trace output and the receipt totals.
- All 47 actual generated setups have the correct module names, both implicit
  options false, and empty plugin and dynamic-library lists. Every recorded
  compiler trace uses its matching generated setup and source path.
- All 282 artifacts across the six suffixes `.olean`, `.olean.private`,
  `.olean.server`, `.ilean`, `.ir`, and `.ir.sig` exist and are nonempty.
  Their current sizes and SHA-256 hashes were read and recorded in the
  independent audit JSON. The cumulative receipt does not contain expected
  per-artifact SHA values, so this is availability/current-hash evidence,
  not a comparison against nonexistent artifact hash fields.

The independent script completed with exit 0. No build was repeated and no
Lean source was modified for this audit.

## Boundary

This confirms consistency of the actual cumulative compiler evidence with
the current source files in that checkpoint. It does not prove additional
mathematical statements or replace the individual source reviews.

The subsequently retained `YZeroCoarseStandardSmoothRankConverse.lean` is
outside this 47-module receipt and has its own named strict verification.
It is deliberately excluded from this audit's inventory and counts. The
earlier cumulative39 receipt remains a historical checkpoint.
