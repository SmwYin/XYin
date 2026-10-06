# Cumulative60 receipt: independent provenance audit

Audit date: 2026-10-04. **PASS for the exact 60-module checkpoint.** This is a source/output/setup/artifact provenance audit, not a fresh mathematical review of every declaration. The reviewer started no compiler or build and changed no Lean source.

## Checkpoint

Root's cumulative driver **71884 closed with exit 0**. The actual receipt `/private/tmp/xyin-y0-aintlib-work/yzero-bridge-receipt.json` records `2026-10-04T04:11:35.651509+00:00`, 60 modules, **549 per-module axiom-print checks**, **105 examples**, and zero own diagnostics, source drift, inventory drift, module failures, `sorryAx`, or unexpected axioms. The build log ends with `Build completed successfully (9490 jobs).` The permanent `AINTLIBBridgeReceipt.json` is byte-identical to the actual driver receipt.

Receipt SHA-256: `991f5980a40a478f2d04bfad3b10039110ed00e9d0ad715fc9af72e6c8461bd0`.

Build-log SHA-256: `a86e6f20059d271e4566ee4fa4ffc0ae31dd851e6bb89ac401242dda0029fca0`.

Exact 60-filename inventory SHA-256, with sorted names separated by newlines: `1e9ff3a8ba5b1b4e6fe13fd043e7ca54757d0f1dbb2d6241c71319b1cfa6ffa8`.

The receipt pins are AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `leanprover/lean4:v4.35.0-rc3`. The actual isolated AINTLIB and mathlib Git HEAD values and the isolated `lean-toolchain` file match those recorded values. Every compiler trace names the exact pinned 4.35.0-rc3 binary. No environment or model setting was changed.

## Independent checks performed

The small script `/private/tmp/VerifyCumulative60.py` verifies the receipt's explicit 60-file subset and writes `/private/tmp/Cumulative60IndependentAudit.json`.

- All 60 current retained source hashes match the receipt. Every isolated source copy is byte-equal. Targets, source-hash keys, and per-module receipt inventories agree exactly. At audit time the retained directory has exactly these 60 Lean files.
- All 60 actual Lake `.trace` files were read. Exact output counts, declaration-name sets, axiom-free declarations, and axiom unions agree with each per-module receipt. Every printed dependency set is a subset of `propext`, `Classical.choice`, and `Quot.sound`. There are no target warnings/errors or `sorryAx`.
- The source files contain exactly 549 axiom-print statements and 105 examples for this subset. Counts agree with the observed trace output and receipt totals. The checks cover 437 distinct fully qualified declaration names, with repeated primitive prints counted separately per module; three distinct declarations are axiom-free.
- All 60 generated setups have correct module names, both implicit options false, and empty plugin/dynamic-library lists. Each trace uses its matching source and generated setup with the exact pinned Lean binary and no implicit-option command-line override. Setup and trace current hashes are recorded per module in the independent audit JSON.
- All **360** canonical artifacts across `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, and `.ir.sig` exist and are nonempty. Their current sizes and SHA-256 hashes were independently read and recorded. The cumulative receipt has no expected per-artifact SHA fields, so this supplies availability/current-hash evidence rather than a comparison against nonexistent artifact-hash fields.
- The actual build log was read and hashed, its 9490-job successful terminator checked, and the two native repository revisions compared with the receipt.

The independent script completed with exit 0. No build was repeated for this audit.

## Boundary

This confirms consistency of the actual cumulative compiler evidence with the current 60-source checkpoint, including `NativeFieldWeierstrassModel.lean`. It does not prove further mathematical statements or replace the individual source reviews.

Any temporary proof, new retained leaf, or later source change outside this exact 60-file inventory is excluded. In particular, post-barrier Hopf-rank and generic-degree probes are not covered by this checkpoint. Historical47 remains a separate historical receipt; its earlier counts are not presented as current60 evidence.
