# Cumulative76: independent provenance verification

**PASS for the exact 76-module checkpoint**, audited after root confirmed the gate CLOSED. This checks source/output/setup/artifact provenance; it is not a fresh mathematical review of every declaration. The reviewer started no Lean compiler or build and changed no retained Lean source.

Root cumulative driver session **96300 closed with exit 0**. The actual receipt records `2026-10-04T05:24:15.676836+00:00`, **9513 jobs**, **76 modules**, **705 per-module axiom checks**, and **139 examples**. The parent `AINTLIBBridgeReceipt.json` is byte-identical to the working receipt. There are no target diagnostics, source/copy/inventory drift, module-check failures, `sorryAx`, or unexpected axioms.

- Receipt SHA256: `cc58b5e36c8e5a0ddaf9663e4e6f8be4277ca9ff267f3c37704519b2be3b9cf8`.
- Build-log SHA256: `04aa08a52d2ddacb081380da67d4d4dfc76e0bb2995ef87a75d7a3d43b888a4e`.
- Exact sorted 76-filename inventory SHA256: `857ca4f3b2b47ae2f964ef4a15d1e934487e5840da674f85506cb939fb9f8042`.
- Independent audit JSON: `/private/tmp/Cumulative76IndependentAudit.json`.

The independent script `/private/tmp/VerifyCumulative76.py` was prepared without executing it during the build. After root confirmed CLOSED 0 it ran as `python3 /private/tmp/VerifyCumulative76.py --expected-jobs 9513` and exited 0. The script SHA256 is `d0d91fd10ac24605377c5d2f7a7eac61721f0bb8c31c22585c5b202ac1e95698`.

The audit independently read all 76 retained sources, isolated copies, actual Lake traces, strict generated setups, and all **456** canonical artifacts (`.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, `.ir.sig`). The retained and working inventories equal the receipt's exact inventory; every source SHA matches it and every copy is byte-equal. Source print/example counts match all per-module traces and recorded totals.

Every trace's actual declaration-name set, axiom-free declarations, axiom union, and exact check count match its per-module receipt. Every individual printed dependency set is a subset of `propext`, `Classical.choice`, `Quot.sound`. There are **520 distinct audited declarations**; repeated primitive prints count independently per module. The 4 distinct axiom-free declarations are:

- `CategoryTheory.CommSq.w`.
- `CategoryTheory.Iso.hom_inv_id`.
- `CategoryTheory.Iso.inv_hom_id`.
- `RingHom.algebraMap_toAlgebra`.

All 76 generated setups have the correct module name, both implicit options false, and empty plugin/dynlib lists. Every recorded compiler command uses its actual matching source/setup and the exact pinned Lean binary, without an implicit-option override. Setup and trace hashes are recorded per module in the audit JSON.

All 456 canonical artifacts exist and are nonempty. Their current sizes and SHA256 hashes are recorded independently. The cumulative receipt has no expected per-artifact SHA fields, so this verifies availability/current hashes rather than comparing them against nonexistent expected artifact hashes. C outputs are not part of this six-artifact claim.

The actual successful build terminator is exactly `Build completed successfully (9513 jobs).` Actual Git HEAD values and the toolchain file match the fixed AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`, and `leanprover/lean4:v4.35.0-rc3` pins.

This checkpoint includes the native constant-compatible AlgEquiv and coordinate fraction-field contract, actual subgroup rank/degree/stalk wrappers, and all earlier retained modules. It does **not** prove native genus, quotient genus, a quotient Weierstrass model, target-j, the modular-polynomial identity, or a normalization comparison. Any later temporary proof, leaf, or changed source outside the exact 76-file snapshot requires separate verification. Historical checkpoints remain historical evidence with their original inventories and times.
