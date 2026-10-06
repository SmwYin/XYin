# Cumulative99 independent provenance verification

Verified checkpoint: `2026-10-04T06:54:23.208551+00:00`.
Root cumulative driver **28990 owner-polled CLOSED, exit 0**, native Lake build
9563 jobs. Independent Python audit **72299 owner-polled CLOSED, exit 0**.
No Lean compiler or dependency build was started by this audit.

| Checkpoint quantity | Verified |
| --- | ---: |
| Exact retained modules | 99 |
| Per-module expected and observed axiom outputs | 935 |
| Actual `example` and `noncomputable example` declarations | 186 |
| Distinct printed declarations | 635 |
| Axiom-free declarations | 5 |
| Nonempty canonical outputs, individually hashed | 594 |
| Own warning/error diagnostics | 0 |

The retained and isolated source inventories match exactly, with no extra source,
missing source, hash drift, or source mutation during the cumulative build. Every
source hash matches the prepared frozen snapshot and final parent/work receipt.
Parent and work receipts are byte-equal. The canonical outputs checked for every
module are `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, and `.ir.sig`.
The independent JSON contains each current output's size and SHA256 (total
11,558,086 bytes), each trace/setup hash, and every exact declaration/axiom pair.

Each module's exact declaration order and axiom subsets are matched against the
independent historical76 audit (76 unchanged sources) or its matching closed,
correct-name frozen receipt and full named log (23 new leaves). The three permitted
axioms remain `propext`, `Classical.choice`, and `Quot.sound`; smaller actual subsets
and axiom-free declarations are preserved exactly. Every trace matches the final
per-module receipt counts, audited names, axiom-free names, and observed union.
No `sorryAx`, unexpected axiom, module-check failure, or source inventory drift
was accepted.

All 99 setups have the correct module name, `autoImplicit=false` and
`relaxedAutoImplicit=false`, with no plugins/dynlibs. Each trace uses the exact
pinned Lean binary and correct setup/source paths, without command-line overrides
of those implicit options. Native Git heads and the toolchain match:

- AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`.
- Mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`.
- `leanprover/lean4:v4.35.0-rc3`.

## Validator repair and preserved history

The first99 driver session15551 exited1 although its native Lean build succeeded
with9563 jobs: the old name parser omitted the legal trailing-apostrophe declaration
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk'`. Its failed validator receipt,
source/log history were preserved. The corrected validator reads the exact closing
`' depends on axioms` / `' does not depend on any axioms` terminator and counts
`noncomputable example` as well. This adds the genuine second NativePatchBaseField
example to the former185 counter, giving186. It changes no mathematical statement,
Lean proof, implicit setting, pin, axiom whitelist, or expected axiom-output count.

A reverse transformation of only those four capture expressions and the example
counter recovers the precise earlier driver hash. The independent audit supports
those same legal declaration names while keeping all previous source, exact-print,
whitelist, trace, setup, artifact and pin assertions. Previous prepared99 snapshots,
script and direct-check matrix were archived as `*-before-parser-repair.*`.
The historical76 checkpoint remains separate and unchanged.

## Exact provenance

- Final parent/work receipt SHA:
  `68e7577379b1c9437041b69fc446da10374ea34226e58a38f118be44a20f0b04`.
- Final build-log SHA:
  `6ee059ff33170d0cc45a465dece62a3c97231b3f2a4f757b29a5a84bb5d9af11`.
- Prepared source-snapshot SHA:
  `ad83a68562f93ef4d378cd02ac33eef6933106c1d44c3a6da41e76da4c015db1`.
- Exact99 inventory SHA:
  `40c9c440ac4f919aad27937af2fb0b794304f9e624cec4ecd43f5f73ff2cd702`.
- Independent auditor script SHA:
  `f21849f1ff6ff5d5eaa172cadc04b93f19a78aa1627bd802c2d51eb12a4f71e8`.
- Independent JSON SHA:
  `5303be5536bed1ffc78138bdc5f371aaf97502c73ab4b28052751eee6a1b63c4`.

Executed command:

```text
python3 /private/tmp/VerifyCumulative99.py --expected-jobs 9563 --expected-modules 99 --expected-checks 935 --expected-examples 186 --cumulative-session 28990 --expected-receipt-sha256 68e7577379b1c9437041b69fc446da10374ea34226e58a38f118be44a20f0b04
```

Full independent output: `/private/tmp/Cumulative99IndependentAudit.log`.
Detailed current per-module provenance: `/private/tmp/Cumulative99IndependentAudit.json`.
This is a receipt/source/compiler-output provenance audit, not a new full mathematical
review of all99 proofs. Temporary proofs and later leaves absent from the exact99
inventory are outside this checkpoint.
