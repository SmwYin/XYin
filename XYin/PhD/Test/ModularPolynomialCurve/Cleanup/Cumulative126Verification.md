# Cumulative126 independent provenance verification

Verified checkpoint: `2026-10-04T08:24:33.531911+00:00`.
Root driver session **49026 owner-polled CLOSED, exit 0**; native Lake build
completed **9590 jobs**. Independent audit completed synchronously with **exit 0**
(tool chunk `ed54b8`, no continuing session). This audit started no Lean compiler.

| Quantity | Verified |
| --- | ---: |
| Exact retained modules | 126 |
| Exact ordered declaration/axiom outputs | 1171 |
| Actual sanity examples, including noncomputable examples | 240 |
| Distinct printed declarations | 749 |
| Axiom-free declarations | 11 |
| Individually hashed canonical outputs | 756 |
| Own warning/error diagnostics | 0 |

Before building, root removed only the 126 experimental modules' own `.olean`
files, with their old hashes recorded. Native and mathlib artifacts were untouched.
All retained sources, isolated copies, exact inventory, native configuration and
compiler identity were frozen before the build. The final receipt confirms no
source or inventory change, and the independent audit checks every source hash,
trace, strict setup and current canonical output against that frozen snapshot.

The canonical outputs are `.olean`, `.olean.private`, `.olean.server`, `.ilean`,
`.ir`, and `.ir.sig`. Every setup uses the correct module name,
`autoImplicit=false`, `relaxedAutoImplicit=false`, and no plugins or dynlibs.
Every compiler trace uses the exact pinned Lean executable without overrides.
Parent and work receipts are byte-equal.

The 99 unchanged modules' exact declaration names, order and axiom subsets match
the immutable historical99 independent audit. The 27 additional modules match
their correct-name, closed successful individual checks frozen before this run.
The parser supports legal apostrophes and axiom-free declarations. The only
permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`,
unexpected axiom, missing output, own diagnostic or drift was accepted.

The injectivity leaf's earlier individual receipt had a metadata parser error
joining an axiom-free line to the next declaration. Before freezing, root repaired
only its ordered checks and added explicit repair provenance, keeping the previous
receipt byte-exact in a separate archive. Its Lean source, successful named log,
setup and compiled artifacts were unchanged. The prepared matrix and this audit
check the corrected nine exact outputs, including the axiom-free declaration.

The native pins remain AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and
`leanprover/lean4:v4.35.0-rc3`. The main XYin toolchain was not upgraded.
Native historical warnings are preserved in the full log. Imported files that
contain `sorry` were not treated as proven dependencies: the checked declarations'
actual axiom lists remain the decisive test.

## Exact provenance

- Final receipt SHA:
  `c209f48a1fe7fae8e54648cb8a77d3530921340db017ac9697a3eda34cc2f30c`.
- Full build log SHA:
  `d11e316b1bffe0e61157c80811823dfff5450511fd17f5e237054cf7b93eddb6`.
- Independent audit SHA:
  `86e50202963f2ec6a2edaf352a2c32bba54781897c4eb1c2ddcfa4651b48eb16`.
- Prepared source snapshot SHA:
  `4d38e20e1b90f284d127ca89fb5497e851208b9e09f4b635ef0c8c8c1cbf5c9f`.
- Prepared direct-check matrix SHA:
  `ced7afb7053b6b9a862dbe1d31f1df9cce00c01a8aed429bcd85124334e318f4`.
- Exact inventory SHA:
  `ad8a38c57041d2343937aaafc981bd5ca10c5fd3ca050808c5392461467e439a`.

Executed audit command:

```text
python3 /private/tmp/VerifyCumulativePost99.py --expected-jobs 9590 --expected-modules 126 --expected-checks 1171 --expected-examples 240 --cumulative-session 49026 --expected-receipt-sha256 c209f48a1fe7fae8e54648cb8a77d3530921340db017ac9697a3eda34cc2f30c
```

Receipt, full build log, independent audit, prepared matrix/snapshot, invalidation
record and exact preparation/verifier scripts are preserved under `Checkpoints/`
with `126` names. Script copies retain their original paths in their contents and
serve as provenance; executing them elsewhere requires supplying/preparing those
same dependencies. Historical99 receipt, audit and archived log remain byte-exact.

This is a source/compiler-output provenance audit. It complements the individual
mathematical reviews and is not a new full mathematical review of every proof.
Temporary probes and later leaves absent from this exact inventory are outside
the checkpoint. It proves no quotient genus, target-j or final coarse comparison.
