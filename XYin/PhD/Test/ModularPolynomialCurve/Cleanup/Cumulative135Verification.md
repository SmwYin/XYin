# Final cumulative135 verification

Checkpoint: **2026-10-04T09:19:50.190688+00:00**. Root driver session
**42018 owner-polled CLOSED, exit 0**; native Lake completed **9599 jobs**.
Independent verifier session **26595 owner-polled CLOSED, exit 0** (chunk
`1baf3e`). Root also inspected the audit and recomputed all 810 current artifact
hashes, every module's metadata and the frozen post99 ordered output matrix.

| Quantity | Verified |
| --- | ---: |
| Retained modules | 135 |
| Exact ordered declaration/axiom outputs | 1263 |
| Actual sanity/API examples, including noncomputable examples | 258 |
| Distinct printed declarations | 804 |
| Axiom-free declarations | 12 |
| Individually hashed canonical outputs | 810 |
| Own warning/error diagnostics | 0 |

Before building, root recorded and removed only the 135 experimental modules'
own `.olean` files. Native and mathlib artifacts were untouched. All sources,
isolated copies, exact inventory, native configurations, named receipts and
compiler identity were frozen first. All original126 Lean sources remain
byte-exact. The unchanged99 modules' exact declaration names, order and axiom
subsets match the immutable historical independent audit; all 36 post99 modules
match their successful correct-name checks frozen before this run.

Every trace uses the exact pinned Lean executable and correct module name.
Every setup has `autoImplicit=false`, `relaxedAutoImplicit=false`, and no plugins
or dynlibs. The six canonical outputs are `.olean`, `.olean.private`,
`.olean.server`, `.ilean`, `.ir`, and `.ir.sig`. The verifier checks each source,
trace, setup and current artifact. Work and parent receipts are byte-equal.
No `sorryAx`, unexpected axiom, missing output, own diagnostic or source/config
drift was accepted. The allowed axioms are `propext`, `Classical.choice` and
`Quot.sound`, including proper subsets and axiom-free declarations.

The parser handles legal apostrophes and multiline axiom lists. Earlier staging
failures and the separately recorded injectivity-receipt parser repair remain
historical; neither changed a successful Lean proof or the allowed axioms.
Native historical warnings remain in the full log. Importing a file containing
`sorry` was not treated as proof: actual checked axiom dependencies are decisive.

AINTLIB is pinned to `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib to
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean to
`leanprover/lean4:v4.35.0-rc3`. The main XYin toolchain was not upgraded.

## Preserved provenance

- Receipt SHA: `0fe73568fa9d2df3c744d4c4d9a48ef7bec6ecc9bd4eeead06714e59e1260856`.
- Full build log SHA: `39e85c74ca86f6fe043796a201e623f0baf3ed0545351eafd94064d0c382edbb`.
- Independent audit SHA: `2b5cab313b52ebde2b021b6d0122a3a5325dc33f008486ea9904776c4d6c6582`.
- Prepared source snapshot SHA: `0e2cc8a84c2be4fa22e10b1329e39de35ba4f95e505c78ccc7dea998c53fc1a8`.
- Prepared direct-check matrix SHA: `012213af901698487f9ca7cd402511230ff770fec1279d680e631b85d9552b16`.
- Inventory SHA: `26c038ba820121daca1436fe912bf52034744532f495871521bf466cec1938bf`.
- Owned-olean invalidation SHA: `5fde807876f2838d417c0e2e6f12a462468e45e725f034d910f0f3963cefcaa9`.

Exact audit command:

```text
python3 /private/tmp/VerifyCumulativePost99.py --expected-jobs 9599 --expected-modules 135 --expected-checks 1263 --expected-examples 258 --cumulative-session 42018 --expected-receipt-sha256 0fe73568fa9d2df3c744d4c4d9a48ef7bec6ecc9bd4eeead06714e59e1260856 --prepared-source-snapshot /private/tmp/CumulativeFinalPreparedSourceSnapshot.json --prepared-direct-checks /private/tmp/CumulativeFinalPreparedDirectChecks.json --output /private/tmp/CumulativeFinalIndependentAudit.json
```

Receipt, audit, full log, prepared snapshot/matrix, invalidation record and exact
preparer/verifier scripts are preserved under `Checkpoints/` with `135` names.
Script copies retain original paths and serve as provenance; replay requires
those dependencies or explicit corresponding paths. Historical99 and126
receipts, audits, snapshots and logs remain byte-exact. Historical artifact
hashes describe their own checkpoint, not the newly rebuilt current artifacts.

This is a source/compiler-output provenance audit, **not** a fresh full
mathematical review of every proof. The bounded mathematical reviews were
performed separately and recorded in individual companions. Every currently
retained leaf is included; temporary failed probes are excluded.

The final nine modules establish genuine closed-point/place interfaces,
valuation restriction, finite-fiber additive divisor pullback and actual
characteristic-zero principal-divisor compatibility. They do not prove quotient
genus, a quotient Weierstrass model, target-j, a modular-polynomial identity or
the final actual `YZeroCoarse` normalization comparison. All proof/compiler
workers stopped after this checkpoint to respect the user's reset/credit limit.
