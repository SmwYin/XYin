# Actual raw local quotient rank verification

The retained module `AINTLIBDrafts.YZeroCoarseRawLocalQuotientRank` proves
`AffineChartPatch.localQuotientOpenπ_finrank P r hG y` for the actual raw
local quotient projection used in the gluing construction. The subgroup rank is
supplied by `G.HasRank r`; the only additional hypothesis is the actual patch's
`Module.Free P.baseRing P.groupRing`. No Noetherian, étale, domain or model premise
is added.

The existing `localQuotientOpenIso` is the honest spectrum isomorphism arising
from the literal raw-invariant-subring equality and the coinvariant carrier ring
equivalence. Its actual projection triangle gives a pullback square with the
identity on the common source and this target isomorphism. The actual raw finite
and flat projection proofs imply those properties for the canonical projection;
`finrank_of_isPullback` then transports the retained canonical rank theorem to
the actual raw target point's isomorphic image. No rank comparison is assumed.

Two actual API examples check an arbitrary ranked subgroup and the marked-axis
subgroup's proved rank `N`. This leaf does not assert global quotient rank or any
function-field degree and does not use held NIsogeny quotient-curve declarations.

## Exact verification

- Approved temporary source: 65 lines, SHA `0d0f8f65c3b15e2893bac7d561f38894f9faf4b91f1d251920429b5c696069d5`. Its first strict run was
  session 83337 CLOSED exit 0, with no failed staging source or diagnostics.
- Retained source: 84 lines, width 93, SHA `274a4ed17e4fc332fc5711bb3b423aa7fd9464e80631bc9a8a34d29e5fcadbca`.
  Both source copies are byte-identical; the entire approved mathematical suffix
  beginning `@[expose] public section` is byte-preserved.
- Correct-name strict emission: session 34900 CLOSED exit 0 on pinned Lean
  4.35.0-rc3, module name `AINTLIBDrafts.YZeroCoarseRawLocalQuotientRank`. Both implicit-variable
  options are false; 9458 normalized import artifacts are available.
- All ten exact axiom prints are the standard three `propext`, `Classical.choice`,
  `Quot.sound`. Two genuine API examples passed; own errors/warnings: zero.
- Log `/private/tmp/xyin-y0-raw-local-quotient-rank-check.log`, SHA `0f7c6f2ac2e656578b5c5dbf5c066a813e2bd36588c6b69852e20dad0e74d5d6`.
- Setup SHA `5160f05e247cf0b3cf68ea9983d5a4093e03beaf6e2d3d989500b04ff656120e`.
- Six Lean artifacts were inspected nonempty: sizes
  12456, 27992, 2048, 15146, 176, 1584. Explicit C output: 3603 bytes.
- Full command/named prints/source/setup/log/artifact hash receipt:
  `/private/tmp/xyin-y0-raw-local-quotient-rank-receipt.json`.

No global build or environment/model/settings changes were performed for this
bounded named check. The approved temporary source and retained leaf are frozen
at this receipt.
