# Actual quotient etaleness: independent review

Review date: 2026-10-04. **PASS for the actual retained source and named strict
receipt.** This is a source/API/output review only; the reviewer made no Lean
source changes and started no compiler.

## Frozen source and retention delta

[YZeroCoarseSubgroupQuotientEtale.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseSubgroupQuotientEtale.lean)
has 99 lines, SHA-256
`cfe54fd24eeb2f53bb10881ef373b2e6f2d2dc4b867cc5dd7e26e3c87b4f82e2`.
The retained and isolated sources are byte-equal. Independent comment removal
restores exactly the approved 77-line temporary program. The retention delta
adds only license/header and module scope documentation.

## Mathematical review

The generic theorem has the explicit input `[Etale G.π]`, where `G.π` is the
**subgroup's** projection to the base. This differs from the quotient
projection being proved étale, so it is not a circular assumption.
On every actual free glue patch, the checked local invariant-ring theorem
gives etaleness of the local quotient projection. Target-locality checks the
actual `pullback.snd` on the quotient's target chart cover. The actual chart
pullback square, flipped, identifies this restriction with the comparison
isomorphism's inverse followed by that local quotient projection.
`isoPullback_inv_snd` and composition preserve the desired property in the
correct direction.

The chosen-killing wrapper uses exactly `G.killN` and `G.killN_spec`.
For the actual marked constant-axis subgroup over arbitrary `Spec R`, the
proof explicitly installs the independently proved subgroup etaleness
`sectionAxisSubgroup_etale` and its direct killing datum. It then applies
the generic theorem. The native level-3 example instantiates the actual
full-point pullback curve and marking. No Noetherian, domain, quotient
Weierstrass, or quotient smoothness assumption is added.

## Named receipt

Named emission session **62881 closed with exit 0**. The actual log
`/private/tmp/xyin-y0-subgroup-quotient-etale.log` has twelve exact
standard-three axiom checks, two passing examples, and no warnings/errors or
`sorryAx`. The setup names
`AINTLIBDrafts.YZeroCoarseSubgroupQuotientEtale`, has both implicit options
false, and has no plugins or dynamic libraries.

All canonical artifacts recorded in
`/private/tmp/YZeroCoarseSubgroupQuotientEtale-receipt.json` were independently
checked on disk: `.olean` 15888 bytes, `.olean.private` 31464,
`.olean.server` 2992, `.ilean` 15876, `.ir` 1728, `.ir.sig` 176,
and `.c` 4215. The receipt records sizes rather than artifact SHA values;
no unrecorded SHA comparison is claimed.

## Boundary

The actual quotient projection is étale under an étale subgroup projection;
the literal marked-axis application supplies that input. This leaf does not
construct the quotient's elliptic curve record, target `j`, or modular
polynomial comparison. It does not invoke the held `NIsogeny` upgrade or
sorried smooth/LFP descent statements. Pins remain AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, Lean `v4.35.0-rc3`.
