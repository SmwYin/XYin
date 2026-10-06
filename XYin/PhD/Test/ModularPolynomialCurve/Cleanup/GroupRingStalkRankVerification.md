# Actual group-chart stalk rank: verification receipt

Retained module: `AINTLIBDrafts/YZeroCoarseGroupRingStalkRank.lean`. Retained
and isolated sources are byte-identical: 109 lines, maximum width 93, SHA256
`dd0f35c3187f1981e7faafe8391df3b998a46ab1962ebb8f91d6bfce5bf12a8f`.
Retention adds only the standard license and short scope documentation.
The mathematical suffix, thirteen axiom prints, and two actual API examples
are byte-identical to approved temporary SHA256
`994fe4f015282ed92fa9e70e2592dd2b2815c59a0d59bc6d8449e4c4df248c5c`.

## Exact actual interface

For `E : EllipticCurve S`, `G : E.FiniteLocallyFreeSubgroup`, and an actual
`P : G.AffineChartPatch`, the new declaration is
`AffineChartPatch.groupRing_rankAtStalk P r hG p`, where `hG : G.HasRank r` and
`p : PrimeSpectrum P.baseRing`. Its conclusion is

```lean
Module.rankAtStalk (R := P.baseRing) P.groupRing p = r
```

There are no extra Free, Noetherian, domain, étale, smooth, or model inputs.
Finite flatness belongs to the existing subgroup projection; no ring-rank
hypothesis is introduced. The scalar map is the existing literal
`(G.π.appLE P.V P.groupOpen le_rfl).hom`, not a chosen substitute.

## Actual geometric comparison

The existing subgroup finite and flat instances give the genuine projection
`G.π`. Its affine group restriction is `P.groupToBase`, and its group ring is
finite over the base ring by the existing `instModuleFiniteGroupRing`.
The actual `G.π.flat_appLE` theorem supplies module flatness with exactly the
existing group-chart algebra.

Both `P.V.toSpecΓ` and `P.groupOpen.toSpecΓ` are existing isomorphisms. Their
actual `Scheme.Opens.toSpecΓ_SpecMap_appLE` square is therefore a pullback.
A prime `p` is explicitly regarded as `s : Spec Γ(S, P.V)` and lifted through
`(asIso P.V.toSpecΓ).inv` to the base-patch point `v`. The explicit iso identity
proves that `v` maps to `s`.

`finrank_of_isPullback` identifies the restricted group projection's rank at
`v` with the rank of `Spec` of its literal scalar map at `s`.
`finrank_SpecMap_algebraMap` identifies the latter with the module stalk rank
at `p`. A second actual restriction pullback identifies the first rank with
`G.π.finrank (P.V.ι.base v)`. The supplied genuine `hG` is evaluated at precisely
that included affine base point. This proves the claimed value `r` without
global freeness or a field hypothesis.

## Genuine sanities and strict verification

The first API example gives the formula at all primes of an arbitrary actual
patch from its supplied `HasRank r`. The second uses the actual marked-axis
subgroup and its proved `sectionAxisSubgroup_hasRank` theorem to obtain value
`N` for any actual affine patch. The invertible level and full marking are
exact existing inputs to that subgroup; no extra patch hypothesis is added.

The correct-name strict emission closed as session 70194 with exit code 0.
The pinned Lean 4.35.0-rc3 binary used setup name
`AINTLIBDrafts.YZeroCoarseGroupRingStalkRank`, 9455 normalized import entries,
and both `autoImplicit` and `relaxedAutoImplicit` false. All thirteen own and
selected primitive prints use exactly `propext`, `Classical.choice`, and
`Quot.sound`. Both examples pass with zero errors or warnings. The final log
is `/private/tmp/xyin-y0-group-ring-stalk-rank-check.log`, SHA256
`92e3659d2ab34d733c9d1ece855fb198fef3703f9babe784682adbffb2544a86`.

All six correct-name Lean outputs were inspected: `.olean`, `.olean.private`,
`.olean.server`, `.ilean`, `.ir.sig`, and `.ir`. Explicit generated C output
was also emitted and inspected at
`.lake/build/ir/AINTLIBDrafts/YZeroCoarseGroupRingStalkRank.c`.
Exact sizes and hashes of all seven outputs, source/setup/log provenance,
full primitive list, command and closed exit are saved in
`/private/tmp/xyin-y0-group-ring-stalk-rank-receipt.json`.

## Staging repair and mathematical boundary

The first temporary run, session 36210, failed only because a rewrite used
`p : PrimeSpectrum P.baseRing` where the unfolded inverse affine isomorphism
expected a literal `Spec Γ(S,P.V)` point. The sole repair introduced the
explicit canonical point `s` in the scheme formulas; no mathematical input
or comparison direction changed. The exact first source and failed log are
preserved separately and excluded from the trusted axiom receipt. The second
temporary run, session 4493, closed with exit code 0 and thirteen standard
three-axiom checks. Its receipt is
`/private/tmp/xyin-y0-group-ring-stalk-rank-probe-receipt.json`.

This module proves the actual group-chart rank adapter. Local quotient-module
rank, global quotient scheme fibre rank, native function-field degree, genus,
quotient-j, and the modular-polynomial relation remain separate statements.
No held NIsogeny quotientCurve or quotient-geometry result is used.
