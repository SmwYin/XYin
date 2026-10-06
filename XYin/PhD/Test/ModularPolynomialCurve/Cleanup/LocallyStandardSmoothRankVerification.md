# Locally standard smooth differential ranks: verification receipt

Retained module: `AINTLIBDrafts/YZeroCoarseLocallyStandardSmoothRank.lean`.
The retained and isolated source bytes are identical: 106 lines, maximum width
92, SHA256 `4caaf8a0e9f811f49c95d62f3954e4bfad81c98ec25de6e6db4e2bceac794c1f`.
Retention only adds the standard license and module documentation to the
approved final 78-line fixture. The mathematical suffix, ten axiom prints, and
two examples are byte-preserved.

## Exact proved statement

`ModularPolynomialCurveTest.AINTLIB.RelativeDimension.kaehler_rankAtStalk_eq_of_locally_standardSmooth`
works over arbitrary commutative rings `R` and `S` with their given algebra
structure. It retains `[Algebra.Smooth R S]` and accepts

```lean
RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R S)
```

for an arbitrary natural number `n`. At each `P : PrimeSpectrum S`, the
conclusion is `Module.rankAtStalk (R := S) Ω[S⁄R] P = n`.

The source hypothesis is the literal local ring-hom condition. A global
standard smooth presentation of `S` is not assumed. Smoothness remains explicit
in this bounded first version to supply the finite and flat differential module
used by the previously verified localization rank comparison. No Noetherian,
domain, field, nontriviality, finite-extension, or global dimension-one
restriction is added.

## Actual proof and source provenance

`RingHom.Locally` (`RingTheory/RingHom/Locally.lean:60`) provides a set generating
the unit ideal and a standard-relative-dimension condition after localization
at each element. For a given prime, some cover element `t` lies outside it:
otherwise the span lies in the proper prime ideal. The proof uses the actual
prime witness `P.2.ne_top`, following the existing prime-spectrum API.

`PrimeSpectrum.localization_away_comap_range`
(`RingTheory/Spectrum/Prime/Topology.lean:587`) gives a prime `Q` of
`Localization.Away t` above `P`. The canonical scalar tower is identified with
the local ring-hom composition by `IsScalarTower.algebraMap_eq` in its checked
forward direction. The ring-hom/algebra-map equivalence installs the actual
standard-relative-dimension structure on this localization.

`Algebra.FormallyEtale.of_isLocalization` supplies formal étaleness of the
localization. The retained `kaehler_rankAtStalk_eq_of_smooth_formallyEtale`
compares the rank at `Q` with the rank at `P`; its comap is explicitly typed
before rewriting by the above-prime equality. The retained
`kaehler_rankAtStalk_eq_of_standardSmooth` gives rank `n` at `Q`. This helper
derives nontriviality from `Q`, so no extra nontriviality assumption enters the
local adapter.

The identity-dimension-zero and one-variable-polynomial-dimension-one examples
construct genuine local conditions using `RingHom.locally_of` and the exact
relative-dimension isomorphism-respect theorem. They exercise the local adapter,
rather than assume the desired local condition as an example premise.

## Strict named verification

The correct-name artifact emission closed as session 92656 with exit code 0.
It used the exact pinned Lean 4.35.0-rc3 binary, setup name
`AINTLIBDrafts.YZeroCoarseLocallyStandardSmoothRank`, `autoImplicit=false`, and
`relaxedAutoImplicit=false`. The setup has 9427 import entries, SHA256
`8048941c605e73b1b3c01328380775ecf706e9f5b21d11c2b93a038cf2dcddb8`.

The final log `/private/tmp/xyin-y0-locally-standard-smooth-rank-check.log`, SHA256
`7cd99e5b80a24f9c5bd1dc93a29ee16097d8afa810a88d17d51fff183a58bbcd`,
contains ten permitted axiom prints and no errors or warnings. Eight declarations,
including the own theorem and both rank helpers, use exactly `propext`,
`Classical.choice`, and `Quot.sound`. The two primitive prints
`IsScalarTower.algebraMap_eq` and `Ideal.span_le` use only `propext` and
`Quot.sound`. Both examples pass.

The correct-name `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir.sig`,
and `.ir` artifacts were inspected under the isolated
`.lake/build/lib/lean/AINTLIBDrafts/` directory. Their sizes are respectively
11608, 72368, 2616, 12994, 176, and 2272 bytes. Full source/setup/log/artifact
hashes, primitive lists, the exact command, and the closed exit are recorded in
`/private/tmp/xyin-y0-locally-standard-smooth-rank-receipt.json`.

## Excluded staged checks and remaining scope

The first temporary run lacked the explicit public import of
`Mathlib.RingTheory.RingHom.Locally`. The second run used the invalid dotted
projection `P.asIdeal.ne_top` instead of the actual prime proof's `P.2.ne_top`.
These two failed logs remain separate and are excluded from the green receipt;
their elaborator-recovery `sorryAx` outputs are not verification evidence. The
approved third temporary run and final named run contain no `sorryAx` and no
diagnostics. The final temporary source remains frozen at SHA256
`661fc1401efeb6bc7417cf8fd05eaaebb2113827b5d98981b2a2b2f029aced39`.

This proves the local-standard-condition-to-stalk-rank direction. The converse
smooth-plus-rank criterion, descent of relative dimension, scheme gluing, and
quotient elliptic curve upgrade are separate tasks. No held quotient-curve or
general scheme smooth-descent theorem is used.
