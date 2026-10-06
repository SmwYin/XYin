# Actual source-chart differential rank one: verification receipt

Retained module: `AINTLIBDrafts/YZeroCoarseChartKaehlerRank.lean`.
The retained and isolated source bytes are identical: 79 lines, maximum width 84,
SHA256 `1be20a89f8e8d4964244e0a9b906613dee6fccb510dd15c5fdef6f36c52e6cfc`.
The mathematical suffix is byte-identical to the approved 53-line fixture,
SHA256 `543b6df61611237799b26ba1fc2602af634b36c13656efc886e6f3520de12949`.
Retention adds only the standard license and module documentation. The single
own theorem, all eight axiom prints, and all three examples are preserved.

## Actual mathematical and scalar inputs

`ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft.chartRing_kaehler_rankAtStalk`
takes only an actual `P : G.AffineChartPatch` and
`p : PrimeSpectrum P.chartRing`. Its conclusion is

```lean
Module.rankAtStalk (R := P.chartRing) Ω[P.chartRing⁄P.baseRing] p = 1
```

There are no additional group-ring freeness, group-projection étaleness,
Noetherian, domain, nontriviality, or global-standard-chart hypotheses.
The base scheme and given elliptic curve remain arbitrary within their actual
upstream types.

The patch's actual affine opens and containment are `P.V`, `P.hV`, `P.U`,
`P.hU`, and `P.hover` (`GroupScheme/StableCharts.lean:89–101`). Its rings are the
literal section rings `Γ(S, P.V)` and `Γ(E.E, P.U)` (lines 108 and 111). The
existing algebra instance is exactly
`(E.π.appLE P.V P.U P.hover).hom.toAlgebra` (lines 120–121). The scalar-map
example checks the resulting algebra-map identity by `rfl`.

The given elliptic curve's geometric record supplies
`E.smooth : SmoothOfRelativeDimension 1 E.π`
(`EllipticCurve/Basic.lean:491`, registered as an instance at line 498).
The actual `HasRingHomProperty` instance for this scheme property corresponds
to `RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)`
(`AlgebraicGeometry/Morphisms/Smooth.lean:141`).

`HasRingHomProperty.appLE` with the actual affine-open witnesses and `P.hover`
therefore gives the local dimension-one condition for the literal geometric
scalar map. A definitional `change` exposes that map. The already verified
`chartRing_smooth P` supplies smoothness of the actual chart algebra, and the
retained local-condition-to-rank adapter gives rank one. This uses local
standard charts, without upgrading the whole chart algebra to globally
standard smooth.

## Actual API sanities

Three examples pass: the literal scalar-map identity, the rank formula for every
prime of an arbitrary actual patch, and specialization to
`G.gluePatch N hkill i`. The arbitrary-patch interface assumes no freeness.
The latter is the actual canonical free gluing patch, with its existing
nonzero killing-integer data; `G.free_gluePatch` is also independently printed
as a clean primitive. No existence of a nonfree patch is asserted or needed.

## Final named strict verification

The final exact-source artifact emission closed as session 41733 with exit code
0. It used the pinned Lean 4.35.0-rc3 binary, correct setup name
`AINTLIBDrafts.YZeroCoarseChartKaehlerRank`, and both `autoImplicit` and
`relaxedAutoImplicit` false. The setup has 9432 import entries and SHA256
`f1637cd4eb127f4ae3f86af61603404c87ed14c8bcc48fc12aa21a932a93a78f`.

The final log `/private/tmp/xyin-y0-chart-kaehler-rank-check.log`, SHA256
`26c58e5b36e0af0411acb8971ed1f5d315a16cb18781030c82f797b78137241d`,
contains exactly eight axiom prints, each using only `propext`, `Classical.choice`,
and `Quot.sound`. There are no errors or warnings. All three examples pass.

The correct-name `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir.sig`,
and `.ir` artifacts were inspected under the isolated
`.lake/build/lib/lean/AINTLIBDrafts/` directory. Their sizes are respectively
9912, 14888, 2576, 12247, 176, and 1864 bytes. Full source/setup/log/artifact
hashes, primitive lists, the exact command, and the closed exit are saved in
`/private/tmp/xyin-y0-chart-kaehler-rank-receipt.json`.

The first temporary invocation stopped before elaboration because its setup
merge omitted the already built gluing dependency used by the concrete patch
example. Its separate log has no proof or axiom output and is excluded from the
green receipt. The corrected setup merges the existing cumulative-build
closures; no extra dependency build was needed. The actual mathematical source
required no repair. A preceding named run closed green as session 95727; one
module-documentation line break was then corrected and all artifacts emitted
again for the exact final source. Both temporary and retained proof suffixes
remain identical.

## Remaining scope

This is the source-chart rank-one input. Coinvariant ranks, relative-dimension
descent for the quotient scheme, and the quotient elliptic curve upgrade are
separate proof steps. No held `NIsogeny` quotient-geometry or general scheme
smooth-descent theorem is used by this module.
