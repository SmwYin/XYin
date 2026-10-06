# Actual subgroup quotient geometry: verification receipt

Retained module: `AINTLIBDrafts/YZeroCoarseSubgroupQuotientGeometry.lean`.
The source is 135 lines, SHA256
`5f1810a5dbd2318367161746dc3c9252683dbe7cf1aa86a92881f946f543e334`.
The isolated build source has identical bytes. The approved temporary source had
110 lines and hash `4f3eef60f80abbe39b40c0808e25b2ecd1df0e43fc4d76087f999a66dc9d8d17`;
retention added only the normal license and module documentation.

## Proven scope

For an actual elliptic curve `E` over an arbitrary scheme `S`, an actual finite
locally free subgroup `G`, a nonzero integer level `N`, and an explicit equation
`G.ι ≫ E.mulByHom N = G.π ≫ E.zero`, the file proves:

- `Flat (G.gluedQuotientπ N hkill)`;
- `Surjective (G.gluedQuotientπ N hkill)`;
- `UniversallyClosed (G.gluedQuotientS N hkill)`.

Three public forwarding theorems use the actual `G.killN` and `G.killN_spec`, under
`[G.HasKillingInt]`. The generic theorems impose no domain, noetherian, affine-base,
or invertibility hypothesis. The literal constant-axis sanity uses precisely the
already checked invertible-level marked subgroup and its independent killing proof.
An additional level-3 example instantiates the subgroup of the native curve and
marking pulled back from an actual full complex scheme point.

The flat proof is local on the **source**, using `glueCover`, the actual local
Hopf–Galois flat projection, and the open immersion of the target quotient chart.
The surjective proof first lifts into a target quotient chart, then through its
surjective local projection, and checks the actual gluing triangle.
Universal closedness follows from `quotientπ ≫ quotientS = E.π`, properness of the
given original curve, and `UniversallyClosed.of_comp_surjective`.

## Final strict check

The single clean dependency leaf `ModularCurves.GroupScheme.SubgroupQuotient`
was built successfully in session 42143 (4121 jobs). Its log is
`/private/tmp/xyin-y0-subgroup-quotient-dependency.log`; upstream style and
deprecation warnings were observed there, with no build errors.

The retained module was then compiled with the exact Lean 4.35.0-rc3 binary,
correct module name, and merged setup closure. Both `autoImplicit` and
`relaxedAutoImplicit` were false. Session 51407 closed with exit code 0.

Final log: `/private/tmp/xyin-y0-subgroup-quotient-geometry-check.log`.
Full command, setup hash, source hash, exit, and artifact hashes:
`/private/tmp/xyin-y0-subgroup-quotient-geometry-receipt.json`.

All 11 printed declarations have exactly the standard three axioms
`propext`, `Classical.choice`, and `Quot.sound`. These include all seven new named
declarations and the actual upstream local flat/surjective theorem, source cover,
free-patch datum, and jointly-surjective target chart primitive. There are no
errors or warnings in the retained module's final log. Both actual subgroup
sanities pass. Correct-name `.olean`, `.olean.private`, `.olean.server`, `.ilean`,
`.ir.sig`, and `.ir` artifacts were inspected and recorded.

Three failed staging logs are preserved separately and are **not** final receipts:

- `/private/tmp/YZeroSubgroupQuotientGeometryProbe-first.log`;
- `/private/tmp/YZeroSubgroupQuotientGeometryProbe-second.log`;
- `/private/tmp/YZeroSubgroupQuotientGeometryProbe-third.log`.

They record opaque patch/free-module/chart-instance lookup failures. The repair
supplies the exact existing `free_gluePatch` and `ι_isOpenImmersion` terms and the
named local flat/surjective theorem; it adds no mathematical assumptions.

## Remaining obligations

This file proves universal closedness of the quotient structure map, **not**
properness. It does not establish finite or étale quotient projection, separated
quotient structure map, smooth relative dimension one, or local Weierstrass
presentations. In particular, it does not construct a quotient elliptic curve or
target-j invariant. It does not use the held `NIsogeny.quotient_*` geometry gates or
the held general smooth-precomposition descent theorem.

The subsequent retained module `YZeroCoarseSubgroupQuotientChartPullback.lean`
now supplies the actual target-chart pullback/preimage identification; its separate
receipt is `SubgroupQuotientChartPullbackVerification.md`. Source-local finite legs
alone do not prove global finiteness. The Hopf–Galois finite/étale algebra interface
and the remaining geometric upgrades are separate bounded tasks.
