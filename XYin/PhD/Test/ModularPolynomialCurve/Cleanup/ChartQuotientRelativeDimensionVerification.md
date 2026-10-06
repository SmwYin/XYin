# Actual chart quotient relative dimension one: verification receipt

Retained module: `AINTLIBDrafts/YZeroCoarseChartQuotientRelativeDimension.lean`.
The retained and isolated sources are byte-identical: 114 lines, maximum width
98, SHA256 `352e33e2278d7e7593602fc024edf713134c62f4830e15d47fe9578b036bdc7e`.
Only the standard license and module documentation were added to the approved
84-line temporary proof. The complete mathematical suffix, all eleven axiom
prints, and both actual API examples remain byte-identical to temporary SHA256
`538155de8aed64e13891043afcb098d98be745a296d265e52aea0d3772b22d10`.

## Exact statements and hypotheses

Given an elliptic curve `E` over an arbitrary scheme `S`, its actual finite
locally free subgroup `G`, and an actual affine chart patch `P`, write

- `R = P.baseRing`, with its existing geometric section-ring scalars;
- `B = P.chartRing`;
- `C = coinvariants P.chartCoaction`, the canonical chart-coaction subalgebra;
- `Q = G.quotientRing P.hstable`, the actual raw equalizer subring.

Both new statements require exactly `[Module.Free P.baseRing P.groupRing]`,
`[Etale G.π]`, and `[IsNoetherianRing P.baseRing]`. No global Noetherianity of
`S`, ring-domain assumption, extra smoothness hypothesis, differential-rank
assumption, or globally standard smooth chart is introduced.

The first API is
`ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft.chartCoinvariants_locally_standardSmoothRelDim_one`:

```lean
RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
  (algebraMap P.baseRing (coinvariants P.chartCoaction))
```

The second API is
`ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch.quotientBaseHom_locally_standardSmoothRelDim_one`:

```lean
RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) P.quotientBaseHom
```

The first combines actual `chartCoinvariants_smooth P` and the retained
`chartCoinvariants_kaehler_rankAtStalk P` with the smooth differential-rank
criterion. Thus the local standard relative dimension is proved from the actual
geometric and Hopf--Galois inputs, rather than added as a comparison hypothesis.

## Literal raw scalar transport

The raw ring `Q` receives only a local algebra instance, explicitly defined by
`P.quotientBaseHom.toAlgebra`. The existing actual
`P.quotientCoinvariantsAlgEquiv` is then an `R`-algebra equivalence `Q ≃ₐ[R] C`.
No exported raw-ring algebra instance is installed or reassigned.

The verified transport direction is codomain postcomposition:
`RingHom.locally_respectsIso(...).1` sends the property of `R → C` to that of
`R → C → Q`, using the inverse ring equivalence. Its exact scalar identity is

```lean
e.symm.toRingEquiv.toRingHom.comp (algebraMap R C) = P.quotientBaseHom
```

The proof uses `e.symm.commutes` with the literal local raw algebra. Explicit
`RingHom.ext` stops at raw-ring equality; this avoids tactic-driven recursion
into the quotient subtype. The resulting composite is the actual existing
scalar map, not a newly chosen map. No raw differential-module comparison or
raw rank hypothesis is needed for this transfer.

## Meaningful API examples

The first example uses an arbitrary actual free patch under the stated étale
and Noetherian patch hypotheses. The second uses the canonical
`G.gluePatch N hkill i`, for actual nonzero `N` and the actual subgroup killing
identity. Freeness is obtained from `G.free_gluePatch N hkill i`; its étale
subgroup and Noetherian base-patch ring hypotheses remain explicit. It checks
the property of the actual chosen patch's literal `quotientBaseHom`.

## Strict named verification

Correct-name artifact emission closed as session 42192 with exit code 0. It
used the exact pinned Lean 4.35.0-rc3 binary, setup name
`AINTLIBDrafts.YZeroCoarseChartQuotientRelativeDimension`, and both
`autoImplicit` and `relaxedAutoImplicit` false. The normalized setup has 9461
import entries, SHA256
`22f7e2d79d38fecd0e1bfd12493ae94afc708fa40df094b2f91538ab228408a6`.

The final log `/private/tmp/xyin-y0-chart-quotient-relative-dimension-check.log`,
SHA256 `946530a236f840787355bdd68cea81d15cb2664985d871b3138048668936c325`,
contains exactly eleven permitted axiom prints and no errors or warnings. Ten
prints, including both own theorems, use exactly `propext`, `Classical.choice`,
and `Quot.sound`. The selected `AlgEquiv.commutes` primitive uses only
`Quot.sound`. Both actual API examples pass. The named log is byte-identical
to the approved third temporary log.

The correct-name `.olean`, `.olean.private`, `.olean.server`, `.ilean`,
`.ir.sig`, and `.ir` artifacts were inspected under the isolated
`.lake/build/lib/lean/AINTLIBDrafts/` directory. Their sizes are respectively
27712, 54392, 3032, 20915, 176, and 1584 bytes. Full source/setup/log/artifact
hashes, exact command, closed exit, and primitive list are recorded in
`/private/tmp/xyin-y0-chart-quotient-relative-dimension-receipt.json`.

## Staging failures and scope

The first temporary run, session 25281, failed because a qualified identifier
was split after a trailing dot. The second, session 82653, failed because the
`ext` tactic recursed through the quotient subtype before the planned `change`.
Both exact failed sources and logs are preserved separately and excluded from
the trusted axiom receipt. The repaired third temporary run, session 21395,
closed with exit code 0; no mathematical hypothesis or proof direction changed.
The temporary provenance is recorded in
`/private/tmp/xyin-y0-chart-quotient-relative-dimension-probe-receipt.json`.

These two conclusions concern actual local chart quotient algebras. They do
not concern the coarse modular curve's global coefficient ring, or supply a
scheme-level gluing result by themselves. Scheme relative-dimension descent,
the quotient elliptic curve upgrade, quotient-j, and the modular-polynomial
relation remain separate proof steps. No held quotient-geometry or general
scheme smooth-descent theorem is used by this module.
