# Actual chart coinvariant differential rank one: verification receipt

Retained module: `AINTLIBDrafts/YZeroCoarseChartCoinvariantsKaehlerRank.lean`.
The retained and isolated source bytes are identical: 91 lines, maximum width
99, SHA256 `649103470193dd4192905e72dab40543d3ae656f587bcf3ef5bceb1308740bba`.
Retention adds only the standard license and module documentation. The complete
mathematical suffix, both actual API examples, and all ten axiom prints are
byte-identical to the approved 63-line fixture, SHA256
`399c555e1a303611b39ab5e1e592b498c9740fbbcca5ebcd60569206d66284ae`.

## Exact actual statement

For a given elliptic curve `E` over an arbitrary scheme `S`, its actual finite
locally free subgroup `G`, and an actual affine chart patch `P`, let

- `R = P.baseRing`, with the existing geometric section-ring scalars;
- `B = P.chartRing`;
- `C = coinvariants P.chartCoaction`, the literal chart-coaction subalgebra of `B`.

`ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft.chartCoinvariants_kaehler_rankAtStalk`
requires exactly `[Module.Free P.baseRing P.groupRing]`, `[Etale G.π]`, and
`[IsNoetherianRing P.baseRing]`. For every prime `p` of `C`, its conclusion is

```lean
Module.rankAtStalk (R := coinvariants P.chartCoaction)
  Ω[coinvariants P.chartCoaction⁄P.baseRing] p = 1
```

It does not assume a differential-rank formula, smoothness of `C`, globally
standard smoothness of `B`, a domain, or nontriviality. The actual existing
smoothness API is used to prove the necessary smoothness of `C`. The
Noetherian hypothesis concerns only the actual affine base-patch ring; no
global Noetherianity of `S` is assumed.

## Actual scalar and descent inputs

The scalar tower `R → C ⊆ B` is the canonical subalgebra tower. No ring
homomorphism or algebra instance is reassigned. `Subalgebra.isScalarTower_mid`
supplies the compatibility between `R`-scalars and the inclusion `C → B`.

`chartCoinvariants_smooth P` supplies `Algebra.Smooth R C` under the exact three
stated patch hypotheses. Its existing instances supply finite and flat
`C`-module differentials `Ω[C⁄R]`. The Noetherian base-ring input is used by this
already verified smoothness theorem; the generic rank descent itself does not
require Noetherian rings.

`chartCoinvariants_etale P` supplies `Algebra.Etale C B` from the actual free
group patch and étale subgroup projection. Its formally étale field is then
available through the existing instance. The faithful-flat input is the literal
`P.isHopfGalois_chartCoaction.faithfullyFlat` field of the actual Hopf--Galois
datum, with the same canonical coinvariant inclusion.

The retained generic
`kaehler_rankAtStalk_eq_of_formallyEtale_faithfullyFlat` lifts every prime of
`C` to a prime of `B` and compares the corresponding differential ranks by
formally étale base change. The unconditional actual source-chart theorem
`chartRing_kaehler_rankAtStalk P` supplies rank one at every prime of `B`.
These are the exact inputs to the new actual coinvariant conclusion.

## Genuine API examples

The first example gives the formula simultaneously at all primes of an
arbitrary actual free patch under the exact étale and base-ring Noetherian
hypotheses. The second specializes to `G.gluePatch N hkill i`. It obtains
freeness from the actual `G.free_gluePatch N hkill i` API, instead of introducing
a freeness assumption for that selected patch. Its étale subgroup and
Noetherian base-patch hypotheses remain explicit.

## Strict named verification

The correct-name artifact emission closed as session 22547 with exit code 0.
It used the exact pinned Lean 4.35.0-rc3 binary, setup name
`AINTLIBDrafts.YZeroCoarseChartCoinvariantsKaehlerRank`, and both `autoImplicit`
and `relaxedAutoImplicit` false. The setup has 9458 import entries and SHA256
`0cf16cb823a7bfd173805d603930e6c4bd334eec26eb2f5b7d1199839829b0c6`.

The final log `/private/tmp/xyin-y0-chart-coinvariants-kaehler-rank-check.log`,
SHA256 `10fc05cba122c6b1259ccd52b05d6a068e4141ae5c93067d35eeddf630310d31`,
has exactly ten permitted axiom prints and no errors or warnings. Nine prints,
including the own theorem and all selected geometric/Hopf/rank-descent inputs,
use only `propext`, `Classical.choice`, and `Quot.sound`.
`Subalgebra.isScalarTower_mid` uses only `propext` and `Quot.sound`.
Both actual API examples pass. The temporary source also passed on its first
strict run, session 20921, without proof repair.

The correct-name `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir.sig`,
and `.ir` artifacts were inspected under the isolated
`.lake/build/lib/lean/AINTLIBDrafts/` directory. Their sizes are respectively
20264, 19800, 2672, 13664, 176, and 1576 bytes. The exact command, closed exit,
complete source/setup/log/artifact hashes, and full primitive list are saved in
`/private/tmp/xyin-y0-chart-coinvariants-kaehler-rank-receipt.json`.

## Remaining scope

This proves rank one for the canonical local chart coinvariant algebra. It is
not a statement about the coarse modular curve's global invariant ring. The
raw equalizer-ring transfer, full local-standard-smooth criterion, quotient
scheme relative-dimension descent, and quotient elliptic curve upgrade are
separate steps. No held quotient-geometry or general scheme smooth-descent
theorem is used by this module.
