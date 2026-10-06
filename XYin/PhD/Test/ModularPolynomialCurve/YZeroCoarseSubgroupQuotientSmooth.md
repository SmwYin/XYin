# Smooth actual subgroup quotient structure maps

The retained module is `AINTLIBDrafts/YZeroCoarseSubgroupQuotientSmooth.lean`.
It proves smoothness for the actual glued quotient scheme and its actual
structure map. Its global hypotheses are `[Etale G.π]` and
`[IsLocallyNoetherian S]`, for `G : E.FiniteLocallyFreeSubgroup` on an actual
elliptic curve over `S`.

The affine-chart declaration, in namespace
`ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch`, is:

```lean
quotientToBase_smooth (P : G.AffineChartPatch)
    [Module.Free P.baseRing P.groupRing] [Etale G.π]
    [IsNoetherianRing P.baseRing] : Smooth P.quotientToBase
```

The preceding retained algebra API proves that the literal raw quotient ring
is smooth for the scalar map `P.quotientBaseHom`. Here `Spec_iff` turns that
ring-hom property into smoothness of its exact `Spec.map`. Composing with
`P.hV.isoSpec.inv` gives the actual `P.quotientToBase`, whose definition uses
that same scalar map. No separate smoothness premise on the quotient ring
or quotient scheme is introduced.

The global declarations, in namespace
`ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup`, are:

```lean
gluedQuotientS_smooth (G : E.FiniteLocallyFreeSubgroup) (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero)
    [Etale G.π] [IsLocallyNoetherian S] : Smooth (G.gluedQuotientS N hkill)

quotientS_smooth (G : E.FiniteLocallyFreeSubgroup)
    [Etale G.π] [IsLocallyNoetherian S] [G.HasKillingInt] : Smooth G.quotientS
```

`gluedQuotientS_smooth` uses the actual source cover
`(G.quotientGlueData N hkill).openCover`. On each chart, the actual
`G.free_gluePatch` supplies group-ring freeness, and local Noetherianity of
`S` supplies the Noetherian section ring of its affine base open. The checked
`gluedQuotientι_gluedQuotientS` rewrites the restriction of the actual global
structure map as `quotientToBase` followed by the base-open immersion.
Both factors are smooth. The existing ring-hom-property source-locality
instance and `IsZariskiLocalAtSource.iff_of_openCover` assemble these exact
restrictions. The public quotient specializes this construction to the
actual chosen `G.killN` and `G.killN_spec`.

In namespace `ModularPolynomialCurveTest.AINTLIB.ConstantAxis`, the wrapper
`sectionAxis_quotientS_smooth` takes an arbitrary Noetherian `R`, a nonzero
invertible level `N`, an actual elliptic curve over `Spec R`, and a full
marking. It uses the literal `sectionAxisSubgroup`, its already checked direct
killing-integer instance, and its proved étale structure map. Thus the étale
input is supplied for this actual subgroup, while the generic theorem makes
it explicit. No field or integral-domain hypothesis is needed.

The two sanity examples check the public chosen-killing-integer API and the
literal quotient attached to an actual full complex point at level 3.
This module proves smoothness of the structure map. Relative dimension one,
genus one, an elliptic curve model on the quotient, and a descended target
j-invariant remain separate proof tasks. In particular, this leaf does not
invoke the upstream elliptic-curve quotient constructor with its known gaps.

The accepted temporary fixture had 98 lines, SHA-256
`3f2b3c5513d8a140328e14feecb327f6a41f57a0bbe19f87ff530d4914b36e8f`,
and strict session 37833 exited 0 on its first elaboration. Its complete log
contains exactly fifteen standard-three-axiom checks, two examples, and zero
warnings/errors. Root and a separate reviewer read the actual source and
complete output before retention. Log:
`/private/tmp/YZeroSubgroupQuotientSmoothProbe.log`; structured receipt:
`/private/tmp/YZeroSubgroupQuotientSmoothProbe-receipt.json`.

The retained source has 126 lines and SHA-256
`39b4d0ea79b88c3b1d839b434296273631e767ad572e52901660a2b5dfdb370f`.
Its declaration, proof, hypothesis and sanity bodies are byte-preserved from
that accepted fixture. The retained license and scope documentation are new;
the same fifteen axiom prints are moved into namespaces so that every line
is at most 91 characters. Correct-name strict emission, session 21344, exited 0 with exactly the same
fifteen standard-three-axiom checks, two examples, and zero diagnostics.
The complete named log is `/private/tmp/xyin-y0-subgroup-quotient-smooth.log`;
structured receipt is `/private/tmp/YZeroCoarseSubgroupQuotientSmooth-receipt.json`.
Both retained and isolated source copies are byte-equal after compilation;
all six canonical Lean artifacts and the C output are present.


The isolated environment pins AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
Setup `/private/tmp/YZeroCoarseSubgroupQuotientSmooth.setup.json` names
`AINTLIBDrafts.YZeroCoarseSubgroupQuotientSmooth`, sets both implicit options
false, and loads no plugins or dynamic libraries. From
`/private/tmp/xyin-y0-aintlib-work`, the exact command was:

```sh
LEAN_PATH=.lake/build/lib/lean:.lake/packages/mathlib/.lake/build/lib/lean:.lake/packages/batteries/.lake/build/lib/lean:.lake/packages/Qq/.lake/build/lib/lean:.lake/packages/aesop/.lake/build/lib/lean:.lake/packages/plausible/.lake/build/lib/lean:.lake/packages/importGraph/.lake/build/lib/lean:.lake/packages/LeanSearchClient/.lake/build/lib/lean:.lake/packages/proofwidgets/.lake/build/lib/lean:.lake/packages/Cli/.lake/build/lib/lean /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean -DautoImplicit=false -DrelaxedAutoImplicit=false --setup /private/tmp/YZeroCoarseSubgroupQuotientSmooth.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientSmooth.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientSmooth.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseSubgroupQuotientSmooth.c AINTLIBDrafts/YZeroCoarseSubgroupQuotientSmooth.lean > /private/tmp/xyin-y0-subgroup-quotient-smooth.log 2>&1
```

Artifact sizes and paths are recorded individually in the structured receipt.
This is the standalone named-module check; it does not claim that a later
cumulative retained-library gate has run. Previously frozen leaves, other
agents' files, the toolchain, and runtime settings were unchanged.
