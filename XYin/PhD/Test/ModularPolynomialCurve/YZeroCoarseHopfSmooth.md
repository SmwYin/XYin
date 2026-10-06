# Smoothness of actual chart and raw quotient algebras

The retained module is `AINTLIBDrafts/YZeroCoarseHopfSmooth.lean`. In namespace
`ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft`, it proves:

```lean
chartRing_smooth P : Algebra.Smooth P.baseRing P.chartRing

chartCoinvariants_smooth P
    [Module.Free P.baseRing P.groupRing]
    [Etale G.π] [IsNoetherianRing P.baseRing] :
    Algebra.Smooth P.baseRing (coinvariants P.chartCoaction)
```

The first declaration has none of the additional hypotheses of the second.
`P.baseRing = Γ(S, P.V)` and `P.chartRing = Γ(E.E, P.U)` are the actual
section rings. `StableCharts.lean:129` defines their algebra structure by
`(E.π.appLE P.V P.U P.hover).hom.toAlgebra`. The curve's actual
relative-dimension-one smoothness gives `Smooth E.π`; its `smooth_appLE`
applied to `P.hV`, `P.hU`, and `P.hover`, followed by
`RingHom.smooth_algebraMap`, proves this literal chart algebra smooth.
There is no assumed chart-ring smoothness.

For the second declaration, the checked actual chart finite-module and
étale theorems concern the same canonical coinvariant subalgebra and
ambient chart ring. The actual Hopf-Galois field supplies faithful flatness.
`Subalgebra.isScalarTower_mid` aligns the base-ring/coinvariant/chart scalar
tower without a new scalar algebra. `Algebra.smooth_of_etale_faithfullyFlat`
gives smoothness over the Noetherian base-patch ring. The theorem requires
no domain or field assumption. If the base scheme is locally Noetherian,
the affine section-ring API supplies the Noetherian condition on this patch;
that convenience wrapper is not added here.

In namespace
`ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup.AffineChartPatch`, the
module also proves the actual raw quotient-ring interfaces:

```lean
quotientRing_smooth P
    [Module.Free P.baseRing P.groupRing]
    [Etale G.π] [IsNoetherianRing P.baseRing] :
    let _ : Algebra P.baseRing (G.quotientRing P.hstable) :=
      (quotientBaseHom P).toAlgebra
    Algebra.Smooth P.baseRing (G.quotientRing P.hstable)

quotientBaseHom_smooth P
    [Module.Free P.baseRing P.groupRing]
    [Etale G.π] [IsNoetherianRing P.baseRing] :
    (quotientBaseHom P).Smooth
```

The imported `YZeroCoarseLocalQuotientFiniteType` fixes the raw algebra's
scalar map explicitly. Its `quotientBaseHom_comp_subtype` proves that this
map, followed by the actual raw subring inclusion, is exactly the geometric
`(E.π.appLE P.V P.U P.hover).hom`. Its
`quotientCoinvariantsAlgEquiv P` is a base-ring algebra equivalence from the
raw ring with this fixed algebra structure to the canonical coinvariants.
The new proof installs actual canonical coinvariant smoothness and applies
`Algebra.Smooth.of_equiv` to this equivalence's inverse, in the direction
coinvariants to raw ring. `RingHom.smooth_algebraMap` then gives smoothness
of this literal quotient scalar ring homomorphism. No different raw algebra
instance or assumed source-algebra smoothness is introduced.

The smooth descent theorem at `ForMathlib/EtaleSmoothDescent.lean:78` uses
Artin–Tate to obtain finite presentation over the Noetherian base. Its
projective-differential argument uses formally étale differential base change
and flat tensor descent. Its H¹ argument is the actual
`EtaleH1Descent.subsingleton_h1Cotangent_of_etale_faithfullyFlat`, which uses
`StandardEtaleH1.tensorH1CotangentOfIsStandardEtale`. All these actual
primitive declarations were independently axiom-checked. The two sorried
scheme smooth/LFP descent declarations of `ForMathlib/SmoothDescent.lean`
are not used in this proof.

Four direct sanity examples exercise canonical chart and coinvariant
`algebraMap` smoothness, the explicitly fixed raw quotient algebra, and the
literal raw quotient scalar ring-hom property. These are algebra smoothness
results. A theorem about the actual quotient scheme structure map requires
the separate geometric projection/structure factorization triangle.

The exact three missing upstream modules were built with no source changes:
`ModularCurves.ForMathlib.StandardEtaleH1`,
`ModularCurves.ForMathlib.EtaleH1Descent`, and
`ModularCurves.ForMathlib.EtaleSmoothDescent`.
The dependency build, session 20632, exited 0 with 3050 jobs.
Its existing pinned-source warnings were recorded separately: 11 in
`StandardEtaleH1` (seven `haveI` style, two unused section-variable, one
`TensorProduct.induction_on` deprecation, and one unused simp argument),
five `haveI` style warnings in `EtaleH1Descent`, and 29 `haveI` style warnings
in `EtaleSmoothDescent`. There were no errors, and no lint settings were
changed. Receipt: `/private/tmp/YZeroChartSmoothProbe-dependency-receipt.json`.
Log: `/private/tmp/xyin-y0-etale-smooth-dependencies.log`.

The canonical temporary fixture had 63 lines and SHA-256
`ea92db3e350695d72facfe2a891d9130959588ec817557288a8b31c82b57afc7`.
Its first strict elaboration, session 59618, exited 0 with 15 allowed standard
axiom checks, two examples, and zero own diagnostics. The Artin–Tate check's
namespace was corrected to its actual root declaration before compilation.
Log: `/private/tmp/YZeroChartSmoothProbe.log`.

The first retained 87-line version had SHA-256
`8c0fb1f43cc7841b80018b8e146061a213fbf6288f4a19ce1aa3263cd9491e2b`.
Its correct-name session 46480 exited 0 with 15 allowed checks and two
examples. This historical version and receipt are saved separately at
`/private/tmp/YZeroCoarseHopfSmooth-before-raw.lean`,
`/private/tmp/YZeroCoarseHopfSmooth-before-raw-receipt.json`, and
`/private/tmp/xyin-y0-hopf-smooth-before-raw.log`, with its previous setup and
companion also archived under the `before-raw` name.

The raw temporary fixture had 49 lines and SHA-256
`3eae7c73b9319a51af66062b2f3bebebded5e8225542b34b98654384c3fa63ec`.
Its first strict elaboration, session 12252, exited 0 with nine standard-three-
axiom checks, two examples, and zero warnings/errors. Actual source and output
were reviewed independently before this augmentation.
Log: `/private/tmp/YZeroRawQuotientSmoothProbe.log`.

The final retained file has 132 lines and SHA-256
`89803a6654740134a57bab10ed17990141e35c88b7d40ffdec6f4b5fdf405bfd`.
The original mathematical namespace tail remains byte-for-byte unchanged,
and the complete accepted raw temporary namespace/body/checks/examples is
appended byte-for-byte. Only its required frozen import/open and scope
explanation were added outside those bodies. Correct-name strict re-emission,
session 67229, exited 0 with four own declarations, four examples, and 24
allowed standard axiom checks: 23 use exactly `propext`, `Classical.choice`,
and `Quot.sound`; `Subalgebra.isScalarTower_mid` uses only `propext` and
`Quot.sound`. Every own declaration and every actual smooth/H¹ descent
primitive uses only the standard three axioms. There are zero own
warnings/errors and no `sorryAx`.
Log: `/private/tmp/xyin-y0-hopf-smooth.log`.
Structured receipt: `/private/tmp/YZeroCoarseHopfSmooth-receipt.json`.

The isolated environment pins AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
The setup `/private/tmp/YZeroCoarseHopfSmooth.setup.json` names
`AINTLIBDrafts.YZeroCoarseHopfSmooth`, with both implicit options false,
and no plugins or dynamic libraries. From
`/private/tmp/xyin-y0-aintlib-work`, the exact dependency build was:

```sh
ELAN_HOME=/private/tmp/xyin-y0-elan /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lake build ModularCurves.ForMathlib.StandardEtaleH1 ModularCurves.ForMathlib.EtaleH1Descent ModularCurves.ForMathlib.EtaleSmoothDescent > /private/tmp/xyin-y0-etale-smooth-dependencies.log 2>&1
```

The exact correct-name artifact invocation was:

```sh
LEAN_PATH=.lake/build/lib/lean:.lake/packages/mathlib/.lake/build/lib/lean:.lake/packages/batteries/.lake/build/lib/lean:.lake/packages/Qq/.lake/build/lib/lean:.lake/packages/aesop/.lake/build/lib/lean:.lake/packages/plausible/.lake/build/lib/lean:.lake/packages/importGraph/.lake/build/lib/lean:.lake/packages/LeanSearchClient/.lake/build/lib/lean:.lake/packages/proofwidgets/.lake/build/lib/lean:.lake/packages/Cli/.lake/build/lib/lean /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean -DautoImplicit=false -DrelaxedAutoImplicit=false --setup /private/tmp/YZeroCoarseHopfSmooth.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseHopfSmooth.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseHopfSmooth.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseHopfSmooth.c AINTLIBDrafts/YZeroCoarseHopfSmooth.lean > /private/tmp/xyin-y0-hopf-smooth.log 2>&1
```

Canonical `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`,
`.ir.sig`, and `.c` artifacts were checked present. The retained and isolated
copies were byte-equal after compilation. Other previously frozen sources,
other agents' files, the local toolchain, and runtime settings were unchanged.
