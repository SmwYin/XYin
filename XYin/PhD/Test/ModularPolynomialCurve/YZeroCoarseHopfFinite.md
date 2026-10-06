# Finite module descent for an actual Hopf-Galois chart

The retained module is `AINTLIBDrafts/YZeroCoarseHopfFinite.lean`, in namespace
`ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft`.

For the same rings, algebras, coaction map, and `h : IsHopfGalois ρ` as the
retained left-factor equivalence, `coinvariants_finite` proves

```lean
[Module.Finite R0 A] : Module.Finite (coinvariants ρ) B
```

The argument uses mathlib's existing faithfully flat finite-module descent:

1. `Module.Finite.base_change` makes `B ⊗[R0] A` finite over its left `B` factor.
2. The inverse of `galoisEquivOverLeft h`, viewed as a `B`-linear equivalence,
   transfers this to `B ⊗[coinvariants ρ] B`.
3. The actual field `h.faithfullyFlat` supplies faithful flatness of `B` over
   `coinvariants ρ`; `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B`
   descends finite generation.

There is no domain, Noetherian, Hopf-algebra, or extra coaction hypothesis in
this generic theorem. The tensor scalar structures are the same actual left
`B`-algebra structures checked in `YZeroCoarseHopfGaloisLeft`.

`chartCoinvariants_finite` specializes to a literal existing
`P : G.AffineChartPatch`:

```lean
[Module.Free P.baseRing P.groupRing] :
  Module.Finite (coinvariants P.chartCoaction) P.chartRing
```

It applies the generic result to `P.isHopfGalois_chartCoaction`, using the
geometric algebra instances and `instModuleFiniteGroupRing` already provided
by `StableChartData`. The local freeness prerequisite is exactly the existing
upstream chart Hopf-Galois theorem's prerequisite. The finite group-ring
instance is proved from the actual finite subgroup structure morphism and its
finite section map over an affine base patch.

Two sanity examples check the generic finite algebra-map API and the actual
patch specialization. The conclusion is finite generation of these actual
section modules; finite morphisms of local or global quotient schemes and
étaleness require subsequent geometric arguments.

The temporary final fixture has 54 lines and SHA-256
`9eb6b81a6d8fc4d514e48d98c16f7dd51c9a1a087d4b932f97b269797efa5b0e`.
Its strict compile exited 0 with zero warnings/errors and eight checks using
only `propext`, `Classical.choice`, and `Quot.sound`.
Receipt: `/private/tmp/YZeroHopfFiniteProbe.log`.
The first kernel-green run's three `letI` style warnings are preserved at
`/private/tmp/YZeroHopfFiniteProbe.kernel-green-warnings.log`; the final proof
uses ordinary typed `let` instances as recommended by the compiler.

The retained file has 77 lines and SHA-256
`fae6683c1c80fbbefd618bcd998960f86c10d7667c04c1aba46a49d0e357eb77`.
It preserves the two accepted declarations, two examples, and eight axiom
checks. Correct-name strict artifact emission exited 0 with zero diagnostics;
all eight checks use only the three standard axioms.
Receipt: `/private/tmp/xyin-y0-hopf-finite.log`.

The isolated environment pins AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
The setup `/private/tmp/YZeroCoarseHopfFinite.setup.json` names
`AINTLIBDrafts.YZeroCoarseHopfFinite` with both implicit options false. From
`/private/tmp/xyin-y0-aintlib-work`, the exact invocation was:

```sh
LEAN_PATH=.lake/build/lib/lean:.lake/packages/mathlib/.lake/build/lib/lean:.lake/packages/batteries/.lake/build/lib/lean:.lake/packages/Qq/.lake/build/lib/lean:.lake/packages/aesop/.lake/build/lib/lean:.lake/packages/plausible/.lake/build/lib/lean:.lake/packages/importGraph/.lake/build/lib/lean:.lake/packages/LeanSearchClient/.lake/build/lib/lean:.lake/packages/proofwidgets/.lake/build/lib/lean:.lake/packages/Cli/.lake/build/lib/lean /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean -DautoImplicit=false -DrelaxedAutoImplicit=false --setup /private/tmp/YZeroCoarseHopfFinite.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseHopfFinite.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseHopfFinite.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseHopfFinite.c AINTLIBDrafts/YZeroCoarseHopfFinite.lean > /private/tmp/xyin-y0-hopf-finite.log 2>&1
```

Canonical `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, `.ir.sig`,
and `.c` artifacts were checked present. The retained and isolated copies were
byte-equal after compilation. Previously frozen sources and the local XYin
toolchain were unchanged.
