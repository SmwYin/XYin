# Finite and étale actual local subgroup quotient projections

The retained module is `AINTLIBDrafts/YZeroCoarseLocalQuotientGeometry.lean`, in
namespace `ModularPolynomialCurveTest.AINTLIB.HopfGaloisLeft`. All four statements
concern an actual `P : G.AffineChartPatch`, with the existing prerequisite
`[Module.Free P.baseRing P.groupRing]` of the upstream chart Hopf-Galois theorem.

The finite declarations are:

```lean
quotientRing_subtype_finite : (G.quotientRing P.hstable).subtype.Finite
localQuotientOpenπ_isFinite : IsFinite (G.localQuotientOpenπ P.hstable)
```

Neither finite declaration assumes that `G.π` is étale. The actual invariant
ring is identified literally by upstream `P.quotientRing_eq_coinvariants` with
`(coinvariants P.chartCoaction).toSubring`. The same carrier and subtype map are
the canonical coinvariants algebra map, so the retained chart finite-module
theorem proves finite generation for the actual ring inclusion. The spectrum
map is finite by `IsFinite.SpecMap_iff`.

The literal local projection definition is

```lean
P.U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (G.quotientRing P.hstable).subtype)
```

Upstream `P.isIso_toSpecΓ_U` makes the first factor an isomorphism. The actual
composition of these two finite factors gives the local finite projection.

With the additional explicit geometric hypothesis `[Etale G.π]`, the module
also proves:

```lean
quotientRing_subtype_etale : (G.quotientRing P.hstable).subtype.Etale
localQuotientOpenπ_etale : Etale (G.localQuotientOpenπ P.hstable)
```

These use exactly the same invariant-ring equality, the retained
`chartCoinvariants_etale P`, `RingHom.etale_algebraMap`, and
`HasRingHomProperty.Spec_iff`. The affine chart isomorphism and spectrum map
are then two actual étale factors. No alternate scalar algebra is introduced
in either argument. There is no domain or Noetherian prerequisite.

The two sanity examples exercise the actual patch finite and étale APIs. These
are local projection results. A global quotient conclusion requires an actual
target-chart cover and the pullback identification of these local projections
with the global projection; that is a separate bridge.

The finite-only temporary proof initially encountered a composition-instance
matching failure. Its first staging output is preserved separately at
`/private/tmp/YZeroLocalQuotientFiniteProbe.first-failure.log` and excluded from
verification. Both factors checked individually, and the accepted proof uses
mathlib's explicit `MorphismProperty.IsStableUnderComposition.comp_mem` on the
actual arrows and their finite instances. The finite-only final fixture had 46
lines and SHA-256 `8fd867530229596c986156536b53c729dd9882796b9dfe9acb3dd8e6d82b47ed`;
all eight checks were standard-three-axiom checks with zero diagnostics.

The combined temporary fixture preserves the finite proof and adds only the
two explicitly conditional étale declarations, their patch sanity example, and
five axiom checks. It has 72 lines and SHA-256
`ac040bf15ac103eb7ecc473517c89d4a4f816b1782c3da1ce0f2845f3827fe71`.
Its first combined strict elaboration exited 0 with zero warnings/errors, both
examples, and thirteen checks using only `propext`, `Classical.choice`, and
`Quot.sound`. Receipt: `/private/tmp/YZeroLocalQuotientFiniteProbe.log`.

The retained file has 97 lines and SHA-256
`b35a853f68fb75b26361e689f236734f972ec2da52959a40e199a4269423b7e8`.
It preserves all accepted proof and example bodies. Correct-name strict artifact
emission exited 0 with the same thirteen standard-three-axiom checks, two examples,
and zero diagnostics. Receipt: `/private/tmp/xyin-y0-local-quotient-geometry.log`.

The isolated environment pins AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
The setup `/private/tmp/YZeroCoarseLocalQuotientGeometry.setup.json` names
`AINTLIBDrafts.YZeroCoarseLocalQuotientGeometry`, with both implicit options false.
From `/private/tmp/xyin-y0-aintlib-work`, the exact invocation was:

```sh
LEAN_PATH=.lake/build/lib/lean:.lake/packages/mathlib/.lake/build/lib/lean:.lake/packages/batteries/.lake/build/lib/lean:.lake/packages/Qq/.lake/build/lib/lean:.lake/packages/aesop/.lake/build/lib/lean:.lake/packages/plausible/.lake/build/lib/lean:.lake/packages/importGraph/.lake/build/lib/lean:.lake/packages/LeanSearchClient/.lake/build/lib/lean:.lake/packages/proofwidgets/.lake/build/lib/lean:.lake/packages/Cli/.lake/build/lib/lean /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean -DautoImplicit=false -DrelaxedAutoImplicit=false --setup /private/tmp/YZeroCoarseLocalQuotientGeometry.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseLocalQuotientGeometry.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseLocalQuotientGeometry.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseLocalQuotientGeometry.c AINTLIBDrafts/YZeroCoarseLocalQuotientGeometry.lean > /private/tmp/xyin-y0-local-quotient-geometry.log 2>&1
```

Canonical `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, `.ir.sig`,
and `.c` artifacts were checked present. The retained and isolated copies were
byte-equal after compilation. Previously frozen sources, the root's parallel
étale probes, and the local XYin toolchain were unchanged.
