# Étale actual subgroup quotient projections

The retained module is `AINTLIBDrafts/YZeroCoarseSubgroupQuotientEtale.lean`.
It uses the actual `E.FiniteLocallyFreeSubgroup`, actual gluing target charts,
and actual public `quotientπ`. Its global statements do not refer to the
unproved upstream elliptic-curve quotient constructor.

For `G : E.FiniteLocallyFreeSubgroup`, `[Etale G.π]`, and a literal killing datum
`hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero`, the generic declarations are:

```lean
gluedQuotientπ_etale : Etale (G.gluedQuotientπ N hkill)
quotientπ_etale [G.HasKillingInt] : Etale G.quotientπ
```

Both are in namespace `ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup`.
The first theorem uses the actual target chart cover
`(G.quotientGlueData N hkill).openCover`. On each chart, `G.free_gluePatch`
supplies exactly the module freeness prerequisite of the retained local
étale projection theorem. The independently checked pullback square is
flipped so that `isoPullback_inv_snd` rewrites the target-local projection
as an isomorphism inverse followed by the actual local projection. These
factors are étale, and `IsZariskiLocalAtTarget.iff_of_openCover` gives the
actual global result. The public quotient is the same construction at its
actual chosen `G.killN` and `G.killN_spec`; no alternate quotient is used.

In namespace `ModularPolynomialCurveTest.AINTLIB.ConstantAxis`, the wrapper is:

```lean
sectionAxis_quotientπ_etale
    (R : CommRingCat) (N : ℕ) [NeZero N]
    (E : EllipticCurve (Spec R)) (hinv : NIsInvertible (Spec R) N)
    (L : E.FullLevelPt N) :
    let G := sectionAxisSubgroup R N E hinv L
    let _ : G.HasKillingInt := sectionAxisSubgroup_hasKillingInt R N E hinv L
    Etale G.quotientπ
```

It installs the existing direct killing-integer instance and the proved
`sectionAxisSubgroup_etale` for this literal subgroup. Invertibility is used
by the subgroup constructor. The wrapper requires neither a field nor a
domain or Noetherian hypothesis. The two sanity examples exercise the
chosen-killing-integer API and the literal subgroup of an actual full complex
point at level 3. No elliptic curve structure or target j-invariant has been
constructed by this file.

The temporary fixture had 77 lines and SHA-256
`bb2b2911b06af5538e2fb1ccef37bebbe7290763d1b0acd71740cab27fa674ba`.
Its first strict elaboration, session 4847, exited 0 with twelve checks using
only `propext`, `Classical.choice`, and `Quot.sound`, two examples, and zero
diagnostics. Actual source and output were reviewed independently before
retention. Temporary receipt: `/private/tmp/YZeroSubgroupQuotientEtaleProbe.log`.

The retained file has 99 lines and SHA-256
`cfe54fd24eeb2f53bb10881ef373b2e6f2d2dc4b867cc5dd7e26e3c87b4f82e2`.
Removing only its license/header and scope documentation restores the entire
accepted temporary source byte-for-byte, including proof and sanity bodies.
Correct-name strict emission, session 62881, exited 0 with the same twelve
standard-three-axiom checks, two examples, and zero warnings/errors.
Log: `/private/tmp/xyin-y0-subgroup-quotient-etale.log`.
Structured receipt: `/private/tmp/YZeroCoarseSubgroupQuotientEtale-receipt.json`.

The isolated environment pins AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
Setup `/private/tmp/YZeroCoarseSubgroupQuotientEtale.setup.json` names
`AINTLIBDrafts.YZeroCoarseSubgroupQuotientEtale`, has both implicit options
false, and loads no plugins or dynamic libraries. From
`/private/tmp/xyin-y0-aintlib-work`, the exact command was:

```sh
LEAN_PATH=.lake/build/lib/lean:.lake/packages/mathlib/.lake/build/lib/lean:.lake/packages/batteries/.lake/build/lib/lean:.lake/packages/Qq/.lake/build/lib/lean:.lake/packages/aesop/.lake/build/lib/lean:.lake/packages/plausible/.lake/build/lib/lean:.lake/packages/importGraph/.lake/build/lib/lean:.lake/packages/LeanSearchClient/.lake/build/lib/lean:.lake/packages/proofwidgets/.lake/build/lib/lean:.lake/packages/Cli/.lake/build/lib/lean /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean -DautoImplicit=false -DrelaxedAutoImplicit=false --setup /private/tmp/YZeroCoarseSubgroupQuotientEtale.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientEtale.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientEtale.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseSubgroupQuotientEtale.c AINTLIBDrafts/YZeroCoarseSubgroupQuotientEtale.lean > /private/tmp/xyin-y0-subgroup-quotient-etale.log 2>&1
```

Canonical `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`,
`.ir.sig`, and `.c` artifacts were checked present. The retained and isolated
copies were byte-equal after compilation. Previously frozen leaves,
other agents' files, the toolchain, and runtime settings were unchanged.
