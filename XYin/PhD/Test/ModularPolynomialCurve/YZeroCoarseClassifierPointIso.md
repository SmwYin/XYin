# Equal fine points identify the original marked complex curves

The retained module is `AINTLIBDrafts/YZeroCoarseClassifierPointIso.lean`.
For native curves `E`, `E'` over `Spec ℂ`, actual full-level markings `α`, `β`,
and equality of their actual `fullComplexSchemePointOfMarking` values, it gives
a pointed isomorphism

```lean
complexFullMarkingIsoOfPointEq N hN E E' α β hpoint :
  complexEllObj E ≅ complexEllObj E'
```

and proves the literal moduli-functor transport equation

```lean
(gammaFullNaiveProblem (.of ℂ) N).map
  (complexFullMarkingIsoOfPointEq N hN E E' α β hpoint).hom.op β = α
```

Let `p`, `q` be the two classification points. The construction composes the
existing comparison `i : complexEllObj E ≅ fullComplexPointEllObj N hN p`,
the equality identification `k = eqToIso (congrArg (fullComplexPointEllObj N hN)
hpoint)`, and the inverse comparison
`j.symm : fullComplexPointEllObj N hN q ≅ complexEllObj E'`.
The helper `fullComplexPointLevel_eqToIso` identifies the actual native markings
along `k` by equality induction. With `F = gammaFullNaiveProblem (.of ℂ) N`,
the contravariant marking flow is

```text
β  →  F.map j.inv.op β = t'  →  F.map k.hom.op t' = t  →  F.map i.hom.op t = α.
```

The first step uses `j.inv_hom_id`, because opposite morphisms reverse the
composition. Thus the proof depends on existing marking transport, equality
induction, functor composition, and the actual isomorphism inverse laws. It does
not use the upstream full-level automorphism-freeness theorem or a coarse-point
classification theorem. No curve or marking is replaced by an assumed record.

This theorem uses equality of actual **fine** points. Passage from equal coarse
points to Borel-related markings, conversion of a native elliptic-object
isomorphism to `HomOver`, and injectivity of the native class map are separate
steps. The present file does not assert them.

The pinned isolated environment is AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
The user's local Lean `v4.30.0` configuration was unchanged.

The exact temporary fixture passed its strict direct check with zero
warnings/errors, three own plus two primitive printed axiom checks using only
`propext`, `Classical.choice`, and `Quot.sound` (`eqToIso` uses only `propext`).
Both the identity-isomorphism and actual level-three existence examples passed.
Temporary receipt: `/private/tmp/YZeroClassifierPointIsoProbe.log`.

The retained module has 102 lines and SHA-256
`3ea4c8b5b922cb56253c24be6668a5763b52d1f53f63cdeb536238af7de8522e`.
It preserves the accepted proofs and uses a correctly named strict setup,
`/private/tmp/YZeroCoarseClassifierPointIso.setup.json`, with both
`autoImplicit` and `relaxedAutoImplicit` set to `false`. Retained-artifact receipt:
`/private/tmp/xyin-y0-classifier-point-iso.log`.

The retained strict named emission passed with exit 0, zero warnings/errors,
the same five standard-axiom checks, and both sanity examples. Its `.olean`,
`.olean.private`, `.olean.server`, `.ilean`, and `.ir` artifacts are available
in the isolated worktree. From `/private/tmp/xyin-y0-aintlib-work`, the exact
invocation was

```sh
LEAN_PATH=.lake/build/lib/lean:.lake/packages/mathlib/.lake/build/lib/lean:.lake/packages/batteries/.lake/build/lib/lean:.lake/packages/Qq/.lake/build/lib/lean:.lake/packages/aesop/.lake/build/lib/lean:.lake/packages/plausible/.lake/build/lib/lean:.lake/packages/importGraph/.lake/build/lib/lean:.lake/packages/LeanSearchClient/.lake/build/lib/lean:.lake/packages/proofwidgets/.lake/build/lib/lean:.lake/packages/Cli/.lake/build/lib/lean /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean --setup /private/tmp/YZeroCoarseClassifierPointIso.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseClassifierPointIso.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseClassifierPointIso.ilean AINTLIBDrafts/YZeroCoarseClassifierPointIso.lean > /private/tmp/xyin-y0-classifier-point-iso.log 2>&1
```
