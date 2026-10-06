# Pointed complex isomorphisms and native classifier morphisms

The retained module is `AINTLIBDrafts/YZeroCoarseHomOverClassifiers.lean`.
It converts an actual pointed morphism `f : E.HomOver E'`, together with
`IsIso f.hom`, into an actual morphism `complexEllObj E ⟶ complexEllObj E'`.
Both curves live over the original `Spec ℂ`; there is no replacement curve or
chosen geometric model in this conversion.

The base morphism is literally the identity, and the top morphism is literally
`f.hom`. The cartesian-square proof is the native `IsPullback.of_horiz_isIso`
applied to `f.over_w`, while preservation of zero is `f.zero_w`. The isomorphism
assumption is necessary here: a general pointed morphism over an unchanged base
does not give the cartesian square required by `EllHom`.

The two section APIs are

```lean
(EllHom.pullSection (.of ℂ) (complexEllHomOfHomOver E E' f) Q).val ≫ f.hom = Q.val

EllHom.pullSection (.of ℂ) (complexEllHomOfHomOver E E' f) Q = P ↔
  P.val ≫ f.hom = Q.val
```

The first equation is the pullback universal property's `lift_fst` equation.
The reverse implication of the second uses cancellation by the given
isomorphism. Thus a forward point-preservation equation can be used directly to
prove the contravariant section equation, without separately constructing an
inverse curve morphism. In particular, a `HomOver.mapPoint` equality yields the
right-hand equation by applying `congrArg Subtype.val`.

This file imports only the marked-complex-curves layer and the upstream
`Moduli.Groupoid` module. It has no additional `Coarse` import, no full-level
hypothesis, and no dependency on the sorried full-level automorphism theorem.
The subsequent full-level functor equality and descent through `GammaHClasses`
belong to the next module. The present bridge is independent of `N`, so its
sanity check is identity-isomorphism transport rather than an artificial
level-three specialization.

The isolated environment is pinned to AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
The user's local Lean `v4.30.0` configuration was not changed.

The exact temporary fixture passed its strict direct check with zero
warnings/errors, five own plus two primitive axiom checks containing only
`propext`, `Classical.choice`, and `Quot.sound`, and the identity transport
example. The retained artifact run uses `autoImplicit = false` and
`relaxedAutoImplicit = false`, with a separate setup carrying the correct
`AINTLIBDrafts.YZeroCoarseHomOverClassifiers` module name. It also passed with
exit 0, zero warnings/errors, all seven standard-axiom checks, and the identity
transport example. Its receipt is `/private/tmp/xyin-y0-homover-classifiers.log`;
the `.olean`, `.olean.private`, `.olean.server`, `.ilean`, and `.ir` artifacts
were emitted in the isolated worktree's `.lake/build/lib/lean/AINTLIBDrafts/`.

The retained source has 97 lines and SHA-256
`cbd657598d8d85a28a8ed30928888fd5e0c716d4314f35fb39294ee308581f65`.
The exact invocation, from `/private/tmp/xyin-y0-aintlib-work`, was

```sh
LEAN_PATH=.lake/build/lib/lean:.lake/packages/mathlib/.lake/build/lib/lean:.lake/packages/batteries/.lake/build/lib/lean:.lake/packages/Qq/.lake/build/lib/lean:.lake/packages/aesop/.lake/build/lib/lean:.lake/packages/plausible/.lake/build/lib/lean:.lake/packages/importGraph/.lake/build/lib/lean:.lake/packages/LeanSearchClient/.lake/build/lib/lean:.lake/packages/proofwidgets/.lake/build/lib/lean:.lake/packages/Cli/.lake/build/lib/lean /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean --setup /private/tmp/YZeroCoarseHomOverClassifiers.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseHomOverClassifiers.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseHomOverClassifiers.ilean AINTLIBDrafts/YZeroCoarseHomOverClassifiers.lean > /private/tmp/xyin-y0-homover-classifiers.log 2>&1
```
