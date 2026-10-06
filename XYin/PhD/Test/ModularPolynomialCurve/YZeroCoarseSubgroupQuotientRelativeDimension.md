# Relative dimension one of the actual quotient

The retained module `AINTLIBDrafts/YZeroCoarseSubgroupQuotientRelativeDimension.lean`
proves `SmoothOfRelativeDimension 1` for the actual raw quotient structure map.
The base is locally Noetherian and the subgroup projection is etale. No domain,
algebraically closed field, quotient model, or genus assumption is introduced.
The actual marked axis supplies subgroup etaleness over any Noetherian ring.

The local conditional API applies to any dimension n: a literal scalar map
which is `RingHom.Locally (IsStandardSmoothOfRelativeDimension n)` gives the
same relative dimension on the actual `quotientToBase`. `Spec_iff` translates
the scalar condition, then composition with the genuine affine-base
isomorphism adds dimension zero. The actual chart theorem instantiates n=1
using the independently checked `quotientBaseHom` result.

Globally, the source-local criterion uses the actual quotient gluing cover.
Each patch receives its native `free_gluePatch` and the Noetherian section
instance. The proved structural triangle rewrites the restricted structure
map as `quotientToBase` followed by the open immersion of the base patch.
Relative dimensions add as 1+0=1. Dimension-one smoothness is not treated as
an idempotent multiplicative property. The public wrapper uses the actual
chosen killing integer; the marked-axis wrapper and level-three complex
example use the same literal native subgroup.

This independently supplies the relative-dimension input needed for the
original raw quotient under these stated scopes. Together with the earlier
properness it makes a smooth proper relative curve. Genus one and a pointed
Weierstrass presentation are still separate requirements; a section and
these curve properties alone do not identify an elliptic curve.

Root's 120-line temporary proof passed strict session 23096 with sixteen
standard-three-axiom checks, two actual examples, and zero diagnostics.
An independent reader reviewed both its complete source and complete log.
The retained 144-line version preserves its entire mathematical suffix,
prints and examples byte-for-byte. Its SHA-256 is
`d5e312b1eff31d61eb8a77cfef58cd41b6aba3d25e323272c0e9cc7bc7c021da`.
Correct-name strict session 61932 closed exit 0, again with all sixteen
checks and both examples, no warnings, errors, or `sorryAx`.

Source copies are identical. All six canonical Lean artifacts and C output
were checked. Detailed source/setup/log/artifact hashes are in
`/private/tmp/xyin-y0-subgroup-quotient-relative-dimension-receipt.json`.
The full named log is
`/private/tmp/xyin-y0-subgroup-quotient-relative-dimension.log`.
The historical 47-module receipt does not cover this leaf; a new cumulative
gate is required.

The pinned environment remains AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, Lean `v4.35.0-rc3`.
The strict setup has no plugins, both implicit options false, and module
name `AINTLIBDrafts.YZeroCoarseSubgroupQuotientRelativeDimension`.

```sh
cd /private/tmp/xyin-y0-aintlib-work
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/YZeroCoarseSubgroupQuotientRelativeDimension.lean --setup YZeroCoarseSubgroupQuotientRelativeDimension.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientRelativeDimension.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientRelativeDimension.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseSubgroupQuotientRelativeDimension.c > /private/tmp/xyin-y0-subgroup-quotient-relative-dimension.log 2>&1
```
