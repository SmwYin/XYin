# Etaleness of the literal constant-axis subgroup

`constSchemeProjection_etale` proves that the projection of the actual finite
constant scheme is etale over every base scheme. Its proof applies mathlib's
source-local property to the identity maps of the constant components. The
local instance explicitly supplies the existing `HasRingHomProperty` instance;
it adds no axiom or new assumption.

`sectionAxisSubgroup_etale` uses the previously proved actual section-axis
triangle to identify the subgroup projection with this constant projection.
`fullComplexPointAxisSubgroup_etale` specializes it to the native elliptic curve
attached to an actual full-level complex point. The subgroup construction
requires the existing invertibility hypothesis on N; the constant projection
itself does not. Both arbitrary-base and actual level-3 examples pass.

The leaf concerns the subgroup projection. The actual quotient projection is
handled separately by local Hopf descent and the glued chart pullback API.
It supplies neither a Weierstrass model of the quotient nor its j-invariant.

The retained source has 71 lines and SHA-256
`5643897d64343233f0f7ad7834460172950448b149a415f93b545538e60248bb`.
Strict named compilation closed session 1802 with exit 0, five standard-three
axiom checks, two examples, and no diagnostics. Both implicit flags are false;
the retained and isolated copies are byte-identical, and all six named artifacts
exist. The log is `/private/tmp/xyin-y0-constant-axis-etale.log`; the detailed
individual receipt is `/private/tmp/xyin-y0-constant-axis-etale-receipt.json`.
Fresh source, API, and artifact review is recorded in
`../Cleanup/ConstantAxisEtaleReview.md`. The cumulative receipt must separately
include this leaf.

Runtime: Lean v4.35.0-rc3; AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`; mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`. The XYin toolchain is unchanged.
