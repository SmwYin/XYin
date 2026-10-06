# Separatedness of the actual raw quotient

`IsSeparated.of_comp_universallyClosed_surjective` works for arbitrary schemes.
If f is universally closed and surjective and f ≫ g is separated, then g is
separated. The product map induced by f is universally closed by base-change
and composition stability. The diagonal square therefore makes f ≫ δg
universally closed; surjectivity descends that property to δg. The diagonal's
closed image and its preimmersion property make it a closed immersion.
`IsSeparated.of_comp_finite_surjective` is a direct finite-map corollary.
No finite-type, Noetherian, or domain assumption is introduced.

For the actual quotient, the finite and surjective projection is proved in the
retained raw-geometry and finite leaves. Its composite with the structure map
is E.π, which is separated by the original elliptic-curve data. This yields
`gluedQuotientS_isSeparated` over every base scheme, and the public wrapper uses
the same actual chosen killing integer. The literal axis wrapper installs its
direct killing datum over arbitrary Spec R. Identity-precomposition and an
actual full level-3 complex point are checked.

The separated raw quotient is not yet an elliptic curve. Its finite type,
properness, smooth relative dimension one, Weierstrass presentation, and target
j still require proofs. The generic diagonal argument can be extracted to a
mathlib-only file independently of these wrappers.

Strict named compilation closed session 35683 with exit 0: eight exact
standard-three axiom checks, two examples, and no diagnostics. The 124-line
retained source SHA-256 is
`27502f8ec523a72c6b531501cbd3d6a729ed6cd25a91c3621a26dfee45d6083f`.
Retained and isolated copies are byte-identical; six named artifacts exist.
The log is `/private/tmp/xyin-y0-subgroup-quotient-separated.log`; the individual
receipt is `/private/tmp/xyin-y0-subgroup-quotient-separated-receipt.json`.
The cumulative receipt must separately include the leaf.

Runtime: Lean v4.35.0-rc3; AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`; mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`. Both implicit flags are false.
The XYin toolchain is unchanged.
