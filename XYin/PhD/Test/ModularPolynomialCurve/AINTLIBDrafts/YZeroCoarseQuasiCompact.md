# Actual subgroup quotient: quasi-compactness

This leaf proves `QuasiCompact.of_comp_surjective` for arbitrary schemes:
if `f` is surjective and `f ≫ g` is quasi-compact, then `g` is quasi-compact.
For each compact open U in the target, the composite preimage is compact.
Its continuous image under f is exactly the preimage under g, by surjectivity.
No quasi-compactness or openness assumption on f is needed.

For the actual glued quotient, `gluedQuotientS_quasiCompact` directly installs
its previously proved `UniversallyClosed` structure map and applies mathlib's
existing universally-closed-to-quasi-compact instance. This avoids repeating
the descent argument in that wrapper. The generic descent lemma remains useful:
its composite quasi-compactness assumption is weaker than universal closedness.
The public wrapper uses the same `killN` and `killN_spec` as the actual upstream
quotient definitions. The axis wrapper uses the directly proved killing datum
of the literal marked constant axis over any `Spec R` with N invertible.

The two examples check identity-precomposition for arbitrary schemes and the
literal axis attached to an actual full level-3 complex point. Quasi-compactness
does not supply separatedness, finite type, properness, or an elliptic model.

The final retained module is 98 lines, SHA-256
`3b288e6e58e9ca28bef611e9fd3e62f009a51758f2d80fcb2ed1091d5eddc9b8`.
Strict correctly named compilation closed session 85088 with exit 0; all seven
axiom checks use exactly `propext`, `Classical.choice`, and `Quot.sound`, with no
warnings or errors. The retained and isolated-worktree copies are byte-identical.
The six named Lean artifacts exist. The final log is
`/private/tmp/xyin-y0-quasi-compact-reuse.log`; the setup and receipt are respectively
`/private/tmp/xyin-y0-aintlib-work/YZeroCoarseQuasiCompact.setup.json` and
`/private/tmp/xyin-y0-quasi-compact-receipt.json`. This receipt is an individual
leaf check; the cumulative receipt must also include this module.

The compiler is Lean `v4.35.0-rc3`, with AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17` and mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`. Both implicit flags are false.
The XYin toolchain is unchanged. Reproduce the entire retained bridge with the
driver in the parent README.
