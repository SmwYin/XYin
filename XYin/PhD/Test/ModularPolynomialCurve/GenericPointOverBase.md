# Generic point over the independently defined base field

For an integral scheme over any field, `fromSpecFunctionField_comp_structureMap`
proves that its actual generic-stalk point is over the literal geometric constant
map. That map remains independently defined by ΓSpecIso, the structure map's
appTop, and the generic germ. The proof uses actual `fromSpecStalk_appTop` and
affine extensionality; no function-field equivalence defines the scalars.

The two examples spell the same triangle through `functionFieldBaseAlgebra`,
for an arbitrary structure map and for a native elliptic curve. No properness,
smoothness, place-centre existence, closedness or place bijection is asserted.

Strict named compilation was owner-polled **40993 CLOSED, exit 0**. All six
checks use exactly `propext`, `Classical.choice`, and `Quot.sound`; both actual
API examples pass with no diagnostics. The accepted temporary theorem and
proof are byte-preserved, and retained/work copies agree. Source: 77 lines,
maximum width 85, SHA-256
`003005ef864d037a45df3264b153024fc1718b65e530453ed47b8dfc15701b7a`.

All six named artifacts and generated C have recorded hashes in
`/private/tmp/xyin-y0-generic-point-over-base-receipt.json`.
Full named log: `/private/tmp/xyin-y0-generic-point-over-base.log`.
The isolated environment remains pinned to AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean 4.35.0-rc3.

The first temporary source/log are archived and excluded. The only proof
repair replaces an untyped identity-map simplification with the literal
Spec(stalk genericPoint) presheaf's `map_id`, then explicitly normalizes the
ΓSpecIso object. No theorem assumptions, scalar definitions, compiler options,
upstream sources or execution settings changed. The retained source is frozen.
