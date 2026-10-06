# Closed centres of proper lifts with finite residue

`isClosed_placeLift_center` proves that an actual lift of an intrinsic place
has closed centre whenever its genuine residue field is finite over the base
field and its base triangle commutes. The structure map needs only
separatedness. The proof uses the literal residue morphism, the canonical
`k → V → κ(V)` scalar triangle, and the already verified finite-field-point
closed-image theorem. Actual `comap_residue` identifies that image with the
centre `l (closedPoint V)`.

`exists_properPlaceLift_closed_center` combines this result with the genuine
proper valuative-criterion lift. It preserves both literal generic and base
triangles and adds closedness. Residue finiteness remains explicit; place
recovery, place correspondence and genus are separate tasks.

The approved 90-line temporary mathematical suffix is byte-preserved in the
108-line named module (maximum width 94). Strict named compilation was
owner-polled **25761 CLOSED, exit 0**. All **nine checks** use exactly the three
standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Both generic and
native elliptic-curve APIs pass, with no warnings, errors or `sorryAx`.

Retained/work copies agree. Frozen source SHA-256:
`642ea2ad55eaaa8e33015300dd3255f0b740837967ecbc05a649988ec72cbbdf`.
Full named log: `/private/tmp/xyin-y0-proper-place-closed-center.log`.
Full provenance, strict setup, source/log hashes, six named artifacts and C
are recorded in `/private/tmp/xyin-y0-proper-place-closed-center-receipt.json`.

The first temporary invocation failed before elaboration because two new
import-artifact entries used the wrong JSON shape. Its source, setup and full
log are preserved and excluded. Only those entries were corrected to the
existing two-array schema. No Lean proof, assumption, scalar definition,
compiler option, model or environment setting changed.

The isolated environment remains pinned to AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean 4.35.0-rc3.
