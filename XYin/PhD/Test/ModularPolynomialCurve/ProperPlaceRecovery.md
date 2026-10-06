# Actual place recovery and finite-residue proper representation

`closedPointPlace_eq_of_generic_lift` proves that the actual closed centre of
a genuine generic lift recovers its original intrinsic Place. It installs the
independently geometric constants and stalk scalars, derives the genuine
closed-point stalk DVR from relative dimension one, and uses the verified
centre-stalk square to put every canonical stalk image in the Place. Native
DVR-place recovery then gives exact equality.

`exists_closedPointPlace_eq` combines this with the actual proper lift and
closed-centre theorem. For an integral smooth proper curve of relative
dimension one over any field, each Place with a finite genuine residue field
is represented by an actual closed point. That finite-residue input remains
explicit. Neither all-place residue finiteness nor point injectivity, place
bijection or genus is assumed or concluded here.

Both native elliptic-curve API examples pass. The approved 86-line temporary
mathematical suffix is byte-preserved in the 104-line named module (maximum
width 95); retained/work copies agree. Strict named compilation was
owner-polled **18121 CLOSED, exit 0**, with **12 exact standard-three-axiom
checks**, two APIs and no diagnostics. No failed attempt or proof repair was
needed in either temporary or named verification. Source is frozen; SHA-256:
`7a8d054c38861b19b36ed71cc8a866c5f9ebb6e94f30c92364732adadde3847d`.

Full named log: `/private/tmp/xyin-y0-proper-place-recovery.log`.
Source/setup/log, exact checks, accepted suffix and all six artifacts plus C
hashes: `/private/tmp/xyin-y0-proper-place-recovery-receipt.json`.
The independent temporary review is recorded in
`Cleanup/ProperPlaceRecoveryReview.md`.

The isolated environment remains pinned to AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean 4.35.0-rc3.
