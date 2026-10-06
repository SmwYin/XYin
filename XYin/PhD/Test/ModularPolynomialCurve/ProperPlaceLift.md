# Proper extension of an intrinsic place

For an integral scheme `X` proper over any field `k`,
`exists_properPlaceLift` extends its actual generic-stalk point to the spectrum
of every intrinsic place's valuation subring. Its two literal equations say
that the extension agrees with `X.fromSpecStalk (genericPoint X)` and lies over
the actual `k`-algebra map into the valuation subring.

The geometric constants remain independently defined through ΓSpecIso,
`π.appTop` and the generic germ. The valuation-subring scalar tower is
identified by `rfl`; typed ring arrows then establish the actual Spec square.
The genuine proper valuative criterion supplies the lift. No closed-centre,
finite-residue, smoothness, genus or place-bijection claim is made here.

The accepted 85-line temporary mathematical suffix is byte-preserved in the
103-line named module (maximum width 94). The generic and native elliptic-curve
examples both pass. Strict named compilation was owner-polled **21688 CLOSED,
exit 0**, with **eight exact checks**: seven use only `propext`,
`Classical.choice`, and `Quot.sound`; `CommSq.HasLift.exists_lift` is axiom-free.
There are no warnings, errors, `sorryAx`, unexpected axioms or option changes.

Retained/work copies agree. Source SHA-256:
`9ad941e93939b95efd3973bab5684ee75907b3742e182938738cd4dbfc0688c1`.
Full named log: `/private/tmp/xyin-y0-proper-place-lift.log`.
Source, setup, full log and all six artifacts plus generated C have recorded
hashes in `/private/tmp/xyin-y0-proper-place-lift-receipt.json`.
The source is frozen.

Both unsuccessful temporary sources and full logs are preserved and excluded
from the verified receipt. The first repair enters the proposition under its
base-algebra let; the second introduces typed ring arrows to avoid a
semireducible function-field carrier mismatch during rewriting. Neither repair
changes the theorem, scalar definition, mathematical assumptions or settings.

The isolated environment remains pinned to AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean 4.35.0-rc3.
