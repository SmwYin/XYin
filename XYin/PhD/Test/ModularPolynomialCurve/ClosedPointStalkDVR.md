# Closed-point stalk DVR interface

The retained `AINTLIBDrafts.ClosedPointStalkDVR` proves that a closed point of a scheme
smooth of relative dimension one over any field has a literal stalk which is a
domain and a DVR. The conclusion returns the two structures together; the theorem
does not assume that the entire scheme is integral.

The proof chooses an actual standard-smooth affine chart. Its base open contains the
point image in the one-point field spectrum, so equals the whole base. The actual
ΓSpec field isomorphism gives the chart scalar map. Closedness gives a maximal chart
prime; native standard-smooth maximal-localization DVR supplies both structures;
the canonical localization equivalence transfers them to the actual stalk.

The two examples check retrieval of the DVR structure when the scheme already is
integral, and an actual native elliptic curve over an arbitrary field. This is a
closed-point interface: no generic-point or all-point DVR, RR-place, genus or
quotient-model conclusion is asserted.

Strict named verification: owner-polled session **25578 CLOSED, exit 0**. The full
log has eleven exact checks: ten standard-three-axiom checks and one axiom-free
`Function.Injective.isDomain` check; two actual API examples; no diagnostics.
Accepted temporary mathematical suffix is byte-preserved; retained/work sources
are equal. All six named artifacts and C output are recorded in
`/private/tmp/xyin-y0-closed-point-stalk-dvr-receipt.json`.

Current source SHA-256: `91cbf00e6ce879a63e2859d72e29350997ac7d5b35c15af8916e843f80563f9b`.
Full log: `/private/tmp/xyin-y0-closed-point-stalk-dvr.log`.
Historical temporary failure (only missing outer namespace on the existing DVR
transfer primitive) is preserved and excluded in the separate temporary receipt.
No native source, model, runtime or settings were changed.
