# Smooth integral curve closed points as intrinsic places

The actual closed point of an integral curve smooth of relative dimension one
over any field determines an intrinsic vendored RR `FunctionField.Place` of its
literal scheme function field. The base algebra remains the independent geometric
`π.functionFieldBaseAlgebra`.

The proof obtains the genuine stalk DVR from the checked closed-point interface,
installs the actual germ-defined `π.stalkBaseAlgebra`, and uses its proved scalar
tower to the literal function field. The generic DVR-to-place constructor then
proves nontriviality, discreteness and containment of the geometric base constants.
It does not assume any of those facts as additional inputs.

`mem_closedPointPlace_iff` identifies membership with existence of an actual stalk
representative under the canonical `algebraMap (stalk x) X.functionField`. The two
examples check an actual native elliptic curve's stalk element and the independent
geometric constant of the literal raw subgroup quotient. The quotient example uses
its actual killing witness, native integrality and proved relative dimension one
under genuine subgroup etaleness; no additional Noetherian, DVR, normality,
full-constant-field, genus or model premise is added.

No assertion that every place has a scheme centre, no place bijection or morphism
functoriality, no Riemann–Hurwitz formula and no quotient Weierstrass construction
is claimed by this leaf.

Strict named owner-polled verification **34263 CLOSED, exit 0**: eleven exact
standard-three-axiom checks; two real APIs; no diagnostics. Accepted80 mathematical
suffix is byte-preserved; retained/work copies are equal. All six named artifacts
and C output hashes are in `/private/tmp/xyin-y0-scheme-closed-point-place-receipt.json`.
Full log: `/private/tmp/xyin-y0-scheme-closed-point-place.log`.
Source SHA-256: `9f153745732694fbad46f3f848364d8660ed6522d4adfec5fd427798317d02ad`.
The first temporary Exists-elimination failure was preserved and excluded. Its
repair derives the DVR inside a Prop-valued proof before constructing place data,
and makes the intended point/closedness binders explicit. No upstream source,
models, settings or runtime were changed.
