# Actual centre-stalk square of a generic lift

`stalkClosedPointTo_comp_functionField` derives the literal ring-homomorphism
square from an actual generic-lift equation. For any irreducible scheme `X`,
local ring `R`, morphism `l : Spec R → X`, and actual `j : R → X.functionField`,
its only extra input is `Spec.map j ≫ l = X.fromSpecStalk (genericPoint X)`.
The conclusion identifies `j` after the native centre-stalk map with the
canonical `stalkFunctionFieldAlgebra` map.

The proof compares actual Spec maps, uses the native local-spectrum
factorization and specialization triangle, cancels the monomorphism
`X.fromSpecStalk` at the centre, and uses Spec faithfulness. No ring square,
properness, closedness, DVR or normality hypothesis is assumed.

The generic result and original-stalk client need only `IrreducibleSpace X`.
The genuine intrinsic Place client additionally requires `IsIntegral X` to
obtain a field, and its base constants remain independently geometric.
These two binder changes are the complete approved generality delta from the
70-line temporary source; all proof, example and print bodies are preserved.

Strict named compilation was owner-polled **57159 CLOSED, exit 0**. Its eight
checks comprise seven using only `propext`, `Classical.choice`, and `Quot.sound`,
plus the axiom-free `cancel_mono`. Two genuine API clients pass with zero
warnings, errors, `sorryAx` or unexpected axioms. The 89-line source has maximum
width 97, retained/work copies agree, and it is frozen. SHA-256:
`8378448602451a011e8d0a504cedd9dd816d89fc8d98cc5c586566dfd133a986`.

Full named log: `/private/tmp/xyin-y0-place-center-stalk-square.log`.
Full source/setup/log and all six artifact plus C hashes:
`/private/tmp/xyin-y0-place-center-stalk-square-receipt.json`.
The first temporary source/log remain preserved and excluded. Their repairs
only replace categorical composition notation on unbundled ring homomorphisms
with `RingHom.comp` and correct the printed faithful-instance name. No settings
or mathematical premises changed. Named hypothesis weakening passed directly.

The isolated environment remains pinned to AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean 4.35.0-rc3.
