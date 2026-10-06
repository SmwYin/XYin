# Literal stalk and function-field pullback square

The retained module `AINTLIBDrafts.StalkFunctionFieldSquare` proves that a
dominant morphism between irreducible schemes gives a commuting square of
the literal native function-field pullback, its actual stalk map, and both
canonical stalk-to-function-field algebra maps. It applies at every source
point and requires no field, integrality, finite type, closed-point,
normality or DVR hypothesis. The generic function fields here are generic
stalks; integrality is needed separately when using their field instances.

The proof checks the square on actual germs. Its identity example and actual
raw subgroup-quotient example use those same four maps. The quotient client
installs the already proved integrality and surjectivity of the actual map.
This supplies the missing scalar-tower square for a later comparison of
closed-point valuations; it makes no ramification, Riemann–Hurwitz or genus
claim.

## Verification

- Pinned AINTLIB: `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`.
- Pinned mathlib: `300d0e535721bc098547106fc297d8ba2a63f6bb`.
- Lean: `4.35.0-rc3`, in the isolated AINTLIB worktree.
- Named strict compilation: owner-polled session `15461`, CLOSED, exit 0.
- Eleven exact axiom checks use only `propext`, `Classical.choice`, and
  `Quot.sound`; both API examples pass, with no own diagnostics.
- Retained source: 99 lines, maximum width 88, SHA-256
  `b4fb7ddf00988a3124239486c740b67aac6d4e23a3e489164ca380894fbed1e9`.
- The accepted temporary module's mathematical suffix is byte-preserved;
  retained and isolated sources are identical. All six named artifacts and
  generated C have recorded hashes.
- Full named log: `/private/tmp/xyin-y0-stalk-function-field-square.log`.
- Full provenance receipt:
  `/private/tmp/xyin-y0-stalk-function-field-square-receipt.json`.

The first temporary failure and its source/log remain archived and excluded
from this receipt. The final temporary and named compilations checked the
explicit source-preimage membership and genuine germ pullback equation,
without changing the theorem's assumptions or compiler options.

The source is frozen pending the cumulative retained-module gate.
