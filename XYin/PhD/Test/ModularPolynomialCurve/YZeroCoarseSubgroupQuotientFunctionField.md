# Function fields of the actual raw subgroup quotient

`AINTLIBDrafts/YZeroCoarseSubgroupQuotientFunctionField.lean` proves that the
literal raw quotient projection over any field induces a finite injective map
of the native function fields. Its public wrapper uses the actual `G.killN`
and `G.killN_spec`, so no alternate scalar algebra or quotient is selected.
The literal marked-axis wrapper applies over any field with invertible level.

The proof installs the independently verified integrality of the raw quotient,
its actual surjective projection, and the actual finite projection. It applies
the generic `functionFieldMap_finite` and the native injectivity theorem to
those same schemes and maps. No Noetherianity, etaleness, algebraic closure,
characteristic restriction, genus, or quotient elliptic model is assumed.

Two sanity examples test the public finite ring-map API and the literal
level-three complex-point subgroup. The complex example writes the native
elliptic curve and subgroup types explicitly to select the correct killing
instance. A failed initial fixture is preserved separately; the successful
source changes only these type annotations, not the theorem signatures.

This proves a finite field extension. It does not provide unramifiedness at
places, a genus comparison, a Weierstrass model for the quotient, a target j,
or the modular-polynomial equation. In particular the raw quotient is not
identified with an elliptic-curve record merely from its integrality.

Root read the complete accepted 84-line temporary source and eight-print
log, and an independent reviewer checked the exact native definitions and
hypotheses. The retained module has 104 lines, SHA-256
`55b414d14df7d149ba6965ffb5efb25cf09eb47b36a223d12a53a077ab70fcc3`.
Its accepted mathematical suffix is byte-preserved. Correct-name strict
session 33982 closed with exit 0, exactly eight standard-three-axiom checks,
two passing examples, and zero warnings, errors, or `sorryAx`.

Retained and isolated source copies are byte-equal. All six canonical Lean
artifacts and the C output were checked. The complete named log is
`/private/tmp/xyin-y0-subgroup-quotient-function-field.log`; source/setup/log
and artifact hashes are in
`/private/tmp/xyin-y0-subgroup-quotient-function-field-receipt.json`.
This individual module check is outside the historical 47-module receipt;
the next cumulative retained-library gate must include it.

The isolated environment pins AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
The correct-name setup is
`/private/tmp/xyin-y0-aintlib-work/YZeroCoarseSubgroupQuotientFunctionField.setup.json`,
with both implicit options false and no plugins or dynamic libraries.

```sh
cd /private/tmp/xyin-y0-aintlib-work
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/YZeroCoarseSubgroupQuotientFunctionField.lean --setup YZeroCoarseSubgroupQuotientFunctionField.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientFunctionField.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientFunctionField.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseSubgroupQuotientFunctionField.c > /private/tmp/xyin-y0-subgroup-quotient-function-field.log 2>&1
```
