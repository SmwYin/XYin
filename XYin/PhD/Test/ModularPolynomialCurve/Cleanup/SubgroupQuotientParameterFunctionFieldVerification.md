# Actual quotient parameter function-field verification

The retained module `AINTLIBDrafts.YZeroCoarseSubgroupQuotientParameterFunctionField` gives raw and public four-fact scalar/function-field bundles for each actual quotient transcendental t. Both explicitly install polynomial aeval-t and rational-function ζ-t algebras; the original base constants remain the actual quotient structure-map constants. The three scalar towers are base→polynomial→quotient, base→rational-function→quotient, and polynomial→rational-function→quotient. The fourth fact is the finite `FunctionField k Q.functionField` structure over this new parameter.

The base towers use existing `IsScalarTower.of_algHom`; the polynomial tower uses the retained generic scalar theorem; finiteness uses actual quotient parameter finiteness. No old coordinate factorization, quotient model, genus, Noetherian, or etale premise is added. Separate raw/public CharZero corollaries obtain finite algebraicity and existing perfect-field separability over k(X). They assert no arbitrary-parameter separation over a perfect field in positive characteristic. Public statements use literal killN/spec. No finite-residue/place result is in this module. It lies outside cumulative99.

## Named closed verification

- Owner-polled **68733**, **CLOSED**, exit **0**.
- Source `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseSubgroupQuotientParameterFunctionField.lean`: 151 lines, maximum width 86; SHA256 `4eee237db83cd3f6aec44a8d3fd82e1e5028b3939f94f20f6149d34586758649`.
- Strict correct-name setup `/private/tmp/xyin-y0-aintlib-work/YZeroCoarseSubgroupQuotientParameterFunctionField.setup.json`, SHA256 `4c6efc643c7ac09f5c98cf8e2cf91fbf990c4c2224ed7251d62a2ff4ea25d757`; both implicit options false, no plugins or dynamic libraries.
- Full log `/private/tmp/xyin-y0-subgroup-quotient-parameter-function-field.log`, SHA256 `af1ba75782438b323914b6a54a01506c80ec6fe30da6ffa770c154f3df0c56f2`.
- **11** exact checks: ten standard-three and `IsScalarTower.of_algHom` uses only `propext`. Four own declarations, two real API examples (raw arbitrary-field pack and public characteristic-zero separability); no warnings, errors, or `sorryAx`.
- Six canonical artifacts and C are present and nonzero; exact sizes and hashes are in `/private/tmp/xyin-y0-subgroup-quotient-parameter-function-field-receipt.json`.
- Source copies are byte-equal. Accepted temporary124 mathematical suffix is byte-exact; only the standard license/header and accurate scope docs were added. The full named log equals the temporary clean first log byte-for-byte.
- Parent read the full temporary124 source, complete11-check log, and strict provenance and approved before retention.

## Reproduction

Cwd `/private/tmp/xyin-y0-aintlib-work`:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/YZeroCoarseSubgroupQuotientParameterFunctionField.lean --setup YZeroCoarseSubgroupQuotientParameterFunctionField.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientParameterFunctionField.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientParameterFunctionField.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseSubgroupQuotientParameterFunctionField.c > /private/tmp/xyin-y0-subgroup-quotient-parameter-function-field.log 2>&1
```

AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`, Lean `leanprover/lean4:v4.35.0-rc3`. No settings/native source changes.

Temporary56969 and named68733 were both owner-polled CLOSED0 on first attempts, with no failed compiler runs. The module is frozen; no finite-residue/place extension has begun.
