# Actual quotient places: finite residue verification

`AINTLIBDrafts.YZeroCoarseSubgroupQuotientPlaceResidueFinite` proves that every intrinsic place of the actual subgroup quotient function field has finite residue extension over its original geometric constants in characteristic zero. The raw and public statements quantify over the actual Place type only after the genuine quotient integrality and structure-map base algebra are installed. Neither statement selects a parameter.

The proof obtains an actual transcendental quotient element, installs its literal aeval and ζ algebras, and uses the already proved actual scalar/function-field pack and CharZero separability. The generic intrinsic-place residue theorem then applies. Positive degree is a separate raw/public corollary from actual residue finiteness and `Module.finrank_pos`. Public wrappers use exactly killN/spec. No etale, Noetherian, genus, model, separating-chart, or closed/proper point representation premise is added. The independent originalκQ is retained. This leaf is outside cumulative99.

## Named closed verification

- Owner-polled **90889**, **CLOSED**, exit **0**.
- Source `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseSubgroupQuotientPlaceResidueFinite.lean`: 115 lines, maximum width 94; SHA256 `463f1169ef893930c0a22aa273087c63fccfce2bad5d2c7165ea722c46eadbd8`.
- Correct-name strict setup `/private/tmp/xyin-y0-aintlib-work/YZeroCoarseSubgroupQuotientPlaceResidueFinite.setup.json`, SHA256 `74ce0369ee771c30bfa293a2568c10117dab1409bf1ef908b55c806719354c02`; both implicit options false, no plugins or dynamic libraries.
- Full log `/private/tmp/xyin-y0-subgroup-quotient-place-residue-finite.log`, SHA256 `a563438107e41e11a0c6e318d4e67c7e1440e390d4e61f53341a6052ad234130`.
- **10** exact standard-three checks; four own declarations, two actual API checks (raw residue finiteness and public degree positivity), no warnings, errors, or `sorryAx`.
- Six canonical artifacts plus C are nonzero; sizes and hashes are recorded in `/private/tmp/xyin-y0-subgroup-quotient-place-residue-finite-receipt.json`.
- Retained/work copies are byte-equal. The accepted temporary89 exposed math suffix is byte-identical; retention added only normal license/header and accurate scope docs. The full named log matches the temporary clean first log byte-for-byte.
- Parent and auditor independently read the complete temporary89/source/scalars and full10-check output and accepted the proof contract.

## Reproduction

Cwd `/private/tmp/xyin-y0-aintlib-work`:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/YZeroCoarseSubgroupQuotientPlaceResidueFinite.lean --setup YZeroCoarseSubgroupQuotientPlaceResidueFinite.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientPlaceResidueFinite.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientPlaceResidueFinite.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseSubgroupQuotientPlaceResidueFinite.c > /private/tmp/xyin-y0-subgroup-quotient-place-residue-finite.log 2>&1
```

AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`, Lean `leanprover/lean4:v4.35.0-rc3`. No source/configuration/toolchain or assumption changes.

Temporary72211 and named90889 were both owner-polled CLOSED0 on first runs; no failures were suppressed. The module is frozen. No proper-point representation proof has started.
