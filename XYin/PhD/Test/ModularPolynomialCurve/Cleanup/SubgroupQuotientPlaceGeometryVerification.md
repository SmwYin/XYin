# Actual quotient places: closed-point representation verification

`AINTLIBDrafts.YZeroCoarseSubgroupQuotientPlaceGeometry` proves that every intrinsic place of the actual subgroup quotient function field is represented by an actual closed quotient point, over a characteristic-zero field and with etale subgroup structural map. The equality is with the literal `closedPointPlace` using the original geometric structure-map constants.

The raw proof installs the already proved quotient integrality, smoothness of relative dimension one and properness (field-base Noetherianity is inferred), then applies proper place recovery using actual all-place residue finiteness. Public statements use exactly native killN/spec. No parameter, chart, residue-finiteness, genus or Weierstrass-model hypothesis is added. This is existence of a real closed-point representation; point injectivity, a point/place bijection, quotient genus and quotient j remain separate. This leaf is outside cumulative99.

## Named closed verification

- Owner-polled **39857**, **CLOSED**, exit **0**.
- Source `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseSubgroupQuotientPlaceGeometry.lean`: 101 lines, maximum width 86; SHA256 `755fd186e3efbd29ea5f4f2d2eea0948bc62a21d49c7ec8b54ee7c6444a42e3d`.
- Correct-name strict setup `/private/tmp/xyin-y0-aintlib-work/YZeroCoarseSubgroupQuotientPlaceGeometry.setup.json`, SHA256 `412c41783aee74264bdff1468fb95b92c46b026a9c666ed30370b1873c74e264`; both implicit options false, no plugins or dynamic libraries.
- Full log `/private/tmp/xyin-y0-subgroup-quotient-place-geometry.log`, SHA256 `7b3451ee2090578a23bb492d503a90232f47116cf673748aaf90620e78bd76ba`.
- **9** exact standard-three checks, two owned theorems and two actual raw/public API examples; no warnings, errors or `sorryAx`.
- Six canonical artifacts plus C are nonzero; exact sizes/hashes are in `/private/tmp/xyin-y0-subgroup-quotient-place-geometry-receipt.json`.
- Retained/work copies are byte-equal. The accepted temporary78 exposed mathematical suffix is byte-identical; retention added only normal license/header and accurate scope docs. The named log is byte-identical to the approved first temporary log.
- Parent and auditor independently read the complete temporary78 actual proof and full nine successful outputs and accepted the proof contract. Temporary18946 and named39857 were both owner-polled CLOSED0 on their first runs; no failed runs were suppressed.

## Reproduction

Cwd `/private/tmp/xyin-y0-aintlib-work`:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/YZeroCoarseSubgroupQuotientPlaceGeometry.lean --setup YZeroCoarseSubgroupQuotientPlaceGeometry.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientPlaceGeometry.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientPlaceGeometry.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseSubgroupQuotientPlaceGeometry.c > /private/tmp/xyin-y0-subgroup-quotient-place-geometry.log 2>&1
```

AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`, Lean `leanprover/lean4:v4.35.0-rc3`. No existing source, configuration, toolchain or assumption changes. The module and compiler are frozen for the next cumulative gate.
