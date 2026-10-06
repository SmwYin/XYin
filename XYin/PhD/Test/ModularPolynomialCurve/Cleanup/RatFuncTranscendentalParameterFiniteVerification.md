# RatFuncTranscendentalParameterFinite verification

The retained module `AINTLIBDrafts.RatFuncTranscendentalParameterFinite` proves exactly two generic helpers. With a supplied source `FunctionField k K` and actual `k → k(X) → K` scalar tower, the literal transcendental-parameter ring map to K is finite. Its proof uses the existing finite-over-adjoin theorem and the composition of the actual inclusion with the finite canonical equivalence. For an independently specified `φ : L →ₐ[k] K`, injectivity transports transcendence and localization extensionality compares the two actual polynomial restrictions, giving `φ.comp ζ(t) = ζ(φ(t))`.

No old source coordinate is assumed to descend into L. The naturality theorem has no source FunctionField hypothesis. The fields may occupy three different universes. This module constructs no quotient finite pack or separability result and is outside the accepted cumulative99 checkpoint.

## Named closed verification

- Owner-polled **84626**, **CLOSED**, exit **0**.
- Source `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/RatFuncTranscendentalParameterFinite.lean`: 93 lines, maximum width 92; SHA256 `3654ee00691c2ee943809c93f36f44e640b1bb414cfb31e1d7fa175fd20bec4a`.
- Correct-name strict setup `/private/tmp/xyin-y0-aintlib-work/RatFuncTranscendentalParameterFinite.setup.json`; SHA256 `4f4b654deb4e87bc401424752b87e99819d53daf03fdf69d72dcfcc5b10bbf46`. Implicit options both false; no plugins or dynamic libraries.
- Full log `/private/tmp/xyin-y0-ratfunc-transcendental-parameter-finite.log`; SHA256 `bca3455204f9fa77ffcd7bc150920e74198d39afc59d93657f89f1be530bf415`.
- **11** exact declaration checks: nine standard-three; `IsLocalization.algHom_ext` and `RingHom.injective` use only `propext` and `Quot.sound`. No warnings, errors, or `sorryAx`.
- Two real APIs passed: the rational indeterminate's finite map and naturality for the identity field map.
- Six canonical artifacts and C output are present and nonzero; exact sizes and SHA256 values are in `/private/tmp/xyin-y0-ratfunc-transcendental-parameter-finite-receipt.json`.
- Retained/work copies are byte-equal. The accepted temporary71 mathematical suffix is byte-exact; only standard license/header and accurate scope docs were added. The complete named log is byte-identical to the accepted temporary third log.

## Reproduction

Cwd `/private/tmp/xyin-y0-aintlib-work`:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/RatFuncTranscendentalParameterFinite.lean --setup RatFuncTranscendentalParameterFinite.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/RatFuncTranscendentalParameterFinite.olean -i .lake/build/lib/lean/AINTLIBDrafts/RatFuncTranscendentalParameterFinite.ilean -c .lake/build/ir/AINTLIBDrafts/RatFuncTranscendentalParameterFinite.c > /private/tmp/xyin-y0-ratfunc-transcendental-parameter-finite.log 2>&1
```

AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`, Lean `leanprover/lean4:v4.35.0-rc3`. No source, setting, toolchain, or hypothesis weakening was used.

## Failed staging excluded

First temporary71439 and second74727 were owner-polled CLOSED1. The first had an inline transcendence-proof rewrite mismatch and an incorrect primitive print name; changing ht's type merely reversed the rewrite mismatch in the second. Both exact failed sources/logs are preserved in the receipt and their compiler recovery `sorryAx` outputs are excluded. Final temporary63184 instead uses a typed calc/congruence equality chain with unchanged statement and assumptions, and was CLOSED0. Named84626 verifies its retained source and own emitted artifacts.

The module is frozen. The next generic subfield finiteness proof has not been started.
