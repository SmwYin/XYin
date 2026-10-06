# RatFuncTranscendentalParameter verification

The retained module is `AINTLIBDrafts.RatFuncTranscendentalParameter`. It constructs a base-field algebra map from the rational-function field to an independently specified field containing a transcendental element. The definition is the canonical `algEquivOfTranscendental`, followed by the literal adjoin inclusion. Its public formulas give `X ↦ t`, the pointwise polynomial restriction `aeval t`, and equality of the polynomial algebra maps. The fields may have different universes; the supplied target `Algebra k K` remains unchanged.

This module supplies no finite-dimensional, separability, quotient-field, or genus result. Its source is outside the accepted cumulative99 checkpoint.

## Closed compiler receipt

- Owner-polled session **75338**, **CLOSED**, exit **0**.
- Source: `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/RatFuncTranscendentalParameter.lean`; 73 lines, maximum width 94.
- Source SHA256: `aa9a04b31606780121c0aea2d14ac070217fb9216c13ad1209afee8b9e1a7054`.
- Strict setup: `/private/tmp/xyin-y0-aintlib-work/RatFuncTranscendentalParameter.setup.json`; SHA256 `3b0e5783f683d7fec7dc4e2fa6556537094a429aa3ee9d3e75b5d5ba9e8047a1`.
- Correct module name; `autoImplicit=false`, `relaxedAutoImplicit=false`; no plugins or dynamic libraries.
- Full log: `/private/tmp/xyin-y0-ratfunc-transcendental-parameter.log`; SHA256 `ca7e00432e08aca8849e04c497ad1bf4db01d79f1b65f8db9a03e9408a283b45`.
- All **11** exact declaration checks passed: nine standard-three, `AlgHom.comp` uses only `propext` and `Quot.sound`, and `Algebra.algHom` is axiom-free. No warnings, errors, or `sorryAx`.
- Both real examples passed: the rational indeterminate and independently supplied base constants.
- Six canonical artifacts and C output are nonzero; each size and SHA256 is recorded in `/private/tmp/xyin-y0-ratfunc-transcendental-parameter-receipt.json`.
- Retained and isolated source copies are byte-identical. The approved temporary55 mathematical suffix is byte-preserved; retention added only the standard license/header and scope documentation.

## Reproduction

Cwd: `/private/tmp/xyin-y0-aintlib-work`.

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/RatFuncTranscendentalParameter.lean --setup RatFuncTranscendentalParameter.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/RatFuncTranscendentalParameter.olean -i .lake/build/lib/lean/AINTLIBDrafts/RatFuncTranscendentalParameter.ilean -c .lake/build/ir/AINTLIBDrafts/RatFuncTranscendentalParameter.c > /private/tmp/xyin-y0-ratfunc-transcendental-parameter.log 2>&1
```

Pinned AINTLIB: `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`. Pinned mathlib: `300d0e535721bc098547106fc297d8ba2a63f6bb`. Lean: `leanprover/lean4:v4.35.0-rc3`. Native sources, toolchain, and options were not changed.

## Excluded staging output

The first temporary run, session12942, exited1 from the polynomial-ext binder and unnecessary-simpa diagnostics. Its exact source/log are separately preserved; recovery `sorryAx` is not verification. The accepted temporary second run, session55733, was owner-polled CLOSED0 with the same clean11 outputs. The named receipt above verifies the final retained source and its own artifacts.

The module is frozen pending parent review. No finite-pack extension was started.
