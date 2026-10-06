# Native full constant field verification

The actual native elliptic curve's function field uses exactly its independently defined geometric projection algebra, `E.π.functionFieldBaseAlgebra`. The theorem constructs all coordinate fraction-ring, polynomial and rational-function scalars, scalar towers, finiteness and separability from the already verified native model pack. It then applies the clean native `FibreRR.isFullConstantField` endpoint. No constant-field or genus assumption is introduced.

The actual-model example and algebraic-element reflection example both compile over arbitrary fields. There is no characteristic restriction, new global instance, or quotient-model conclusion.

## Exact compiler receipt

- Module: `AINTLIBDrafts.NativeFullConstantField`; strict named session 49100 CLOSED, exit 0.
- Source: 77 lines; SHA-256 `40450b851f2f20fae22ea6c982a68c57c2e7548981b81c87e5c4c6be4c2eeefd`.
- Retained and isolated copies are byte-equal. The accepted 59-line temporary mathematical suffix is byte-preserved; only license and scope documentation were added.
- All 11 printed declarations have exactly `propext`, `Classical.choice`, `Quot.sound`; two real APIs pass; no diagnostics or `sorryAx`.
- Setup: `/private/tmp/xyin-y0-aintlib-work/NativeFullConstantField.setup.json`; SHA-256 `9d7b114a6949f8d95a835f35c4c853dbaf996588e4154af2308b27311c0ce859`; both implicit options false, no plugins/dynlibs.
- Full log: `/private/tmp/xyin-y0-native-full-constant-field.log`; SHA-256 `61bf50bed02d0b717240dbfe25d15979129b1091d80f5928b695a9eb6ba2645d`.
- Six canonical named Lean artifacts and the C output exist and have recorded nonzero sizes and hashes.
- Structured receipt: `/private/tmp/xyin-y0-native-full-constant-field-receipt.json`.

```text
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/NativeFullConstantField.lean --setup NativeFullConstantField.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/NativeFullConstantField.olean -i .lake/build/lib/lean/AINTLIBDrafts/NativeFullConstantField.ilean -c .lake/build/ir/AINTLIBDrafts/NativeFullConstantField.c > /private/tmp/xyin-y0-native-full-constant-field.log 2>&1
```

The native RR dependency build's historical warnings are separately recorded in `/private/tmp/YZeroNativeRRPrimitive-dependency-receipt.json`; the retained module has none. This module was added after the cumulative-76 checkpoint and is outside that receipt. Its genus application is a separate bounded next proof.
