# Native function-field ring equivalence: verification

For arbitrary `Field k` and the actual native curve `E : EllipticCurve (Spec k)`, `nativeFieldFunctionFieldEquiv` is a ring equivalence from `E.E.functionField` to `(fieldWeierstrassModel E.toEllipticCurveGeom).toAffine.FunctionField`.

The geometric model iso is `E.E ≅ projModel W`. Its inverse has direction `projModel W ⟶ E.E`, so its function-field pullback has the required direction `K(E) ⟶ K(projModel W)`. The existing open-immersion function-field isomorphism supplies that pullback. Its conversion to a RingEquiv followed by the existing projective-model RingEquiv gives the actual native comparison.

`nativeFieldModelIso_functionFieldMap` verifies that the function-field iso's forward map is exactly the literal `(nativeFieldModelIso E).inv.functionFieldMap`; the two generic-point equality proofs agree by proof irrelevance, so this is `rfl`. `nativeFieldFunctionFieldEquiv_toRingHom` identifies the composed forward ring hom with that same actual pullback followed by the actual model bridge, also by `rfl`. The pointwise sanity checks the same forward formula, and the other example applies the comparison to the genuine native `modelEllipticCurve W`.

Only the field hypothesis is present. No algebraic closure, characteristic-zero, chosen quotient model, or genus hypothesis is used. This is a RingEquiv. Compatibility with independently defined geometric constants, an AlgEquiv over `k`, and any genus consequence require separate proofs and are outside the current module.

## Temporary provenance

The final actual 56-line probe has SHA256 `c4fc15897f554639942209c54aa825b42f19f7e9cd13ecf9702dd148112cdf16`. Strict session `23588` is CLOSED, exit 0. Its full output `/private/tmp/YZeroNativeFunctionFieldProbe-second.log` has all eight checks using only the standard three axioms, two examples, and zero diagnostics. The exact temporary source/setup/log receipt is `/private/tmp/YZeroNativeFunctionFieldProbe-receipt.json`.

The first failure and exact source are separately preserved at `/private/tmp/YZeroNativeFunctionFieldProbe-first.log` and `/private/tmp/YZeroNativeFunctionFieldProbe-first.lean`. It concerned two split-dot notation parser failures only; the direct native pullback equality already checked. Its recovered downstream prints are excluded from verification. The mathematical construction was unchanged in the final successful probe.

## Named receipt

The retained module is `AINTLIBDrafts/NativeFieldFunctionFieldEquiv.lean`, 79 lines, maximum width 99, SHA256 `6771234f92f3eaaeb376d9c859c3510d329da00b35de351292e76b3d9aba3ebe`. Retained and isolated source copies are byte-equal. Removing only the added license and module scope documentation restores the accepted full 56-line probe exactly, including all proofs, primitive prints, and both examples.

Named strict session `82623` is **CLOSED, exit 0**. Complete named output `/private/tmp/xyin-y0-native-field-function-field-equiv.log`, SHA256 `32bcdb56f3748952c70ad2275583150cfdab3c5f03928b0d2268bdb65c404262`, contains exactly eight checks, all using only `propext`, `Classical.choice`, and `Quot.sound`. Both genuine API examples pass, with zero warnings/errors or `sorryAx`.

The setup has correct name `AINTLIBDrafts.NativeFieldFunctionFieldEquiv`, both implicit options false, no plugins/dynlibs, and SHA256 `597f2420786d1961239304400ff10b985603f66af15846d87da8c279107d518b`. All six canonical named artifacts (`.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, `.ir.sig`) and C output were independently checked as nonempty and hashed. Their exact sizes and hashes, the source/setup/log values, and suffix preservation are recorded in `/private/tmp/xyin-y0-native-field-function-field-equiv-receipt.json`.

Literal command, cwd `/private/tmp/xyin-y0-aintlib-work`:

```text
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/NativeFieldFunctionFieldEquiv.lean --setup NativeFieldFunctionFieldEquiv.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/NativeFieldFunctionFieldEquiv.olean -i .lake/build/lib/lean/AINTLIBDrafts/NativeFieldFunctionFieldEquiv.ilean -c .lake/build/ir/AINTLIBDrafts/NativeFieldFunctionFieldEquiv.c > /private/tmp/xyin-y0-native-field-function-field-equiv.log 2>&1
```

The source and named artifacts are frozen. Model, toolchain, and execution settings were preserved, with no reset or paid-credit action taken by this worker.
