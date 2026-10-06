# Native function-field AlgEquiv: verification

This module packages five checked APIs over an arbitrary field `k`: the inverse model isomorphism's structure-map equation, the independent geometric constant square for the native function-field RingEquiv, the resulting AlgEquiv, and two `rfl` formulas preserving its underlying RingEquiv and forward RingHom.

The source constants are the actual `E.π.functionFieldConstants`: `(ΓSpecIso k).inv` followed by the native structure map's `appTop` and the generic top germ. They are defined independently of the model RingEquiv. The inverse model is over `Spec k` by cancellation in the previously proved forward structure-map formula. Actual dominant-pullback constant naturality therefore identifies native constants with the model's independently specified constants, and the existing projective-model square identifies the latter with the usual Weierstrass function-field constants.

`nativeFieldFunctionFieldAlgEquiv` explicitly installs `E.π.functionFieldConstants.toAlgebra` in its return type and definition. `AlgEquiv.ofRingEquiv` uses the checked constant square for scalar compatibility. The underlying RingEquiv and RingHom are the previously retained native comparison by definitional equality. This is not an algebra structure defined by transporting through the equivalence, and it adds no global instance.

Only `Field k` is assumed. No algebraic closure, characteristic-zero, quotient Weierstrass model, or genus premise is used. The four examples check the native model constant square, literal native geometric germs, the actual model AlgEquiv, and scalar commutation with the independent source algebra. No fraction-ring tower or genus theorem is asserted here.

## Temporary provenance

The independent constant square first passed on the actual 59-line source, SHA256 `dc5e5a487141d72608fbe569d12d24fea2cb66fb82f91c0a9b0a339305a1f693`, strict session `25117` CLOSED exit 0. That exact source is preserved at `/private/tmp/YZeroNativeFunctionFieldConstantsProbe-constants-green.lean`, separately from its historical ten-check receipt.

The complete 99-line AlgEquiv extension has SHA256 `3401206c77145e9084f5da1cafbd9303f8de1c497b21f85e22846d9d68c1f9c8`. Session `93602` is CLOSED, exit 0. The full second output `/private/tmp/YZeroNativeFunctionFieldConstantsProbe-alg-equiv-second.log` contains fourteen permitted axiom checks: twelve standard-three, `RingHom.comp_assoc` using only `propext` and `Quot.sound`, and `AlgEquiv.ofRingEquiv` using only `Quot.sound`. All four examples pass, with zero diagnostics. The full exact source/setup/log record is `/private/tmp/YZeroNativeFunctionFieldConstantsProbe-alg-equiv-receipt.json`.

The first extension staging failure and exact 98-line source are preserved at `/private/tmp/YZeroNativeFunctionFieldConstantsProbe-alg-equiv-first.log` and `/private/tmp/YZeroNativeFunctionFieldConstantsProbe-alg-equiv-first.lean`. The only repair repeated the same explicit source-algebra let inside the final scalar sanity proof; its five own APIs were already clean. The failed full run is excluded from final verification. The accepted 59-line constant proof and checks are byte-preserved in the successful extension.

## Named receipt

The retained module is `AINTLIBDrafts/NativeFieldFunctionFieldAlgEquiv.lean`, 124 lines, maximum width 100, SHA256 `4d15b82bc3f21e158601d8b0453e75a970204d0521118399a1d6ec2d63e141b5`. Removing only the added license and minimal scope documentation restores the accepted 99-line temporary source exactly. Retained and isolated copies are byte-equal.

Named strict session `35261` is **CLOSED, exit 0**. Complete named output `/private/tmp/xyin-y0-native-field-function-field-alg-equiv.log`, SHA256 `0529b5ecef0e4b8acbb2abf0ca58370e466067850143d9d2501f6889321249b8`, contains all fourteen permitted axiom checks and all four successful examples, with zero warnings/errors or `sorryAx`. The output is byte-identical to the clean current99 temporary output.

The setup name is exactly `AINTLIBDrafts.NativeFieldFunctionFieldAlgEquiv`, both implicit options false, no plugins/dynlibs, and SHA256 `0a173cea220cc2772788af0b7f0e15261ee078ea64fe4d9896b80813bd496462`. All six canonical named artifacts (`.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, `.ir.sig`) and C output were independently read, confirmed nonempty, and hashed. Exact artifact sizes/hashes, source/setup/log values, and accepted99 suffix preservation are in `/private/tmp/xyin-y0-native-field-function-field-alg-equiv-receipt.json`.

Literal command, cwd `/private/tmp/xyin-y0-aintlib-work`:

```text
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/NativeFieldFunctionFieldAlgEquiv.lean --setup NativeFieldFunctionFieldAlgEquiv.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/NativeFieldFunctionFieldAlgEquiv.olean -i .lake/build/lib/lean/AINTLIBDrafts/NativeFieldFunctionFieldAlgEquiv.ilean -c .lake/build/ir/AINTLIBDrafts/NativeFieldFunctionFieldAlgEquiv.c > /private/tmp/xyin-y0-native-field-function-field-alg-equiv.log 2>&1
```

The current99 mathematical source/full second14 output/new receipt received independent read-only review from `/root/aint_build_audit` with PASS. Fresh named source/output/artifact review is requested separately. The named source and artifacts are frozen, and this later module is outside the cumulative60 checkpoint. Model, toolchain, and execution settings were preserved.
