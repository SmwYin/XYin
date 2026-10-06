# Native field Weierstrass model: verification

For an arbitrary field `k` and the actual native object `E : EllipticCurve (Spec k)`, the module constructs `nativeFieldModelIso E : E.E ≅ projModel (fieldWeierstrassModel E.toEllipticCurveGeom)`. The theorem `nativeFieldModelIso_over` proves that composing its forward map with the model projection gives the original `E.π`.

The model is the retained global field model obtained from the existing top local presentation. Its coefficient map is the literal `(ΓSpecIso k).hom.hom`, not an arbitrary identification. The inverse of the top-open pullback projection brings the actual native curve into its top presentation. The inverse of the coefficient-base-change projection then gives the model over `k`. Both projections are isomorphisms, and the over-base equation uses the actual presentation compatibility, the coefficient pullback square, the top affine `isoSpec` formula, and `pullback.condition`.

There is no algebraic-closedness or characteristic-zero hypothesis, no assumed quotient model, and no genus premise. The example applies the construction to the genuine native `modelEllipticCurve W`. The two own declarations and eleven actual primitives are printed; these include the projective-model function-field equivalence and native integrality helper so their transitive axiom closure is checked rather than inferred from source alone.

The result at this checkpoint is an actual scheme isomorphism over the field. A function-field algebra equivalence preserving constants, native genus computation, and quotient Weierstrass upgrade remain separate tasks. No such conclusion is asserted by this module.

## Temporary provenance

The first complete iso-only check was strict session `38570`, CLOSED exit 0, twelve standard-three checks and one actual model sanity. Its accepted 58-line source is preserved at `/private/tmp/YZeroNativeFieldModelIsoProbe-iso-green.lean`, with receipt `/private/tmp/YZeroNativeFieldModelIsoProbe-iso-receipt.json`.

The over-base extension passed strict session `69528`, CLOSED exit 0, on the actual 102-line source SHA256 `bb09890c31b3f73b6b7fad939c60beea3770ed357776e685cb706c8fa4f9da5d`. Complete output is `/private/tmp/YZeroNativeFieldModelIsoProbe-over-second.log`; receipt `/private/tmp/YZeroNativeFieldModelIsoProbe-over-receipt.json`. The original accepted iso body is byte-preserved.

Earlier failed staging logs are kept separately and excluded: the first iso staging used an incorrect constructor namespace in its sanity/print, the second used an Iso-valued noncomputable sanity, and the first over-base staging lacked only final reassociation before inverse cancellation. None of their recovered outputs is used as a verified receipt.

## Named artifact receipt

The named source is `AINTLIBDrafts/NativeFieldWeierstrassModel.lean`, 129 lines, maximum width 92, SHA256 `925aea83b165dbfbc6fd6bf3df9477535c1dc3b07833ffd4dbf6ce7fddf3d7ab`. Retained and isolated copies are byte-equal. The retention delta consists only of the license and module scope documentation; removing those additions restores the accepted 102-line temporary source exactly, including all declarations, checks, and the example.

Strict named session `94422` is **CLOSED, exit 0**. The complete output `/private/tmp/xyin-y0-native-field-weierstrass-model.log`, SHA256 `1fcc49ffa2e6ec98ac573490df54390d60c4d2b84edddd4aa3c0d88ae39dd283`, contains all **13** printed declarations, each using only `propext`, `Classical.choice`, and `Quot.sound`. The actual model sanity passes; there are zero warnings/errors and no `sorryAx`.

The correct setup name is `AINTLIBDrafts.NativeFieldWeierstrassModel`, with `autoImplicit=false`, `relaxedAutoImplicit=false`, no plugins/dynlibs, and setup SHA256 `411d7198eb48904fd3d105edd7f639b4d5c0183bfda0d7f571510f9f55335a8f`. All six canonical named artifacts (`.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, `.ir.sig`) and generated C output exist and have independently recorded nonzero sizes and hashes in `/private/tmp/xyin-y0-native-field-weierstrass-model-receipt.json`.

Literal invocation, cwd `/private/tmp/xyin-y0-aintlib-work`:

```text
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/NativeFieldWeierstrassModel.lean --setup NativeFieldWeierstrassModel.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/NativeFieldWeierstrassModel.olean -i .lake/build/lib/lean/AINTLIBDrafts/NativeFieldWeierstrassModel.ilean -c .lake/build/ir/AINTLIBDrafts/NativeFieldWeierstrassModel.c > /private/tmp/xyin-y0-native-field-weierstrass-model.log 2>&1
```

This is the final frozen named source/artifact receipt. Existing toolchain, model, and execution settings were preserved.
