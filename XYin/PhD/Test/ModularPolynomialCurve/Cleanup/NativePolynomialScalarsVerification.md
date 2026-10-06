# Native polynomial scalars verification

The actual `W.algebraPolynomial` constructor uses the retained chosen-coordinate embedding into the native field. The first tower factors the polynomial algebra through that coordinate ring. The second tower proves compatibility with the independent `E.π.functionFieldBaseAlgebra`; it uses the actual coordinate and polynomial towers and the canonical base/polynomial/coordinate tower.

The accepted81 mathematical suffix, checks, and two real chosen-model/constant-map examples are preserved byte-for-byte. The retained source is 100 lines, width 94, SHA256 `1b95aec71cd122011ad0fca7a142fbe8eb5a65d8610ca389464143d598b0971a`. Only a normal license and minimal scope documentation were added. The retained/isolated copies are byte-identical.

Strict named session2177 is CLOSED with exit0. The full named log is byte-identical to the clean second probe log: ten allowed checks (eight standard-three, scalar-tower constructor `propext`, algebra-map formula `propext, Quot.sound`), two examples, zero diagnostics. Source/setup/log hashes and all six canonical artifacts plus C were read and recorded in `/private/tmp/xyin-y0-native-polynomial-scalars-receipt.json`. The exact module setup has both implicit options false and no plugins/dynlibs; no source/config/environment setting was changed.

Literal invocation from `/private/tmp/xyin-y0-aintlib-work`:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/NativePolynomialScalars.lean --setup NativePolynomialScalars.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/NativePolynomialScalars.olean -i .lake/build/lib/lean/AINTLIBDrafts/NativePolynomialScalars.ilean -c .lake/build/ir/AINTLIBDrafts/NativePolynomialScalars.c > /private/tmp/xyin-y0-native-polynomial-scalars.log 2>&1
```

The first temporary attempt failed only on the constant sanity's statement-side let binder. Its exact source and log are preserved separately and excluded. The clean probe added a single explicit `change` before the existing rewrites; the three owned declarations were unchanged. No global instance, additional field hypothesis, RatFunc/FunctionField/separability/fullconstant/genus theorem or quotient model is supplied by this module. It is a later leaf outside the cumulative76 snapshot.
