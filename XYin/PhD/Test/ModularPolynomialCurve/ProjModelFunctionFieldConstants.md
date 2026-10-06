# Constants in the projective-model function-field equivalence

The retained module is `AINTLIBDrafts.ProjModelFunctionFieldConstants`. For every field `k` and every elliptic Weierstrass curve `W`, it proves that the native `EllipticCurve.projModelFunctionFieldEquiv W` preserves the actual geometric constant map. No algebraic-closedness, characteristic restriction, extra `DecidableEq`, or genus hypothesis appears in either declaration's signature.

`projModelConstantRingHom W` is defined independently of the equivalence. It is the composite from `k` through `(ΓSpecIso k).inv.hom`, then `(projModelπ W).appTop.hom`, and finally the generic-point germ of global sections. Thus the theorem `projModelFunctionFieldEquiv_comp_constants` checks a genuine geometric diagram: the composite of this ring homomorphism with the existing function-field ring equivalence equals `algebraMap k W.toAffine.FunctionField`.

The proof first identifies the germ of the restriction of a global section to the nonempty affine Z-chart with its original global germ. The public native theorem `coordRingToZSection_algebraMap` identifies the chart image of a coordinate-ring constant with the restricted constant pulled back through the actual structure map. The public `projModelFunctionFieldEquiv_germ` then computes the equivalence on that chart germ. Finally, the canonical scalar tower from `k` through the affine coordinate ring to its fraction field gives the desired constant. An explicitly typed local instance of the chart-constant equality avoids a rewrite mismatch between `ConcreteCategory.hom` and `CommRingCat.Hom.hom`; no transparency option is changed.

The two examples use the literal geometric constant expression. The first checks that the independently defined constant map is exactly that expression. The second checks the resulting pointwise constant-preservation interface for an arbitrary scalar. Neither example defines the source scalars by conjugating through the function-field equivalence.

This module packages the constant-map square for the projective model. An algebra equivalence for an arbitrary native elliptic curve, compatibility after its chosen model isomorphism, a genus computation, and a Weierstrass model for a subgroup quotient remain separate results.

## Native reuse and primitive verification

The reused chart-constant theorem is already public in pinned `ModularCurves.WeilPairing.FieldComparisonBridge`; the `_C` name does not occur in that source. Only the exact missing native leaf was built, strict session `91247`, CLOSED exit 0, 4077 jobs. It compiled `PointsDictionaryGalois` and `FieldComparisonBridge`. Their own historical source traces contain two and eighteen warnings respectively, with zero errors; replayed upstream warnings in the native build log are kept separate from this module's own checks. Native build log: `/private/tmp/YZeroFieldConstants-native-build.log`.

The prerequisite print-only fixture completed as strict session `74543`, CLOSED exit 0. Its seven actual primitive checks all use only `propext`, `Classical.choice`, and `Quot.sound`, including the chart constants, coordinate-germ formulas, localization image formula, and restriction compatibility of germs. The native theorem's actual type includes `DecidableEq`; the retained proof supplies it locally with `classical`. Primitive receipt: `/private/tmp/YZeroFieldConstantsPrimitiveProbe-receipt.json`.

## Temporary provenance

The accepted 79-line source is `/private/tmp/xyin-y0-aintlib-work/YZeroProjModelConstantsProbe.lean`, SHA256 `e49f9336d96936291391edc5e39a16220bcadcd529ea15153c56f54674a5894a`. Strict session `28243` is CLOSED, exit 0. The complete third log contains ten permitted axiom checks: nine standard-three checks and the scalar-tower check using only `propext` and `Quot.sound`. Both examples pass, with zero warnings/errors and no `sorryAx`. Receipt: `/private/tmp/YZeroProjModelConstantsProbe-receipt.json`.

The first and second staging logs are preserved and excluded from verified evidence. They failed respectively because `zChart` needed its native namespace qualifier and because a rewrite required the explicitly typed local chart-constant equality. Their recovered theorem prints are not verification receipts.

## Frozen named verification

The named 104-line source has maximum width 96 and SHA256 `2855cec94626258f833472b78c9f59d46b3416140313493336e273b6b5d0d7f7`. Retained and isolated copies are byte-equal. Removing only the added license and module documentation restores the accepted 79-line mathematical suffix exactly, including both declarations, both examples, and all ten prints.

Strict named session `58776` is CLOSED, exit 0. Full log: `/private/tmp/xyin-y0-projmodel-function-field-constants.log`. It contains all ten expected permitted checks, both examples pass, and there are zero diagnostics or `sorryAx`. Setup uses the correct name `AINTLIBDrafts.ProjModelFunctionFieldConstants`, `autoImplicit=false`, `relaxedAutoImplicit=false`, and no plugins or dynamic libraries. All six canonical named artifacts and generated C output have nonzero sizes and recorded SHA256 hashes in `/private/tmp/ProjModelFunctionFieldConstants-receipt.json`.

Literal compiler invocation, cwd `/private/tmp/xyin-y0-aintlib-work`:

```text
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/ProjModelFunctionFieldConstants.lean --setup ProjModelFunctionFieldConstants.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/ProjModelFunctionFieldConstants.olean -i .lake/build/lib/lean/AINTLIBDrafts/ProjModelFunctionFieldConstants.ilean -c .lake/build/ir/AINTLIBDrafts/ProjModelFunctionFieldConstants.c > /private/tmp/xyin-y0-projmodel-function-field-constants.log 2>&1
```

The Lean source is frozen after this receipt. The existing model, toolchain, and environment were preserved. The parent-reported session budget state is one reset used out of one allowed; no further reset or paid credit is authorized.
