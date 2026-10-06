# Native coordinate fraction field verification

The retained module uses the actual inverse native field comparison to embed the chosen Weierstrass coordinate ring into the native function field. The source field algebra remains the independently defined `E.π.functionFieldConstants.toAlgebra`. The proven scalar tower identifies it with the coordinate constants. The coordinate-ring AlgEquiv has the same inverse ring map, and `IsFractionRing.of_algEquiv` then gives the native fraction-field property.

This is over any field, with no algebraic-closedness, characteristic, quotient-model, or genus premise. It does not install global instances. Polynomial/RatFunc scalars, full constants, genus, and a quotient model are outside the module's scope.

The accepted 95-line probe's mathematical suffix, checks, and two actual model/constant examples are byte-preserved. The retained source has 116 lines, width 99, SHA256 `f0d3c86b5cc1c789a1bddc804eff12ab186321fb45f36ece0f10527961d4cdfa`; retained and isolated copies are identical. Only a normal license and scope documentation were added.

Strict named emission session 77344 is CLOSED with exit 0. The complete named log is byte-identical to the successful probe log: nine permitted axiom checks (six standard-three; the scalar-tower constructor uses `propext`; fraction-ring transfer uses `propext, Quot.sound`; AlgEquiv construction uses `Quot.sound`), two examples, and zero diagnostics. Source/setup/log hashes and all six canonical artifacts plus C are verified in `/private/tmp/xyin-y0-native-coordinate-fraction-field-receipt.json`. The correct module setup has `autoImplicit=false`, `relaxedAutoImplicit=false`, and no plugins or dynlibs. No source option was changed.

Literal invocation from `/private/tmp/xyin-y0-aintlib-work`:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/NativeCoordinateFractionField.lean --setup NativeCoordinateFractionField.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/NativeCoordinateFractionField.olean -i .lake/build/lib/lean/AINTLIBDrafts/NativeCoordinateFractionField.ilean -c .lake/build/ir/AINTLIBDrafts/NativeCoordinateFractionField.c > /private/tmp/xyin-y0-native-coordinate-fraction-field.log 2>&1
```

The complete log is `/private/tmp/xyin-y0-native-coordinate-fraction-field.log`. This is an independent leaf receipt after the cumulative-60 checkpoint; that older checkpoint does not certify this new module.
