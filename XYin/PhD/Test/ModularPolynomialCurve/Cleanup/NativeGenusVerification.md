# Native intrinsic genus verification

The only curve input is the actual native elliptic curve over an arbitrary field. The statement installs exactly `E.π.functionFieldBaseAlgebra` and asserts its intrinsic `FunctionField.genus` is one. It has no chart, full-constant-field, genus, characteristic or quotient-model hypotheses.

The proof installs the verified coordinate fraction-field, polynomial and rational-function scalar pack, finite/separable structures, independent base tower and proved full-constant-field factory. It applies `FunctionField.genus_eq_genusChart`, followed by the chosen genuine Weierstrass model's clean `Chart.genus_eq_one`. The intrinsic genus itself is defined using only the original field algebra, so the local coordinate choices are proof inputs.

The two examples check the actual projective-model native elliptic curve and the literal geometric scalar map `ΓSpecIso.inv → E.π.appTop → generic top germ`. No target genus, target j, quotient elliptic model, or Riemann–Hurwitz formula is asserted.

## Exact compiler receipt

- Strict correct-name emission session 21372 CLOSED, exit 0.
- Source `AINTLIBDrafts.NativeGenus`: 80 lines, SHA-256 `26f006dc6ef42e7adba7bfa4ac033fafc6b936c70372b3ca0d34c4ef9de2296e`.
- Accepted 62-line temporary mathematical suffix is byte-identical; retained and isolated copies equal. Only license and scope documentation were added.
- All 12 printed declarations depend on exactly `propext`, `Classical.choice`, `Quot.sound`; both examples pass; no diagnostics or `sorryAx`.
- Setup `/private/tmp/xyin-y0-aintlib-work/NativeGenus.setup.json` SHA-256 `d0846e706f478da85af526e0965f350c905858f25737a1363e4beb3dc1510b54`; both implicit flags false, no plugins/dynlibs.
- Full output `/private/tmp/xyin-y0-native-genus.log` SHA-256 `8ed54ace16a226c8c3298bd2512e9bb682cb6976caf2cd27c20afeeecd83eef5`.
- Six canonical artifacts and C output exist with nonzero sizes and recorded hashes.
- Structured receipt `/private/tmp/xyin-y0-native-genus-receipt.json`.

```text
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/NativeGenus.lean --setup NativeGenus.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/NativeGenus.olean -i .lake/build/lib/lean/AINTLIBDrafts/NativeGenus.ilean -c .lake/build/ir/AINTLIBDrafts/NativeGenus.c > /private/tmp/xyin-y0-native-genus.log 2>&1
```

The underlying native RR dependency build's historical warnings are kept separately in `/private/tmp/YZeroNativeRRPrimitive-dependency-receipt.json`. This retained leaf is outside the cumulative-76 checkpoint. No further proof or global instance was added.
