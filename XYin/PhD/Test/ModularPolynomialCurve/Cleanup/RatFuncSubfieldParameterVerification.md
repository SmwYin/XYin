# RatFuncSubfieldParameter verification

The module `AINTLIBDrafts.RatFuncSubfieldParameter` proves a single generic finiteness theorem. For independent k-algebras L and K, an actual k-algebra map `φ : L →ₐ[k] K`, and transcendental `t : L`, the literal rational-function map `ζ(t)` into L is finite whenever K has a supplied source function-field structure and genuine base scalar tower. There is no finite-map premise on φ.

The proof obtains the finite composite using the old source scalars before replacing the rational-function scalars. The new algebras are explicitly `ζ.toRingHom.toAlgebra` on L and `(φ.comp ζ).toRingHom.toAlgebra` on K. The actual φ is repackaged as a rational-function algebra map with definitionally valid scalar compatibility, and `FiniteDimensional.of_injective` transfers finite dimension. Both independently specified k-algebras remain unchanged. No old coordinate factorization into L is assumed, and no actual quotient wrapper or separability claim is supplied. This module is outside cumulative99.

## Named closed verification

- Owner-polled **17900**, **CLOSED**, exit **0**.
- Source `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/RatFuncSubfieldParameter.lean`: 75 lines, maximum width 81; SHA256 `f5def847425d3ac083c5e85eb0a57276bc695e002fa2ac724278862230622dd7`.
- Correct-name strict setup `/private/tmp/xyin-y0-aintlib-work/RatFuncSubfieldParameter.setup.json`, SHA256 `0915d0f3d5d33f7b6eb99006792c616bdaf3239096b0d3bd554c06eba47b6886`. Both implicit options false; no plugins or dynamic libraries.
- Full log `/private/tmp/xyin-y0-ratfunc-subfield-parameter.log`, SHA256 `50e2e95103ed625361aae2255bd50adbdc6eb12e943ce1aafc98a81396a0d45d`.
- All **8** exact checks passed: five standard-three, `RingHom.injective` uses only `propext` and `Quot.sound`, and `RingHom.toAlgebra` and `IsScalarTower.toAlgHom` are axiom-free. No warnings, errors, or `sorryAx`.
- Two genuine API examples passed: the identity field map and the actual source rational-function inclusion.
- Six canonical artifacts and C output are nonzero; exact sizes and hashes are in `/private/tmp/xyin-y0-ratfunc-subfield-parameter-receipt.json`.
- Copies are byte-equal. The accepted temporary52 mathematical suffix is byte-preserved; only standard license/header and accurate docs were added. The full named log equals the accepted first temporary log byte-for-byte.

## Reproduction

Cwd `/private/tmp/xyin-y0-aintlib-work`:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/RatFuncSubfieldParameter.lean --setup RatFuncSubfieldParameter.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/RatFuncSubfieldParameter.olean -i .lake/build/lib/lean/AINTLIBDrafts/RatFuncSubfieldParameter.ilean -c .lake/build/ir/AINTLIBDrafts/RatFuncSubfieldParameter.c > /private/tmp/xyin-y0-ratfunc-subfield-parameter.log 2>&1
```

AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`; mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`; Lean `leanprover/lean4:v4.35.0-rc3`. All settings and native sources were preserved.

The temporary first run21006 and the named first run17900 were both owner-polled CLOSED0. There were no failed compiler attempts. The module is frozen; no actual quotient wrapper was started.
