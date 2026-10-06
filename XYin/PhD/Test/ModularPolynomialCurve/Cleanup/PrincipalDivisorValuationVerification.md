# Intrinsic principal-divisor valuation verification

`AINTLIBDrafts.PrincipalDivisorValuation` proves `v.valuation (u : K) = WithZero.exp (-(principalDivisor k K (Additive.ofMul u) v))` for every unit and intrinsic place. It uses the actual chart/place equivalence, existing chart coefficient identity and normalized valuation equality, transporting the principal divisor through the actual `Finsupp.domCongr`.

The current native principal-divisor definition has explicit polynomial/rational-function scalars, the two scalar towers, FunctionField and separability inputs. They remain explicit here. No full constant field, genus, scheme quotient/model or cross-field pullback premise is used. This does not claim independence under varying chart choices. The two API examples compare the original chart coefficient and recover the valuation of a nonzero constant. This leaf is outside cumulative126.

## Named closed verification

- Owner-polled **27962**, **CLOSED**, exit **0**.
- Source `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/PrincipalDivisorValuation.lean`: 74 lines, maximum width 86; SHA256 `0513a0cdc400a6ed2efd77f21fc5770111846e47b09dc42b6b31bef51c276e86`.
- Correct-name strict setup `/private/tmp/xyin-y0-aintlib-work/PrincipalDivisorValuation.setup.json`, SHA256 `8cdfc904e7377636a8dd0090665ee7f99a8d126294297ddfa70b1c8476772514`; both implicit options false; no plugins or dynamic libraries.
- Full log `/private/tmp/xyin-y0-principal-divisor-valuation.log`, SHA256 `f178b7d9d03f346438aebe80199a4028211580af329f676f3a8c836b0abff606`.
- **8** exact standard-three checks; one owned theorem and two actual chart/constant APIs, no diagnostics or `sorryAx`.
- Six canonical artifacts plus C are nonzero; sizes/hashes in `/private/tmp/xyin-y0-principal-divisor-valuation-receipt.json`.
- Retained/work copies are byte-equal, accepted final53 exposed mathematical suffix byte-identical, and named/final temporary logs byte-equal. Header and accurate scope docs are the only retention delta.
- Parent read complete final53 and full clean fourth output: PASS. The current named module and compiler are frozen, with no further theorem started.

## Failed staging attempts

All three failed exact snapshots and full logs remain separately archived and excluded in the temporary and named receipts. First91830 used unrestricted simp, which rewrote chartToPlace to ofChart before inverse cancellation; second1468 lacked explicit equivMapDomain evaluation and the Additive toMul/ofMul simplification; third61490 used an invalid namespace for the actual root theorem `toMul_ofMul`. Final7562 owner-polled CLOSED0 has the same mathematical statement and assumptions, with restricted source-backed simplification. Recovery `sorryAx` in failed outputs is not verification evidence. No linter or transparency option was disabled.

## Reproduction

Cwd `/private/tmp/xyin-y0-aintlib-work`:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/PrincipalDivisorValuation.lean --setup PrincipalDivisorValuation.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/PrincipalDivisorValuation.olean -i .lake/build/lib/lean/AINTLIBDrafts/PrincipalDivisorValuation.ilean -c .lake/build/ir/AINTLIBDrafts/PrincipalDivisorValuation.c > /private/tmp/xyin-y0-principal-divisor-valuation.log 2>&1
```

AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`, Lean `leanprover/lean4:v4.35.0-rc3`. Prior cumulative126 retained sources and named receipts were untouched.
