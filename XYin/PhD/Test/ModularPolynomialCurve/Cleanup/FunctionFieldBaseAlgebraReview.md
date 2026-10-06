# Independent function-field base-algebra review

Read-only review of root's fresh temporary source `/private/tmp/xyin-y0-aintlib-work/YZeroFunctionFieldBaseAlgebraProbe.lean`, 64 lines, SHA
`9f48d10f1eafc4b13a24ab57ca7d1ca023b6288bca6e4584eeb02d95bab3bf46`, and the full second log `/private/tmp/YZeroFunctionFieldBaseAlgebraProbe-second.log`, SHA `c070ed05e2011028271b6b06144deb64434f4e00060c8014c5f0e90f24264874`.
No source edit, compiler invocation, artifact emission or option change was
performed by this reviewer. The CLOSED exit-0 session 60976 receipt is supplied by
root; this review independently inspected the actual source and all log contents.

Verdict: **PASS** for the stated scope. `functionFieldBaseAlgebra π` is the actual
constant map induced by the structure morphism `π`, converted with `toAlgebra`.
It is specified independently for `Y` via `π` and for `X` via `f ≫ π`. The
function-field extension scalar map is the literal dominant pullback from the
existing `functionFieldAlgebra f`; no replacement algebra chosen from a desired
tower or assumed comparison is introduced.

`isScalarTower_functionFieldBaseAlgebra` applies `IsScalarTower.of_algebraMap_eq`,
whose required equation is the direct `k → K(X)` map equal to the composite
`k → K(Y) → K(X)`. The symmetric direction of the genuine constant-naturality
equality is therefore correct. The `functionFieldBaseAlgHom` uses the same
natural equality in its forward direction for `commutes'`; its underlying ring
hom remains `f.functionFieldMap.hom`, as the first actual example checks by `rfl`.
The second example checks the actual constant scalar map by `rfl`.

The hypotheses are an arbitrary base field, integral source and target schemes,
and dominance of `f`. No finite, flat, genus, model or dimension assumption is
added. The structural map to `Spec k` itself does not need a supplied dominance
hypothesis for this construction. The `@[instance_reducible]` annotation on the
base-algebra definition is a targeted definitional transparency declaration;
there is no global transparency setting or linter/diagnostic suppression.

The inspected log has exactly seven axiom prints: six with the standard three
`propext`, `Classical.choice`, `Quot.sound`; `IsScalarTower.of_algebraMap_eq` only
uses `propext`. There are no errors, warnings or `sorryAx`. Both checked examples
have the asserted scalar directions. The prior transient failure, if any, is not
used as this review's verification evidence.

Source references inspected:

- `FunctionFieldConstantsNaturality.lean`, constants definition and naturality
  proof, SHA `eb8ffff2be247e9b8bc74b648934467ef55638cc010f74925c7861667fd76391`. This is the genuine generic germ map composed with
  `ΓSpecIso.inv` and structural `appTop`; naturality follows the real generic
  germ pullback and `comp_appTop`.
- `DominantFunctionField.lean:53`, `:69`, definition of actual dominant pullback
  and its exact `toAlgebra`, SHA `801809792bc1fce93d82dfaf144f4949d36a2f524f9fc4b952fccd31265c85f2`.
- Mathlib `Algebra/Algebra/Tower.lean:114`, exact scalar-tower equation direction,
  SHA `a43bea3eb561f4851def5553e4f0e0ac00c55b5c2b0060e3acac0c53b8545e7a`.

This review approves only the fresh generic base-algebra/tower/base-AlgHom API.
It does not certify a retained named artifact or any later quotient function-field
degree comparison.

## Correct-name retained artifact follow-up

Independently read the complete retained `AINTLIBDrafts.FunctionFieldBaseAlgebra` source, 82 lines,
SHA `9e32357342d395c82e82fe61d3e50f21519633b237a1514495e9c44e5d81dd59`. Its retained and isolated copies are byte-identical, and the
complete `@[expose] public section` suffix is byte-identical to the reviewed
64-line probe. The added header/docs accurately describe the independent
structure-map scalars and actual dominant pullback. Verdict remains **PASS**.

Independently checked root's correct-name emission receipt
`/private/tmp/FunctionFieldBaseAlgebra-receipt.json`: session 51208 CLOSED exit 0
is supplied by root. The actual full named log has the same seven permitted
prints, two examples and no diagnostics; its hash is `c070ed05e2011028271b6b06144deb64434f4e00060c8014c5f0e90f24264874`.
The exact setup has the correct module name and both implicit-variable options
false; SHA `7cc0245996338d2a239de2e3228610b4d655d414d9709adc3cc17719214f23fa`. All six reported Lean artifacts and
the explicit C output were inspected as nonempty and matched every reported
size and SHA. Six artifact sizes are 28504, 11176, 2720, 7279, 1456, 176;
C output 3009 bytes. No fresh compiler or source change was
performed by this reviewer. This follow-up certifies the retained suffix/copy
and named log/artifact evidence, in addition to the preceding source proof review.
