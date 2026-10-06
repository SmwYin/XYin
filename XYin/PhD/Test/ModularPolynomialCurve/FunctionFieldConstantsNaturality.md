# Naturality of geometric function-field constants

The retained module `AINTLIBDrafts.FunctionFieldConstantsNaturality` defines the actual constants of an integral scheme over an arbitrary field and proves their compatibility with dominant pullback. It uses only `ModularCurves.ForMathlib.DominantFunctionField` as its direct import. No finiteness, algebraic-closedness, characteristic restriction, model, or genus assumption appears.

For `π : X ⟶ Spec k`, the ring homomorphism `π.functionFieldConstants` is the independent geometric composite `k → Γ(Spec k, ⊤) → Γ(X, ⊤) → X.functionField`: the maps are the inverse of `ΓSpecIso`, `π.appTop`, and the generic top germ. Its definition does not refer to a ring equivalence or to a previously chosen scalar structure on the function field.

For integral schemes `X` and `Y`, a dominant `f : X ⟶ Y`, and `π : Y ⟶ Spec k`, the theorem `functionFieldMap_comp_functionFieldConstants` states the literal ring-homomorphism equality

```lean
f.functionFieldMap.hom.comp π.functionFieldConstants =
  (f ≫ π).functionFieldConstants
```

The proof computes the native function-field pullback on the generic germ using `functionFieldMap_germToFunctionField` and then uses the actual `Scheme.Hom.comp_appTop` formula. Both sides obtain constants independently from their structure maps. The theorem therefore supplies the geometric constant square needed when a separately proved over-base equation later identifies a composite structure map.

A uniquely named local instance, `constantsNaturalityTopNonempty`, witnesses the top open's nonemptiness using the actual generic point. The pinned API does not infer this subtype's nonemptiness automatically in the generic setup. The witness is proved from integrality, adds no premise, and is not installed as a global instance. Its axiom closure is printed alongside the two public declarations.

The first example checks the literal geometric formula for the defined constant map. The second checks the native identity pullback on that same geometric expression, using the actual `functionFieldMap_id` theorem. This module does not package a native elliptic-curve algebra equivalence, transport a chosen model's constants, prove a genus result, or construct a subgroup-quotient Weierstrass model.

## Temporary provenance

The accepted 57-line source is `/private/tmp/xyin-y0-aintlib-work/YZeroFunctionFieldConstantsNaturalityProbe.lean`, SHA256 `e52ca2819ae8e442e9dee2dea9804768fa46fc07c7f19a595c489e9100209cd6`. Strict session `77211` is CLOSED, exit 0. Full output: `/private/tmp/YZeroFunctionFieldConstantsNaturalityProbe-fourth.log`; receipt: `/private/tmp/YZeroFunctionFieldConstantsNaturalityProbe-receipt.json`. All nine printed declarations use only `propext`, `Classical.choice`, and `Quot.sound`. Both literal examples pass, with zero diagnostics and no `sorryAx`.

Earlier staging logs are preserved and excluded. The first attempt failed before Lean elaboration because the setup path was wrong. The second lacked the proved top-open nonemptiness instance. The third already checked the public definition and naturality theorem but failed only in a coercion-heavy identity example; that example was repaired through the public native identity theorem, without changing transparency settings or any mathematical signature. No failed whole-module run is used as a verified receipt.

## Frozen named verification

The retained 77-line source has maximum width 82 and SHA256 `eb8ffff2be247e9b8bc74b648934467ef55638cc010f74925c7861667fd76391`. Retained and isolated copies are byte-equal. The only additions to the accepted temporary source are the license and minimal module documentation; the entire mathematical suffix, local instance, examples, and nine prints are byte-preserved.

Strict named session `43285` is CLOSED, exit 0. Full output is `/private/tmp/xyin-y0-function-field-constants-naturality.log`. All nine expected checks are standard-three, both examples pass, and there are zero warnings/errors or `sorryAx`. Setup uses the correct name `AINTLIBDrafts.FunctionFieldConstantsNaturality`, `autoImplicit=false`, `relaxedAutoImplicit=false`, no plugins, and no dynamic libraries. The six canonical artifacts and generated C output have recorded nonzero sizes and SHA256 hashes in `/private/tmp/FunctionFieldConstantsNaturality-receipt.json`.

Literal compiler invocation, cwd `/private/tmp/xyin-y0-aintlib-work`:

```text
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/FunctionFieldConstantsNaturality.lean --setup FunctionFieldConstantsNaturality.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/FunctionFieldConstantsNaturality.olean -i .lake/build/lib/lean/AINTLIBDrafts/FunctionFieldConstantsNaturality.ilean -c .lake/build/ir/AINTLIBDrafts/FunctionFieldConstantsNaturality.c > /private/tmp/xyin-y0-function-field-constants-naturality.log 2>&1
```

The source is frozen at this receipt. No existing retained Lean leaf, model, toolchain, environment, or execution setting was changed. The parent-reported session budget remains one reset used out of one permitted, with no further reset or paid credit authorized.
