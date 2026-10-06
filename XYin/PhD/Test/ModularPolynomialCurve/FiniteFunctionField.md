# Finite native function-field extensions

The retained module is `AINTLIBDrafts/FiniteFunctionField.lean`. It proves
finite-module extension for the actual function-field pullback of a finite
dominant morphism between integral schemes. All schemes have arbitrary
universe `u`; no field-of-definition, Noetherianity, flatness, dimension,
genus, or elliptic-curve-model hypothesis is added.

The two declarations are in namespace `AlgebraicGeometry`:

```lean
moduleFinite_functionField (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] :
    let _ := functionFieldAlgebra f
    Module.Finite Y.functionField X.functionField

functionFieldMap_finite (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] : f.functionFieldMap.hom.Finite
```

The second API is a definitional wrapper around the first. It packages the
literal native ring homomorphism, whose `toAlgebra` is exactly
`functionFieldAlgebra f`. Callers can use it without choosing an ambient
module structure. This matters particularly for identity morphisms, where
Lean can otherwise infer the canonical field self-module before the intended
local algebra is elaborated. The module sanity explicitly selects the
actual `alg.toModule`; the ring-hom sanity needs no such local selection.

The proof chooses an affine open `U` of `Y` containing its generic point.
Dominance puts the generic point of `X` in `f ⁻¹ᵁ U`, so both chart section
rings have their canonical fraction-field presentations. Finiteness of `f`
makes the preimage affine and supplies the actual finite ring map
`Γ(Y,U) → Γ(X,f ⁻¹ᵁ U)` through `f.finite_app`. Since the target scheme is
integral and therefore reduced, dominance gives scheme-theoretic dominance
and injection of that section map. This is the faithful scalar action needed
by the fraction-ring base-change theorem.

The two towers use literal native maps. The chart-to-source-function-field
map is the source germ after the section pullback. The other tower is checked
using `functionFieldMap_comp_germToFunctionField`, rather than assumed as an
extra hypothesis. The existing
`Algebra.IsAlgebraic.isBaseChange_of_isFractionRing` then identifies
`Y.functionField ⊗[Γ(Y,U)] Γ(X,f ⁻¹ᵁ U)` with `X.functionField` as modules over
`Y.functionField`. Finite-module base change and the actual equivalence finish
the proof. No alternate definition of a function field is introduced.

The three sanity examples exercise the intended native algebra on an
identity map, a finite map `Spec B → Spec R` with its explicit dominance
hypothesis, and the identity native ring-hom interface. This leaf is generic;
applications to the retained actual subgroup quotient remain separate.

The accepted temporary version has 97 lines, SHA-256
`1c371018448d9a9bd5fdf70e364ac1d6d5f61f2a8963b523160a959cedfd9b3d`.
Strict session 76106 exited 0. Root read its actual source and complete final
log before retention. Its historical log and receipt are
`/private/tmp/YZeroFiniteFunctionFieldProbe-ringHom-final.log` and
`/private/tmp/YZeroFiniteFunctionFieldProbe-ringHom-receipt.json`. Earlier
staging failures are preserved separately and excluded from the green
receipt; they concerned explicit primitive arguments and identity-fixture
elaboration. No transparency or lint option was disabled.

The retained source has 118 lines, SHA-256
`d592c0357c72b40265574b3c825b28caa7f70c8576ba41115dd0aa4fbe9279cc`.
Its entire mathematical suffix is byte-preserved from the accepted fixture;
the additions are the license and scope documentation. Maximum Lean line
width is 96. Correct-name strict session 1529 exited 0 with sixteen axiom
checks and three passing examples. Fifteen checks use exactly `propext`,
`Classical.choice`, and `Quot.sound`; `IsScalarTower.of_algebraMap_eq` uses
only `propext`. The complete log contains zero warnings, errors, `sorryAx`,
or unexpected axioms. Retained and isolated source copies are byte-equal.

Named log: `/private/tmp/xyin-y0-finite-function-field.log`.
Structured receipt: `/private/tmp/FiniteFunctionField-receipt.json`.
All six canonical Lean artifacts and the C output are present, with their
paths, sizes, and hashes recorded in the receipt. This is a standalone named
module check; a subsequent cumulative retained-library gate is separate.

The native `DominantFunctionField` dependency had already been produced by
the prior cumulative gate when its exact cached target was validated.
Session 29324 exited 0, 2567 jobs. Its source remained byte-equal to the
pinned source. Four existing upstream `haveI` style warnings were replayed;
they are distinct from this module's zero-diagnostic receipt. The native log
and receipt are `/private/tmp/xyin-y0-dominant-function-field-dependency.log`
and `/private/tmp/YZeroFiniteFunctionFieldProbe-dependency-receipt.json`.

The isolated environment pins AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
Setup `/private/tmp/FiniteFunctionField.setup.json` names
`AINTLIBDrafts.FiniteFunctionField`, sets both implicit options false, and
loads no plugins or dynamic libraries. From
`/private/tmp/xyin-y0-aintlib-work`, the exact command was:

```sh
LEAN_PATH=.lake/build/lib/lean:.lake/packages/mathlib/.lake/build/lib/lean:.lake/packages/batteries/.lake/build/lib/lean:.lake/packages/Qq/.lake/build/lib/lean:.lake/packages/aesop/.lake/build/lib/lean:.lake/packages/plausible/.lake/build/lib/lean:.lake/packages/importGraph/.lake/build/lib/lean:.lake/packages/LeanSearchClient/.lake/build/lib/lean:.lake/packages/proofwidgets/.lake/build/lib/lean:.lake/packages/Cli/.lake/build/lib/lean /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean -DautoImplicit=false -DrelaxedAutoImplicit=false --setup /private/tmp/FiniteFunctionField.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/FiniteFunctionField.olean -i .lake/build/lib/lean/AINTLIBDrafts/FiniteFunctionField.ilean -c .lake/build/ir/AINTLIBDrafts/FiniteFunctionField.c AINTLIBDrafts/FiniteFunctionField.lean > /private/tmp/xyin-y0-finite-function-field.log 2>&1
```

Previously frozen leaves, upstream source, the project toolchain, and runtime
settings were unchanged.
