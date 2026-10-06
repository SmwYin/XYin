# Formal unramifiedness of the native generic-stalk pullback

The retained module is `AINTLIBDrafts/FunctionFieldFormallyUnramified.lean`.
Its sole declaration, in namespace `AlgebraicGeometry`, is:

```lean
functionFieldMap_formallyUnramified (f : X ⟶ Y) [FormallyUnramified f]
    [IsDominant f] [IrreducibleSpace X] [IrreducibleSpace Y] :
    f.functionFieldMap.hom.FormallyUnramified
```

The exact native `functionFieldMap` is a generic-point stalk map preceded by
`eqToHom`, using dominance to identify the image generic point with the
target's generic point. `FormallyUnramified.stalkMap` supplies the property
on the actual stalk map. `RingHom.FormallyUnramified.respectsIso` and
`cancel_left_isIso` transport it across that literal equality isomorphism.
The proof consists of unfolding the native definition, rewriting the ring
homomorphism of the composite, and applying the existing cancellation iff
in its reverse direction.

The assumptions are intentionally only irreducibility and the two morphism
properties. Here the native object named `functionField` is a generic stalk;
for an integral scheme it has the existing field structure. Irreducibility
alone does not make it a field. The theorem requires no reducedness,
integrality, finiteness, scalar tower, or choice of an alternative function
field. Separability and actual étaleness remain additional conclusions.
The identity sanity exercises the same native API on an arbitrary
irreducible scheme, without adding an integral hypothesis.

The accepted temporary fixture has 37 lines, SHA-256
`f9ff48f43bf0461f66d31627502c13e33e4e31dcb0c23b55630efe5b6fcf060f`.
Strict final session 97404 exited 0 with seven standard-three-axiom checks,
one example, and zero diagnostics. Root read the actual final source and
complete output before authorizing retention. The first elaboration was
also green (session 17555); its sole subsequent delta was a docstring
clarifying that the minimal assumptions concern generic stalks.
Temporary receipt: `/private/tmp/YZeroFunctionFieldUnramifiedProbe-receipt.json`.

The retained source has 57 lines, SHA-256
`f0cf34fc727048d6d4fdc330c45ba34823126ebf31e5da6e75a30434c4bbf893`.
Its entire mathematical suffix, including the identity example and seven
axiom prints, is byte-preserved. License and scope documentation are the
only additions. Maximum Lean line width is 97. Correct-name strict session
46190 exited 0; all seven checks use exactly `propext`, `Classical.choice`,
and `Quot.sound`, with one passing example and zero warnings/errors or
`sorryAx`. The retained and isolated copies are byte-equal.

Named log: `/private/tmp/xyin-y0-function-field-formally-unramified.log`.
Receipt: `/private/tmp/FunctionFieldFormallyUnramified-receipt.json`.
The receipt records exact source/setup/log hashes and all six canonical
Lean artifacts plus C output. This named check is distinct from a later
cumulative retained-library gate.

The isolated pins are AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`,
mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
Setup `/private/tmp/FunctionFieldFormallyUnramified.setup.json` names
`AINTLIBDrafts.FunctionFieldFormallyUnramified`, disables both implicit
options, and loads no plugins or dynamic libraries. From the isolated
worktree `/private/tmp/xyin-y0-aintlib-work`, the exact command was:

```sh
LEAN_PATH=.lake/build/lib/lean:.lake/packages/mathlib/.lake/build/lib/lean:.lake/packages/batteries/.lake/build/lib/lean:.lake/packages/Qq/.lake/build/lib/lean:.lake/packages/aesop/.lake/build/lib/lean:.lake/packages/plausible/.lake/build/lib/lean:.lake/packages/importGraph/.lake/build/lib/lean:.lake/packages/LeanSearchClient/.lake/build/lib/lean:.lake/packages/proofwidgets/.lake/build/lib/lean:.lake/packages/Cli/.lake/build/lib/lean /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean -DautoImplicit=false -DrelaxedAutoImplicit=false --setup /private/tmp/FunctionFieldFormallyUnramified.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/FunctionFieldFormallyUnramified.olean -i .lake/build/lib/lean/AINTLIBDrafts/FunctionFieldFormallyUnramified.ilean -c .lake/build/ir/AINTLIBDrafts/FunctionFieldFormallyUnramified.c AINTLIBDrafts/FunctionFieldFormallyUnramified.lean > /private/tmp/xyin-y0-function-field-formally-unramified.log 2>&1
```

Other retained leaves, upstream source, the toolchain, and runtime settings
were unchanged.
