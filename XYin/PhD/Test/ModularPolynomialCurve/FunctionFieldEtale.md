# Etaleness of the native function-field pullback

The retained module is `AINTLIBDrafts/FunctionFieldEtale.lean`. Its single
generic declaration, in namespace `AlgebraicGeometry`, is:

```lean
functionFieldMap_etale (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [FormallyUnramified f] :
    f.functionFieldMap.hom.Etale
```

The assumption on the original morphism is formal unramifiedness. In
particular, an étale original morphism supplies it through the existing
instance. The theorem works in arbitrary characteristic and does not add
characteristic-zero, perfect-field, Noetherian scheme, flatness, relative
dimension, genus, or quotient-model assumptions.

Every internal field-algebra statement uses the literal native ring map's
`toAlgebra`. The retained `functionFieldMap_finite` gives finite-module
extension for that exact action, and `functionFieldMap_formallyUnramified`
gives formal unramifiedness for the same action. Module finiteness supplies
finite type and hence essentially finite type.
`Algebra.FormallyUnramified.isSeparable` then proves separability over the
actual field, and `Algebra.FormallyEtale.of_isSeparable` gives formal
étaleness. The base function field is Noetherian as a field, so
`Algebra.FinitePresentation.of_finiteType` supplies finite presentation.
The two fields of the existing `Algebra.Etale` class conclude exactly the
requested `RingHom.Etale`, whose definition uses that same `toAlgebra`.
No scalar tower or alternate field definition is introduced.

The identity sanity is stated directly as `RingHom.Etale` of the native
identity pullback. It exercises the intended
scalar structure without ambient self-module inference. This theorem
concerns the generic function-field extension. Ramification of valuation
rings or places is a separate question, and this module supplies no such
place API or quotient-specific specialization.

The accepted temporary source has 46 lines, SHA-256
`53201e85481e8b22c9faf172635a25f14f529f2c8e892fae7de87d9a08047b42`.
Its first elaboration, strict session 10891, exited 0 with nine standard
three-axiom checks, one identity example, and zero warnings/errors. Root read
the actual source and complete output before authorizing retention.
Temporary log: `/private/tmp/YZeroFunctionFieldEtaleProbe-first.log`.
Receipt: `/private/tmp/YZeroFunctionFieldEtaleProbe-receipt.json`.

The retained source has 66 lines, SHA-256
`606a5fc9a92e13126b5a1c6c91ae67af1e7a3b9ed1b5b391f31c854a11f4d8e3`.
Its complete accepted mathematical suffix is byte-preserved, including the
identity example and nine prints. The additions are the license and scope
documentation, and maximum Lean line width is 96. Correct-name strict session
72794 exited 0 with exactly nine checks using `propext`, `Classical.choice`,
and `Quot.sound`, one passing example, and zero diagnostics or `sorryAx`.
Source copies are byte-equal, and all six canonical Lean artifacts and the
C output exist.

Named log: `/private/tmp/xyin-y0-function-field-etale.log`.
Receipt: `/private/tmp/FunctionFieldEtale-receipt.json`, which records the
source/setup/log hashes and artifact paths, sizes, and hashes. This is a
standalone named-module check; a later cumulative retained-library gate is
separate.

The isolated environment pins AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
Setup `/private/tmp/FunctionFieldEtale.setup.json` names
`AINTLIBDrafts.FunctionFieldEtale`, disables both implicit options, and
loads no plugins or dynamic libraries. The exact command, from the isolated
worktree `/private/tmp/xyin-y0-aintlib-work`, was:

```sh
LEAN_PATH=.lake/build/lib/lean:.lake/packages/mathlib/.lake/build/lib/lean:.lake/packages/batteries/.lake/build/lib/lean:.lake/packages/Qq/.lake/build/lib/lean:.lake/packages/aesop/.lake/build/lib/lean:.lake/packages/plausible/.lake/build/lib/lean:.lake/packages/importGraph/.lake/build/lib/lean:.lake/packages/LeanSearchClient/.lake/build/lib/lean:.lake/packages/proofwidgets/.lake/build/lib/lean:.lake/packages/Cli/.lake/build/lib/lean /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean -DautoImplicit=false -DrelaxedAutoImplicit=false --setup /private/tmp/FunctionFieldEtale.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/FunctionFieldEtale.olean -i .lake/build/lib/lean/AINTLIBDrafts/FunctionFieldEtale.ilean -c .lake/build/ir/AINTLIBDrafts/FunctionFieldEtale.c AINTLIBDrafts/FunctionFieldEtale.lean > /private/tmp/xyin-y0-function-field-etale.log 2>&1
```

Other retained leaves, upstream source, the toolchain, and runtime settings
were unchanged.
