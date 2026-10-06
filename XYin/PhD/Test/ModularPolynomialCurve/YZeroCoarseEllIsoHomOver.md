# Native pointed complex isomorphisms recover fixed-base HomOver data

The retained module is `AINTLIBDrafts/YZeroCoarseEllIsoHomOver.lean`.
For any actual native isomorphism

```lean
e : complexEllObj E ≅ complexEllObj E'
```

it constructs `complexHomOverOfEllIso E E' e : E.HomOver E'`, with the literal
underlying morphism `e.hom.top`, a named `IsIso` instance, and exact adapter
reconstruction

```lean
complexEllHomOfHomOver E E' (complexHomOverOfEllIso E E' e) = e.hom.
```

The direction remains `E → E'`. The `[simp]` API
`complexHomOverOfEllIso_hom` exposes the same top morphism by reflexivity.

Every native morphism between these literal complex objects has identity base
map: its `base_w` is `baseHom ≫ id = id`. The recovered `HomOver.over_w` follows
from the actual cartesian square's commutativity, and `zero_w` follows from
native pointedness. Both proofs use explicitly typed scheme-morphism aliases
`t : E.E ⟶ E'.E` and `b : Spec ℂ ⟶ Spec ℂ`, so identity cancellation acts on the
canonical schemes. The total-space isomorphism is the literal record with hom
`e.hom.top`, inv `e.inv.top`, and inverse laws obtained by `congrArg EllHom.top`
from the two original native inverse laws.

These facts do not require a level condition. The adapter reconstruction gives
the interface for transferring an existing native full-level pullback equation
to the fixed-base `HomOver` point-preservation equation. Native class-map
injectivity is a subsequent theorem rather than an assumption of this converter.

The exact temporary fixture passed strict checking with zero warnings/errors
and ten clean axiom prints: seven using only `propext`, `Classical.choice`, and
`Quot.sound`, and three primitive record projections using no axioms. Its
identity-`HomOver` sanity example also passed. Temporary source has 77 lines and
SHA-256 `d2966260ae8bb355294640bc4c508cf5d725324671417f7c67b5703c33a4672d`;
receipt `/private/tmp/YZeroEllIsoHomOverProbe.log`.

The first prototype's semireducible-projection cancellation failure is preserved
at `/private/tmp/YZeroEllIsoHomOverProbe.first-failure.log`. Its failed downstream
kernel and axiom staging output is excluded from verification claims. The
accepted canonical-alias proof is the one retained here.

The pinned isolated environment is AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
The user's local Lean `v4.30.0` configuration was unchanged.

The retained module preserves the accepted core and adds the explicit `[simp]`
top formula and a general-isomorphism sanity example inside the actual
`gammaFullNaiveProblem` functor. It has 110 lines and SHA-256
`17023dc57e5fd6b912e0e2516b24483a2fa06b9675747d0ccb92d62290369220`.
Its exact-name strict setup is `/private/tmp/YZeroCoarseEllIsoHomOver.setup.json`,
with `autoImplicit = false` and `relaxedAutoImplicit = false`; retained-artifact
receipt `/private/tmp/xyin-y0-ell-iso-homover.log`.

The retained strict named artifact emission passed with exit 0 and zero
warnings/errors. All eleven printed checks are clean: eight use only the three
standard axioms, and three primitive projections are axiom-free. Both the
identity-`HomOver` example and the general native-isomorphism level-functor
example passed. The `.olean`, `.olean.private`, `.olean.server`, `.ilean`, and
`.ir` artifacts are available in the isolated worktree. From
`/private/tmp/xyin-y0-aintlib-work`, the exact invocation was

```sh
LEAN_PATH=.lake/build/lib/lean:.lake/packages/mathlib/.lake/build/lib/lean:.lake/packages/batteries/.lake/build/lib/lean:.lake/packages/Qq/.lake/build/lib/lean:.lake/packages/aesop/.lake/build/lib/lean:.lake/packages/plausible/.lake/build/lib/lean:.lake/packages/importGraph/.lake/build/lib/lean:.lake/packages/LeanSearchClient/.lake/build/lib/lean:.lake/packages/proofwidgets/.lake/build/lib/lean:.lake/packages/Cli/.lake/build/lib/lean /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean --setup /private/tmp/YZeroCoarseEllIsoHomOver.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseEllIsoHomOver.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseEllIsoHomOver.ilean AINTLIBDrafts/YZeroCoarseEllIsoHomOver.lean > /private/tmp/xyin-y0-ell-iso-homover.log 2>&1
```
