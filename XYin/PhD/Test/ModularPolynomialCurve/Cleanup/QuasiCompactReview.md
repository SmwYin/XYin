# QuasiCompact independent review

Review date: 2026-10-04. **Verdict: PASS for the retained source and named strict
receipt.** Only this review document was edited; no Lean source or compiler run
was added by this reviewer.

The 101-line snapshot below is a historical receipt. The current source and
fresh verification are recorded in the final reuse-delta section.

## Source and retained delta

[YZeroCoarseQuasiCompact.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseQuasiCompact.lean)
has 101 lines and SHA-256
`8373448e3178e2409995b488f21c8effcd9083795046b687998b18cccaff6c7b`.
The accepted temporary source had 77 lines and SHA-256
`c338ef1445aa98e8d105f95f551370328db29d95380ea374a3de0a7afc63881a`.
The actual retained delta consists only of the license, module exposition, and
four declaration docstrings. Proofs, statements, examples, imports, and axiom
prints are unchanged. The retained and isolated sources were independently
checked byte-equal.

## Generic cancellation theorem

The actual statement is

```lean
theorem QuasiCompact.of_comp_surjective {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [QuasiCompact (f ≫ g)] :
    QuasiCompact g
```

For an open compact `U ⊆ Z`, quasi-compactness of the composite makes
`f ⁻¹' (g ⁻¹' U)` compact. Continuity of `f` makes its image compact, and
surjectivity of `f` identifies that image with `g ⁻¹' U`. This is exactly the
compact-preimage obligation for `QuasiCompact g`.

The proof was checked against the actual mathlib class at
`AlgebraicGeometry/Morphisms/QuasiCompact.lean:41`: it requires compact
preimages of open compact subsets. `Scheme.Hom.comp_base`, `Set.preimage_comp`,
`IsCompact.image`, and `Set.image_preimage_eq _ f.surjective` give precisely
the identifications used. No openness, quasi-compactness, flatness, or
properness of `f` is required; no separatedness or additional assumption on
`g` is introduced. The theorem works over arbitrary schemes.

## Literal quotient application

`gluedQuotientS_quasiCompact` applies the generic theorem to the actual glued
quotient projection and structure map. Its first factor is surjective by the
previously checked raw quotient theorem. Their literal composite equals
`E.π`; the elliptic curve's proper structure map supplies quasi-compactness
of that composite. The cancellation direction is therefore correct.

`quotientS_quasiCompact` uses precisely `G.killN` and `G.killN_spec`, as do
the actual public quotient definitions. The marked-axis theorem supplies its
previously checked direct killing datum. The native level-3 example uses the
actual full-point pullback curve and its literal constant-axis subgroup.
No rank-implies-killing or sorried quotient elliptic-curve theorem is used.

## Named strict verification

The correctly named emission session 11788 closed with exit 0. The actual log
`/private/tmp/xyin-y0-quasi-compact.log` contains seven axiom checks, each with
exactly `propext`, `Classical.choice`, and `Quot.sound`, and no warnings/errors.
The identity-first-map cancellation sanity and actual native level-3 example
both pass.

The setup
`/private/tmp/xyin-y0-aintlib-work/YZeroCoarseQuasiCompact.setup.json` names
`AINTLIBDrafts.YZeroCoarseQuasiCompact`, sets `autoImplicit = false` and
`relaxedAutoImplicit = false`, and contains no plugins or dynamic libraries.
Canonical artifacts were independently checked: `.olean` 16736 bytes,
`.olean.private` 28072, `.olean.server` 3216, `.ilean` 13878, `.ir` 1456,
and `.ir.sig` 176. The environment remains pinned to AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.

## Boundary

The module proves quasi-compactness of the raw quotient's structure map.
Together with the previous universal-closedness result, this still does not
establish properness: separatedness and finite type remain separate
obligations. It proves neither finiteness of the quotient projection nor
smoothness or a local pointed Weierstrass presentation. There is no quotient
curve record, target `j`, or modular-polynomial assertion in the module.

## Fresh reuse delta and current receipt

The current retained source has **98 lines**, SHA-256
`3b288e6e58e9ca28bef611e9fd3e62f009a51758f2d80fcb2ed1091d5eddc9b8`.
Its only mathematical-body change is in `gluedQuotientS_quasiCompact`:
it installs the already proved actual structure-map universal-closedness,
then reuses mathlib's existing `UniversallyClosed` to `QuasiCompact` instance
(`Morphisms/UniversallyClosed.lean:163`). The literal structure-map statement
and chosen-killing/axis wrappers are preserved. The revised module exposition
accurately describes that reuse. The full 98-line source was independently
read and checked byte-equal to the isolated copy.

The generic cancellation theorem remains useful and unchanged: its input is
only quasi-compactness of the composite and surjectivity of the first map.
It therefore has weaker hypotheses than obtaining quasi-compactness via a
universally closed composite. Its independent compact-image proof and two
sanity checks remain valid.

Fresh named session **85088 closed with exit 0**. The actual new log
`/private/tmp/xyin-y0-quasi-compact-reuse.log` contains seven exact standard-three
axiom checks, both passing examples, and no diagnostics. Its SHA-256 is
`d656e802490fab6a23a40d812b0bec975b6eaf79c5ba77195bb9440b69d650d8`.
The current correctly named setup has both implicit options false, no plugins
or dynamic libraries, and SHA-256
`e92c8c840a7bac9805d757d0383ab505bed7509e51d93a27f07796c0a18fea62`.
All current artifact sizes and SHA values in
`/private/tmp/xyin-y0-quasi-compact-receipt.json` were independently checked:
`.olean` 16736 bytes, `.olean.private` 24432, `.olean.server` 3184,
`.ilean` 12968, `.ir` 1456, and `.ir.sig` 176.

**PASS for this new snapshot.** The earlier 11788 receipt is not presented as
verification of the modified source. The source still claims only the stated
quasi-compactness results; other independently checked quotient properties
are supplied by their own modules.
