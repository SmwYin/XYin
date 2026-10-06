# Actual quotient finite type and properness: independent review

Review date: 2026-10-04. **PASS for the frozen retained source and named strict
receipt.** The reviewer read the entire temporary and retained programs,
relevant mathlib APIs, complete actual output, setup, and recorded artifacts.
No Lean source was edited or compiler started for this review.

## Source and retention delta

[YZeroCoarseSubgroupQuotientFiniteType.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseSubgroupQuotientFiniteType.lean)
has 218 lines and SHA-256
`f60f224d08800a83f55af35b8faf37a80cc2b5614a1354b72051e4568b38e2c3`.
The retained and isolated copies are byte-equal. Removing comments, relocated
axiom-print lines, and blank lines restores exactly the approved 189-line
temporary program. Proof signatures, mathematical bodies, and both examples
are unchanged.

## Mathematical and scalar alignment

`quotientToBase` is literally the spectrum map of `P.quotientBaseHom`, followed
by the actual affine base patch's spectrum isomorphism. The projection
triangle uses the proved subtype composition formula and the existing
`appLE` naturality theorem. The contravariant spectrum composition order is
correct; no auxiliary chosen morphism is assumed.

`gluedQuotientι_gluedQuotientS` proves that the actual quotient structure map
restricts to this local scalar morphism followed by the base open immersion.
Its cancellation is through the actual local quotient projection's proved
epimorphism property, and its two triangles are the literal upstream gluing
and structure-map triangles.

Local finite type comes from the checked Artin--Tate result for the literal
scalar ring homomorphism. Global local finite type uses the **quotient chart
cover as a source cover** of the quotient structure map. The required patch
freeness comes from `free_gluePatch`; patch-base Noetherianity comes from
`IsLocallyNoetherian.component_noetherian`. The locally Noetherian base is an
explicit hypothesis, not a domain or field assumption. Supplying the existing
ring-property source-locality instance locally repairs typeclass inference
without changing mathematical hypotheses.

Local finite presentation uses the clean mathlib Noetherian instance
(`AlgebraicGeometry/Noetherian.lean:263`), requiring a locally Noetherian target
and a locally finite type map. Properness combines the already checked actual
separatedness, universal closedness, and local finite type, exactly as in the
mathlib `IsProper` record (`Morphisms/Proper.lean:42`). Neither step uses the
excluded sorried `SmoothDescent` gates.

The public wrappers specialize the same actual gluing construction to
`G.killN` and `G.killN_spec`. The marked-axis wrapper installs its independently
proved killing instance; the level-3 complex example uses the literal axis
of an actual full complex point.

## Named strict receipt

Emission **90232 closed with exit 0**. The complete actual log
`/private/tmp/xyin-y0-subgroup-quotient-finite-type.log` contains exactly 13
standard-three axiom checks, zero own diagnostics, and no `sorryAx`. Both API
examples pass. Its SHA-256 is
`aabaf909e43263d05c95e245ce8bb2e0fe3063091a20ad20a343b0dbdbd0c3ed`.

The actual setup names `AINTLIBDrafts.YZeroCoarseSubgroupQuotientFiniteType`,
has both implicit options false, and has empty plugins and dynamic-library
lists. Its hash is
`532d234b2f3415c8c48d55a452864b21818645bd480b7257c46310241a31b2d9`.
All six artifact sizes **and SHA-256 values** in
`/private/tmp/xyin-y0-subgroup-quotient-finite-type-receipt.json` were checked
on disk: `.olean` 41216, `.olean.private` 84616, `.olean.server` 6448,
`.ilean` 50605, `.ir` 1864, and `.ir.sig` 176 bytes.

## Boundary

The actual raw quotient is proper and locally of finite presentation over
a locally Noetherian base. That base restriction is this proof route's scope;
it is not asserted necessary for the mathematical quotient. Subgroup
projection étaleness is not required by this leaf. Smoothness, relative
dimension one, genus one, a pointed Weierstrass presentation, target `j`, and
the modular polynomial comparison require their own proofs.
