# LocalQuotientGeometry independent review

Review date: 2026-10-04. **Verdict: PASS for the retained source and named strict
receipt.** Only this Markdown report was edited; no Lean source or compiler run
was changed by the reviewer.

[YZeroCoarseLocalQuotientGeometry.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseLocalQuotientGeometry.lean)
has 97 lines and SHA-256
`b35a853f68fb75b26361e689f236734f972ec2da52959a40e199a4269423b7e8`.
The accepted temporary source had 72 lines and SHA-256
`ac040bf15ac103eb7ecc473517c89d4a4f816b1782c3da1ce0f2845f3827fe71`.
The actual retained diff is only the license, module exposition, and four
docstrings. All four statements/proofs, thirteen checks, imports, and two
examples are unchanged. Retained and isolated sources were independently
checked byte-equal.

For an actual free affine patch `P`, `quotientRing_subtype_finite` uses the
existing literal equality

```lean
G.quotientRing P.hstable = (coinvariants P.chartCoaction).toSubring
```

from pinned `SubgroupQuotientGlue.lean:387`. After rewriting, the subtype
inclusion is the canonical coinvariant algebra map. The retained chart-module
finiteness theorem therefore proves that exact ring map finite.

The actual local quotient projection at `SubgroupQuotientGlue.lean:109` is

```lean
P.U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (G.quotientRing P.hstable).subtype)
```

`P.isIso_toSpecΓ_U` is the genuine affine-chart isomorphism, obtained from
`P.hU` in `StableCharts.lean:188`. Its first map is finite; `IsFinite.SpecMap_iff`
at mathlib `Morphisms/Finite.lean:74` gives finiteness of the second map from
the proved ring-map statement. Explicit composition then gives finiteness
of the literal local quotient projection.

The two étale declarations repeat this actual map identification with
étaleness. They explicitly retain `[Etale G.π]`, used by the checked chart
coinvariant étale theorem. The first factor is again an isomorphism, while
`HasRingHomProperty.Spec_iff` transfers the canonical subtype's étaleness to
the second factor. Composition is in the same forward morphism direction.

The two finite declarations precede the `variable [Etale G.π]` command and
their proof bodies are unchanged from the earlier finite-only fixture. Thus
that extra hypothesis is not silently added to the finite statements.
All four declarations retain the actual patch freeness prerequisite
`Module.Free P.baseRing P.groupRing`, with no field, Noetherian, or domain
assumption and no replacement coaction or algebra instance.

Named emission session 10853 closed exit 0. The actual log
`/private/tmp/xyin-y0-local-quotient-geometry.log` has thirteen exact
standard-three axiom prints, no diagnostics, and both actual patch-map
sanity examples pass. The setup names
`AINTLIBDrafts.YZeroCoarseLocalQuotientGeometry`, sets both implicit-variable
options to `false`, and has no plugins or dynamic libraries. Canonical sizes
were independently checked: `.olean` 24056 bytes, `.olean.private` 41512,
`.olean.server` 3440, `.ilean` 16769, `.ir` 2288, and `.ir.sig` 176.

The earlier finite-only attempts failed in composition lookup/transparency;
their outputs are excluded. The exact finite-only final 90537 closed exit 0
with eight standard-three checks. The combined temporary run 87472 closed
exit 0 on its first étale elaboration with thirteen standard-three checks
and no diagnostics.

This leaf proves properties of **actual local quotient maps**. Global finite
transport must use the separately checked target-chart pullback and target
open cover; finiteness is not source-local. The module itself claims no
global quotient finiteness or étaleness, quotient properness/smoothness,
pointed Weierstrass model, target `j`, or modular-polynomial equation.
