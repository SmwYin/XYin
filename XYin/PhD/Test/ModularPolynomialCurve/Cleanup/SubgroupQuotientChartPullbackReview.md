# SubgroupQuotientChartPullback independent review

Review date: 2026-10-04. **Verdict: PASS for the retained source and named strict
receipt.** This reviewer made no Lean edits or compiler invocations; only this
Markdown report was written.

## Frozen source and delta

[YZeroCoarseSubgroupQuotientChartPullback.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseSubgroupQuotientChartPullback.lean)
has 133 lines and SHA-256
`71e18b26c3eea713f11c1e86ce5c30d101788bf4c8b60752d08f5c9cc79fcec5`.
The accepted temporary source had 107 lines and SHA-256
`adbb042b621cb9026b1f5c6bcd83def52d8df6683c0d7d6e07febdede30feb6d`.
The actual retained diff contains only the license and module exposition.
Statements, local instance, proofs, checks, and native level-3 sanity are
unchanged. Retained and isolated copies were independently checked byte-equal.

## Actual open preimage equality

For the actual glued quotient `q`, its chart inclusion `ιᵢ`, and corresponding
stable source patch `Uᵢ`, the first theorem proves

```lean
G.gluedQuotientπ N hkill ⁻¹ᵁ (G.gluedQuotientι N hkill i).opensRange =
  (G.gluePatch N hkill i).U
```

Its input is an elliptic curve over an arbitrary scheme, a finite locally free
subgroup, a nonzero integer `N`, and the actual killing equation. It introduces
no field, Noetherian, characteristic-zero, rank, or quotient-geometry hypothesis.
The local chart open-immersion instance is obtained from the actual gluing data
and stays local to the file.

For the forward inclusion, start with `q(x) = ιᵢ(z)`. The genuine source cover
supplies a patch `j` and point `u` with `Uⱼ.ι(u) = x`. The literal local-to-global
triangle gives, with `b = localπⱼ(u)`,

```text
ιⱼ(b) = q(Uⱼ.ι(u)) = q(x) = ιᵢ(z).
```

The exact `Scheme.GlueData.ι_eq_iff j i b z` yields an overlap point `v`.
Its **first** equation is `fⱼᵢ(v) = b`; in the actual quotient gluing data,
`fⱼᵢ` is the inclusion of `Pⱼ.imageOpens(Uⱼ ∩ Uᵢ)`. Thus `b` lies in that
image open. `Pⱼ.preimage_imageOpens` identifies its complete local-projection
preimage with the stable window `Uⱼ ∩ Uᵢ`. Hence `Uⱼ.ι(u)` belongs to the
intersection, and its second membership component gives `x ∈ Uᵢ`.

This argument uses an actual single overlap witness supplied by mathlib's
gluing equivalence. It does not invent a transition identification, assume a
pullback square, or use an unproved orbit/closure argument. The explicit
`G.free_gluePatch N hkill j` supplies the existing freeness input for saturation.
The canonical typed `j/u` witnesses and explicit set coercions only repair
elaboration through the chosen source cover.

For the reverse inclusion, represent `x ∈ Uᵢ` by `u` in the actual open scheme.
The same literal projection triangle makes `q(x)` the image under `ιᵢ` of
`localπᵢ(u)`. This proves precisely the required range membership, in the
forward morphism direction.

## Actual pullback square

The second theorem concludes

```lean
IsPullback (G.localQuotientOpenπ (G.gluePatch N hkill i).hstable)
  (G.gluePatch N hkill i).U.ι (G.gluedQuotientι N hkill i)
  (G.gluedQuotientπ N hkill)
```

Mathlib `AlgebraicGeometry/OpenImmersion.lean:757` requires the two vertical
open immersions, the equation `Uᵢ.ι ≫ q = localπᵢ ≫ ιᵢ`, and equality of
their corresponding open ranges under pullback. These are exactly the actual
chart inclusions, the existing projection triangle, and the first theorem.
The ordering of all four arrows matches the genuine square.

The primitive contracts were checked directly in pinned sources:
`AlgebraicGeometry/Gluing.lean:245` supplies the overlap relation;
AINTLIB `SubgroupQuotientGlueData.lean:110` defines its quotient chart overlap
inclusions; `SubgroupQuotientGlue.lean:761` supplies saturation; and
`SubgroupQuotientGlueData.lean:418` supplies the projection restriction formula.

## Named strict verification and boundary

Named artifact emission session 32650 closed exit 0. The actual log
`/private/tmp/xyin-y0-subgroup-quotient-chart-pullback-check.log` contains eight
exact standard-three axiom prints, no diagnostics, and the actual native
full-point constant-axis sanity at level 3 passes.

The actual setup names `AINTLIBDrafts.YZeroCoarseSubgroupQuotientChartPullback`,
sets both implicit-variable options to `false`, and has no plugins or dynamic
libraries. Its independently checked SHA-256 is
`eb71cd9281af6184ba2c7fef7fdbd9bf96d6f488d936349fb0280672d3795fd1`.
The literal invocation, closed exit, and source/setup/artifact hashes are
preserved in
`/private/tmp/xyin-y0-subgroup-quotient-chart-pullback-receipt.json`.
All six canonical artifact sizes and hashes were independently verified:
`.olean` 31176 bytes, `.olean.private` 128520, `.olean.server` 3128,
`.ilean` 27882, `.ir` 1456, and `.ir.sig` 176.

The first and second failed temporary logs are preserved separately and their
recovery-stage `sorryAx` prints are excluded. The final third temporary run
9532 closed exit 0 with eight standard-three checks and no diagnostics.
The repair adds ordinary set extensionality, canonical cover witness types,
and explicit membership coercions; it uses no transparency setting or linter
disable. No temporary emitted artifact is claimed.

The result identifies the actual local quotient projection as the target-chart
pullback of the actual global projection. This is the needed seam for subsequent
target-local checks, including finiteness. The module itself claims no global
finiteness or étaleness, quotient curve upgrade, pointed Weierstrass model,
target `j`, or modular-polynomial equation.
