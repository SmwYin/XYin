# SubgroupQuotientGeometry independent review

Review date: 2026-10-04. **Verdict: PASS for the retained source and named strict
receipt.** This review changed only this Markdown report. No Lean edits,
compiler invocations, environment changes, or usage resets were performed.

## Frozen source and retained delta

Retained source:
[YZeroCoarseSubgroupQuotientGeometry.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseSubgroupQuotientGeometry.lean).
It has 135 lines and SHA-256
`5f1810a5dbd2318367161746dc3c9252683dbe7cf1aa86a92881f946f543e334`.
The retained and isolated copies were independently checked byte-equal.

The final accepted temporary source had 110 lines and SHA-256
`4f3eef60f80abbe39b40c0808e25b2ecd1df0e43fc4d76087f999a66dc9d8d17`.
Its actual diff against the retained file consists only of the normal license
and module exposition. All seven declarations, two instantiation checks,
eleven axiom prints, imports, and proof bodies are unchanged.

The module imports `ModularCurves.GroupScheme.SubgroupQuotient` and the checked
`AINTLIBDrafts.YZeroCoarseConstantAxis`. It does not import `NIsogeny` or use the
sorried quotient elliptic-curve upgrade.

## Actual proof directions

Let `G` be a finite locally free subgroup of an actual elliptic curve `E/S`.
The explicit glued statements assume `N ≠ 0` and the genuine killing equation
`G.ι ≫ E.mulByHom N = G.π ≫ E.zero`. They need no field, characteristic-zero,
base-domain, or level-at-least-three hypothesis.

| Conclusion | Actual argument independently checked |
| --- | --- |
| `Flat (G.gluedQuotientπ N hkill)` | Check flatness on the actual source open cover. On each chart, the restricted map is the local flat quotient projection followed by an open immersion into the glued target. |
| `Surjective (G.gluedQuotientπ N hkill)` | Lift a target point into a glued quotient chart, lift its chart point through the local surjective quotient projection, then include the source point into `E.E`. |
| `UniversallyClosed (G.gluedQuotientS N hkill)` | The actual composite of quotient projection and structure map equals `E.π`, which is universally closed by properness of `E`. Universal closedness descends across the already proved surjective first map. |

The flatness proof uses `IsZariskiLocalAtSource.iff_of_openCover` with
`G.glueCover N hkill`. The actual cover maps are `(G.gluePatch ... i).U.ι`.
`ι_gluedQuotientπ` rewrites the restriction to the actual leg

```lean
G.localQuotientOpenπ (G.gluePatch N hkill i).hstable ≫
  G.gluedQuotientι N hkill i
```

The local freeness and flatness facts are explicitly obtained from
`G.free_gluePatch` and `AffineChartPatch.flat_and_surjective_localQuotientOpenπ`.
The second factor's open-immersion fact is explicitly obtained from the actual
`GlueData.ι_isOpenImmersion`. These local declarations fix typeclass lookup
through opaque chosen charts; they introduce no mathematical assumptions.

For surjectivity, the literal point equation extracted from the restriction
formula is

```text
q(Uᵢ.ι(x)) = gluedQuotientιᵢ(localQuotientOpenπᵢ(x)).
```

The local lifting equality rewrites the right-hand inner image to the chart
point `z`; transitivity with `gluedQuotientιᵢ(z) = y` gives the required image
`y`. The orientation is forward throughout.

`UniversallyClosed.of_comp_surjective` requires universal closedness of the
**composite** and surjectivity of its **first** factor. Both are supplied in
these directions. No universal-closedness premise about the quotient projection
itself is assumed.

The three public wrappers use exactly `G.killN` and `G.killN_spec`, matching the
literal definitions of `G.quotient`, `G.quotientπ`, and `G.quotientS`. They do not
identify quotient constructions made using unrelated chosen killing integers.
The marked-axis instantiation supplies the previously checked direct
`sectionAxisSubgroup_hasKillingInt`; the native level-3 example uses that same
checked killing datum. No generic rank-implies-killing shortcut is used.

Pinned source primitives independently checked:

- AINTLIB `SubgroupQuotientGlueData.lean:53`: actual chosen chart freeness;
  `:219`: actual source cover; `:233` and `:238`: target inclusion and leg.
- AINTLIB `SubgroupQuotientGlueData.lean:413` and `:418`: glued projection and
  its literal restriction formula; `:590` and `:594`: structure map and triangle.
- AINTLIB `SubgroupQuotientGlue.lean:487`: local flatness and surjectivity.
- AINTLIB `SubgroupQuotient.lean:51`, `:55`, and `:61`: public chosen-killing
  quotient, structure map, and projection.
- mathlib `AlgebraicGeometry/Gluing.lean:176` and `:180`: actual chart open
  immersions and joint surjectivity; `Morphisms/Basic.lean:281`: source-local iff.
- mathlib `Morphisms/UniversallyClosed.lean:74`: composite/surjective descent
  in the direction used above.

## Named strict receipt

Pins: AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, Lean `v4.35.0-rc3`.
Named artifact emission session 51407 closed with exit 0. The actual log
`/private/tmp/xyin-y0-subgroup-quotient-geometry-check.log` has eleven checks,
each with exactly `propext`, `Classical.choice`, and `Quot.sound`, and no
warnings/errors. The generic marked-axis check and actual native full-point
level-3 example both pass.

The actual setup names `AINTLIBDrafts.YZeroCoarseSubgroupQuotientGeometry`, sets
both implicit-variable options to `false`, and has no plugins or dynamic
libraries. Its SHA-256 is
`c77485b7df2de6e4a098ae428d7d89be7a0727ad57d2464348e0303d666479e0`.
The closed exit, literal compiler invocation, source hash, and artifact hashes
are saved in `/private/tmp/xyin-y0-subgroup-quotient-geometry-receipt.json`.

Canonical artifact sizes and all receipt hashes were independently checked:
`.olean` 19360 bytes, `.olean.private` 81088, `.olean.server` 4744,
`.ilean` 26188, `.ir` 1720, and `.ir.sig` 176.

The first, second, and third failed temporary logs are separately preserved as
`/private/tmp/YZeroSubgroupQuotientGeometryProbe-{first,second,third}.log`.
Their recovery-stage `sorryAx` outputs are excluded from the accepted receipt.
The final temporary strict run also closed exit 0 with eleven standard-three
prints. It did not request an output artifact; no temporary artifact is claimed.

## Exact mathematical boundary

This proves properties of the existing raw subgroup quotient: its projection
is flat and surjective, and its structure map is universally closed. It does
not prove the quotient projection finite, the structure map proper or smooth,
or the existence of a local pointed Weierstrass model. It constructs no
quotient elliptic-curve record, target `j`, cyclic-pair classification, or
modular-polynomial relation. The retained module's exposition states this
boundary accurately.
