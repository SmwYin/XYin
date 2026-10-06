# Actual subgroup quotient chart pullback: verification receipt

Retained module: `AINTLIBDrafts/YZeroCoarseSubgroupQuotientChartPullback.lean`.
It is 133 lines, maximum width 99, SHA256
`71e18b26c3eea713f11c1e86ce5c30d101788bf4c8b60752d08f5c9cc79fcec5`.
The retained and isolated sources have identical bytes. Compared with the approved
temporary 107-line source (`adbb042b621cb9026b1f5c6bcd83def52d8df6683c0d7d6e07febdede30feb6d`),
retention adds only the normal license and module documentation.

## Exact mathematical scope

For an elliptic curve `E` over any scheme `S`, an actual finite locally free
subgroup `G`, a nonzero `N`, and the explicit killing equation
`G.ι ≫ E.mulByHom N = G.π ≫ E.zero`, the actual glued quotient projection satisfies

```lean
G.gluedQuotientπ N hkill ⁻¹ᵁ (G.gluedQuotientι N hkill i).opensRange =
  (G.gluePatch N hkill i).U
```

The theorem `isPullback_localQuotientOpenπ_gluedQuotientπ` then proves the actual
square with top arrow the local quotient projection, left arrow the source patch
inclusion, right arrow the target quotient chart inclusion, and bottom arrow the
global quotient projection. There are no extra domain, noetherian, affine-base,
constant-group, or assumed Cartesian-square hypotheses.

The source-cover lift is given explicitly the canonical types of the actual
curve point and actual patch point. If the image lies in quotient chart `i`,
`Scheme.GlueData.ι_eq_iff` gives one original overlap witness from chart `j` to
chart `i`. Its **first** equation puts the local image in
`Pj.imageOpens (Uj ∩ Ui)`. The already proved `preimage_imageOpens` forces the
original point into `Uj ∩ Ui`, hence into `Ui`. The reverse inclusion is the
actual chart projection triangle. `IsOpenImmersion.isPullback` converts this
open preimage equality into the scheme-level pullback square.

The actual chart open-immersion wrapper is registered only as a local instance
within this file. It is the existing `Scheme.GlueData.ι_isOpenImmersion` term.
The level-3 sanity applies the square to the literal constant-axis subgroup of
the native marked curve pulled back from an actual full complex scheme point,
using its independent killing datum and the public construction's `killN`.

## Final named strict check

Named artifact emission session 32650 closed with exit code 0. It used the exact
Lean 4.35.0-rc3 binary and correct module name, with both `autoImplicit` and
`relaxedAutoImplicit` false. The final log
`/private/tmp/xyin-y0-subgroup-quotient-chart-pullback-check.log` contains exactly
8 axiom prints, every one with only `propext`, `Classical.choice`, and `Quot.sound`.
There are no errors or warnings. The actual level-3 sanity passes.

The full command, setup/source hashes, closed exit, and inspected correct-name
artifact hashes are in
`/private/tmp/xyin-y0-subgroup-quotient-chart-pullback-receipt.json`.
The `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir.sig`, and `.ir`
artifacts were checked on disk.

The temporary first and second failed logs are preserved separately:
`/private/tmp/YZeroSubgroupQuotientChartPullbackProbe-first.log` and
`/private/tmp/YZeroSubgroupQuotientChartPullbackProbe-second.log`.
They concern Set extensionality and opaque cover-index/coercion lookup, and are
excluded from the final receipt. The canonical typed lift fixes the latter;
the existing composition simp lemma then fires without an unused-argument warning.
No transparency option or linter disabling was introduced.

## Use and limitations

This supplies the previously missing actual target-chart identification for
target-local proofs such as finiteness. It does not itself prove the local or
global quotient projection finite or étale. Properness, smooth relative dimension
one, local Weierstrass presentations, quotient elliptic curve construction, and
target-j remain separate conclusions. No held `NIsogeny` geometry or general
smooth-precomposition theorem is used.
