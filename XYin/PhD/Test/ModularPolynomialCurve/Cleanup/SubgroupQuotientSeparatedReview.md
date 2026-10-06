# Actual quotient separatedness: independent review

Review date: 2026-10-04. **PASS for the frozen retained source and named strict
receipt.** The reviewer inspected the source, actual mathlib APIs, complete
log, setup, source copies, and artifact hashes. No Lean source was edited and
no compiler was started by this reviewer.

## Source and retained delta

[YZeroCoarseSubgroupQuotientSeparated.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseSubgroupQuotientSeparated.lean)
has 124 lines, SHA-256
`27502f8ec523a72c6b531501cbd3d6a729ed6cd25a91c3621a26dfee45d6083f`.
Retained and isolated copies are byte-equal. Independent comment/blank-line
removal gives the exact approved 99-line temporary program. The retention
delta adds license, module exposition, and declaration documentation; proof
bodies, hypotheses, examples, and checks are preserved.

## General descent theorem

The primary statement assumes only

```lean
[UniversallyClosed f] [Surjective f] [IsSeparated (f ≫ g)]
```

and concludes `IsSeparated g`. Finiteness of `f` is a separate corollary;
no Noetherian, finite-type, flatness, or étale hypothesis is needed.

The actual induced product map
`X ×[S] X ⟶ Y ×[S] Y` is universally closed by
`MorphismProperty.pullbackMap` with both factors `f`. The identity
`f ≫ diagonal g = diagonal (f ≫ g) ≫ productMap` is proved by the two
pullback projections. It has the same orientation as mathlib's
`pullback.comp_diagonal` (`Limits/Shapes/Diagonal.lean:290`).
Since the first diagonal is a closed immersion, the right-hand composite
is universally closed. `UniversallyClosed.of_comp_surjective` therefore
makes `diagonal g` universally closed. Surjectivity of the induced product
map is neither required nor assumed; surjectivity is used only for `f`
in that cancellation theorem.

Mathlib already proves that every scheme diagonal is an immersion
(`Morphisms/Immersion.lean:194`). Thus the diagonal is a preimmersion.
Its universally closed map has closed image, so
`IsClosedImmersion.of_isPreimmersion` (`ClosedImmersion.lean:61`) makes
it a closed immersion. This is precisely the `IsSeparated g` obligation.
The actual proof uses the existing nondeprecated `pullbackMap` API.

## Actual quotient application

The raw application installs the checked finite and surjective instances
for the literal glued quotient projection. Its composite with the literal
quotient structure map equals `E.π` by `gluedQuotientπ_gluedQuotientS`.
The original elliptic curve's separated structure morphism supplies the
composite hypothesis. The finite-surjective corollary then proves
separatedness of the actual quotient structure map.

The public wrapper uses the actual chosen `G.killN` and `G.killN_spec`.
The arbitrary `Spec R` axis wrapper supplies its checked direct killing
datum, and the complex level-3 example uses the actual full-point pullback
curve and its marked constant-axis subgroup. There is no hidden domain
assumption or target elliptic-curve structure in any conclusion.

## Actual named verification

Named emission session **35683 closed with exit 0**. The full actual log
`/private/tmp/xyin-y0-subgroup-quotient-separated.log` contains eight exact
standard-three axiom checks, no diagnostics, and no `sorryAx`.
Both identity-first-map descent and actual level-3 axis examples pass.
Log SHA-256 is
`8edb28a806868bad08de7a4aec46a20ed9d19a0a6a2c493d95e475360cc7a0f2`.

The actual setup names
`AINTLIBDrafts.YZeroCoarseSubgroupQuotientSeparated`, sets `autoImplicit`
and `relaxedAutoImplicit` to false, and has no plugins or dynamic libraries.
Its SHA-256 is
`49eef79298b15487bbcbd37e3fd9d402f51f3083de1cb7d0d24b8a0f4d7dfac7`.
Every artifact size and SHA in
`/private/tmp/xyin-y0-subgroup-quotient-separated-receipt.json` was
independently checked on disk: `.olean` 18424 bytes,
`.olean.private` 50272, `.olean.server` 3824, `.ilean` 17852,
`.ir` 1912, and `.ir.sig` 176.

## Boundary and axiom risk

This leaf proves separatedness of the raw quotient over its original base.
Together with the separate universal-closedness and quasi-compactness leaves,
it advances the properness obligations, but this leaf does not prove finite
type or properness. It asserts no LFP or smooth descent, relative dimension,
Weierstrass model, quotient elliptic curve record, target `j`, or modular
polynomial relation. In particular, it does not invoke the sorried
`SmoothDescent` finite-presentation or smoothness gates.

The pins remain AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`,
mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
