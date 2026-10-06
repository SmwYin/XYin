# HopfEtale independent review

Review date: 2026-10-04. **Verdict: PASS for the retained source and named strict
receipt.** Only this report was edited by the reviewer; no Lean edits or
compiler invocations were added.

## Frozen source and delta

[YZeroCoarseHopfEtale.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseHopfEtale.lean)
has 84 lines and SHA-256
`59a6b4bee0d7490f93aa77a5ef0bfe15ff64ad84b3a58c2565036c55373da2b7`.
The accepted temporary source had 59 lines and SHA-256
`2e3d7413b244cf6496bd6844bdf93adf89915de5d08679ec02fde82db8c3c972`.
The actual retained delta contains only the license, module exposition, and
three docstrings. All three proofs, statements, imports, eight axiom prints,
and two sanity examples are unchanged. Retained and isolated sources were
independently checked byte-equal.

## Algebraic descent and scalar alignment

The generic theorem assumes the actual `IsHopfGalois ρ` record and
`Algebra.Etale R0 A`, and concludes `Algebra.Etale (coinvariants ρ) B`.
Base change makes `B ⊗[R0] A` étale over the **left** `B` factor. The inverse
of the retained `galoisEquivOverLeft h` transfers this étale algebra structure
to `B ⊗[coinvariants ρ] B`, with that same left-factor scalar ring.
The actual field `h.faithfullyFlat` supplies faithful flatness of `B` over
its coinvariants. Étale descent then gives the desired coinvariant inclusion.

The exact primitive `Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat`
is at mathlib `RingTheory/Etale/Descent.lean:78`. Its section variables require
only commutative rings, the stated algebra structures, and faithful flatness;
there is no Noetherian, domain, field, or finite-module premise. Here its
parameters are `R = coinvariants ρ`, `S = B`, and `T = B`. The base-change
and equivalence-transport primitives are at `RingTheory/Etale/Basic.lean:241`
and `:227`, respectively. Their directions match the actual proof.

## Actual chart hypotheses

`chartGroupRing_etale` explicitly assumes **`Etale G.π`**. The actual
`G.π.etale_appLE P.hV P.isAffineOpen_groupOpen le_rfl` gives étaleness of
the literal geometric map from `P.baseRing` to `P.groupRing`.
`RingHom.etale_algebraMap.mp` packages this as the corresponding algebra
property. This uses the actual affine base patch and actual group preimage
open, not a replacement algebra structure.

`chartCoinvariants_etale` retains both that group-projection hypothesis and
`Module.Free P.baseRing P.groupRing`, required by the existing actual chart
Hopf-Galois theorem. Its coaction remains literally `P.chartCoaction`.
No étaleness of the quotient or its coinvariant inclusion is assumed as an
input. Conversely, this file does not establish the additional
`Etale G.π` hypothesis for the constant axis.

## Named strict verification and boundary

Named artifact emission session 28333 closed exit 0. The actual log
`/private/tmp/xyin-y0-hopf-etale.log` contains eight exact standard-three
axiom checks and no diagnostics. The generic algebra-map étaleness sanity and
the actual chart specialization both pass.

The actual setup names `AINTLIBDrafts.YZeroCoarseHopfEtale`, sets both
implicit-variable options to `false`, and has no plugins or dynamic libraries.
Its SHA-256 is
`f5ce6f9588e67eb8668e4a90bc9c4b86e8f3b6f8e1815a0673647781b4e611df`.
The actual receipt `/private/tmp/xyin-y0-hopf-etale-receipt.json` preserves
the closed exit, source/setup hashes, exact checks, and artifact hashes.
All six canonical artifact sizes and hashes were independently checked:
`.olean` 25632 bytes, `.olean.private` 24776, `.olean.server` 3000,
`.ilean` 12691, `.ir` 2048, and `.ir.sig` 176.

The result is an étale coinvariant algebra extension and its honest chart
specialization under the explicit group-projection hypothesis. It does not
claim the constant axis étale, a global quotient projection étale, quotient
properness or smoothness, a pointed quotient Weierstrass model, or target `j`.
