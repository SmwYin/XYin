# Hopf–Galois étale descent

`coinvariants_etale` proves `Algebra.Etale (coinvariants ρ) B` from the existing
`IsHopfGalois ρ` and `Algebra.Etale R0 A`. Base change gives étaleness of
`B ⊗[R0] A` over its left B factor. The exact left B-algebra equivalence in
`YZeroCoarseHopfGaloisLeft` transfers this to `B ⊗[coinvariants ρ] B`.
The actual field `h.faithfullyFlat` then supplies mathlib's faithfully flat
étale descent. No finite-module, domain, or Noetherian assumption is used.

`chartGroupRing_etale` uses the explicit hypothesis `Etale G.π` and the actual
`appLE` map on the affine base patch and its full group preimage. This is the
same algebra structure as `P.groupRing`. `chartCoinvariants_etale` combines
that result with the actual free-patch Hopf–Galois theorem. The geometric
group-projection hypothesis remains explicit. This leaf does not prove
étaleness of a constant axis or of the global quotient projection.

The generic RingHom example and actual-patch example check the two interfaces.
The retained leaf is 84 lines, SHA-256
`59a6b4bee0d7490f93aa77a5ef0bfe15ff64ad84b3a58c2565036c55373da2b7`.
Correct-module strict compilation closed session 28333 with exit 0, eight
exact standard-three-axiom checks, two examples, and no diagnostics.
The retained/build copies are byte-identical and six named Lean artifacts exist.
The log and detailed source/setup/artifact receipt are
`/private/tmp/xyin-y0-hopf-etale.log` and
`/private/tmp/xyin-y0-hopf-etale-receipt.json`. This is an individual leaf receipt;
the next cumulative gate must include the leaf. Independent review is saved in
`../Cleanup/HopfEtaleReview.md`.

The isolated environment uses Lean `v4.35.0-rc3`, AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, and mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`. Both implicit flags are false.
XYin's toolchain is unchanged. The parent README supplies the retained-bridge
reproduction driver.
