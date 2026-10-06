# Formally étale differential stalk ranks: verification receipt

Retained module: `AINTLIBDrafts/YZeroCoarseKaehlerRank.lean`.
The retained and isolated source bytes are identical: 80 lines, maximum width 84,
SHA256 `b7c17ca009d3070f04e96b5ef38317178a560bc01e3d78c8830d4b703ac6081c`.
Retention only adds the standard license and module documentation to the approved
55-line finite-flat fixture. The mathematical suffix, both declarations, all
seven axiom prints, and all three examples are byte-preserved.

## Mathematical scope and generality

For a commutative-ring scalar tower `R → A → B`, the primary theorem
`ModularPolynomialCurveTest.AINTLIB.RelativeDimension.kaehler_rankAtStalk_eq_of_formallyEtale`
requires exactly `[Module.Finite A Ω[A⁄R]]`, `[Module.Flat A Ω[A⁄R]]`, and
`[Algebra.FormallyEtale A B]`. At a prime `P` of `B`, it identifies the stalk rank
of `Ω[B⁄R]` with that of `Ω[A⁄R]` at `P.comap (algebraMap A B)`.

The proof is the literal composition of mathlib's
`KaehlerDifferential.isBaseChange_of_formallyEtale` and
`Module.rankAtStalk_isBaseChange`. The latter's inherited finite and flat module
hypotheses are the exact boundary chosen for the primary statement. Neither a
global standard smooth presentation nor a source-relative-dimension assumption
enters the proof.

The separate `kaehler_rankAtStalk_eq_of_smooth_formallyEtale` corollary replaces
the two module hypotheses with `[Algebra.Smooth R A]`. Existing instances provide
finite differentials and projective differentials, hence flat differentials.
There is no added Noetherian, domain, nontriviality, finite-extension,
surjectivity, or `B`-smoothness hypothesis. The primary statement can be used
outside the smooth-algebra setting whenever its exact module hypotheses hold.

## Strict named verification

The correct-name direct artifact emission closed as session 84303 with exit code
0. It used the exact pinned Lean 4.35.0-rc3 binary, setup name
`AINTLIBDrafts.YZeroCoarseKaehlerRank`, `autoImplicit=false`, and
`relaxedAutoImplicit=false`. The setup has 9425 import entries and SHA256
`18772ec8d97853a924f1ca49d81051119ca8c2b2dad96ed3d4a24da0632bf7aa`.

The final log `/private/tmp/xyin-y0-kaehler-rank-check.log`, SHA256
`feb36e143133c7d0e4adcd076b67fc1d848b67d982e6d9ebd4cd957b1f2e79f9`,
contains exactly seven axiom prints. Both own declarations and all five selected
mathlib primitives depend only on `propext`, `Classical.choice`, and `Quot.sound`.
There are no errors or warnings. All three examples pass: the exact finite-flat
statement, the smooth identity map, and the smooth prime-comap interface.

The correct-name `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir.sig`,
and `.ir` artifacts were inspected under the isolated
`.lake/build/lib/lean/AINTLIBDrafts/` directory. Their sizes are respectively
21976, 11232, 2896, 7073, 176, and 2008 bytes. The exact command, closed exit,
source/setup/log hashes, full primitive list, and all six artifact hashes are in
`/private/tmp/xyin-y0-kaehler-rank-receipt.json`.

The original 40-line smooth-only fixture and the approved 55-line finite-flat
fixture remain unchanged, with source hashes respectively
`9f6146a66667e189bfa9711f036a7bf697d8cb15a68c1a261e0d358f21bca977` and
`68b2fb46a3215197b72b2c3fcb8c38bfe8871fafbea8a217fba34a9bde08cf8f`.
They are not imported by the retained module. Neither fixture needed a failed
proof-repair run.

## Source-backed next adapter, not implemented here

To turn an existing `RingHom.Locally (IsStandardSmoothOfRelativeDimension n)`
condition into a stalk-rank formula, use its defining unit-span localization
cover (`RingHom/Locally.lean:60`). At a given prime `P`, choose a cover element
`t ∉ P`; the unit-span property rules out all cover elements lying in `P`.
`PrimeSpectrum.localization_away_comap_range` (`Spectrum/Prime/Topology.lean:587`)
provides a prime of `Localization.Away t` above `P`.

The local condition supplies the actual standard-relative-dimension statement
on that localization, after the canonical scalar-tower composition equality.
A separately supervised global-standard-at-prime rank helper can give rank
`n` there. The retained formally étale rank comparison then transports it back
to the original prime. Localization is formally étale; an already available
smooth algebra can supply the finite-flat differential hypotheses through the
convenience corollary. The localization's lifted prime also supplies the
nontriviality needed by standard-smooth global-rank formulas.

This is an implementation outline only. The local-standard-to-rank adapter,
the converse smooth-plus-rank adapter, relative-dimension descent, scheme
cotangent/rank interfaces, and quotient elliptic curve upgrades remain outside
this module's proved scope. No held `NIsogeny` or smooth-descent theorem is used.
