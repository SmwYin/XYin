# Actual chart smoothness: independent review

Review date: 2026-10-04. **PASS for the current 132-line retained source and its
named strict receipt, reviewed below.** The original 87-line review is preserved
as historical evidence. This reviewer read the source, exact descent theorem, complete log,
setup, source copies, and artifact sizes. No Lean source was edited and no
compiler was started by this reviewer.

## Historical 87-line source and retention

[YZeroCoarseHopfSmooth.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseHopfSmooth.lean)
originally had 87 lines, SHA-256
`8c0fb1f43cc7841b80018b8e146061a213fbf6288f4a19ce1aa3263cd9491e2b`.
The then-current isolated and retained copies were byte-equal. Independent comment removal
restores the entire accepted 63-line temporary program byte-for-byte modulo
blank lines; only normal header and scope documentation were added.

## Proof and hypotheses

`chartRing_smooth` has no assumed chart-ring smoothness. It derives `Smooth
E.π` from the actual elliptic curve record's relative-dimension-one field,
then uses `E.π.smooth_appLE P.hV P.hU P.hover`. This is the exact geometric
scalar map used by the existing `Algebra P.baseRing P.chartRing` instance.
`RingHom.smooth_algebraMap` changes only the presentation of that same claim.

For coinvariants, the canonical subalgebra tower supplies all three compatible
algebra structures. The proof uses the checked finite inclusion, checked
étale inclusion (with explicit `[Etale G.π]`), and the actual
`P.isHopfGalois_chartCoaction.faithfullyFlat` field. The clean theorem
`Algebra.smooth_of_etale_faithfullyFlat` in
`ForMathlib/EtaleSmoothDescent.lean:88` then descends smoothness over the
explicit Noetherian base-patch ring.

The actual descent proof has three independent ingredients: Artin--Tate gives
finite presentation over the Noetherian base, projectivity of relative
differentials descends, and the cotangent `H1` obstruction vanishes under
étale faithfully flat descent. Its printed primitives and both own theorem
checks contain no `sorryAx`. This is the clean algebraic `EtaleSmoothDescent`
route, distinct from the excluded sorried `SmoothDescent` LFP/smooth gates.
No field or domain hypothesis is added. Existing patch freeness and subgroup
étaleness are explicit inputs to the coinvariant result.

## Historical named receipt

Named emission **46480 closed with exit 0**. The full actual log
`/private/tmp/xyin-y0-hopf-smooth-before-raw.log` contains 15 allowed-axiom checks:
14 have exactly `propext`, `Classical.choice`, and `Quot.sound`; the canonical
`Subalgebra.isScalarTower_mid` uses only `propext` and `Quot.sound`.
There are two passing ring-hom sanity examples, no own warnings/errors,
and no `sorryAx`.

The actual setup `/private/tmp/YZeroCoarseHopfSmooth.setup.json` names
`AINTLIBDrafts.YZeroCoarseHopfSmooth`, has both implicit options false, and
has no plugins or dynamic libraries. Every recorded artifact size in
the historical `/private/tmp/YZeroCoarseHopfSmooth-before-raw-receipt.json`
was checked on disk at that snapshot:
`.olean` 16048 bytes, `.olean.private` 24800, `.olean.server` 2640,
`.ilean` 13547, `.ir` 1840, `.ir.sig` 176, and `.c` 3988. The receipt
records sizes rather than artifact SHA values; no missing SHA comparisons
are claimed.

The separate existing-dependency receipt records 11 warnings for
`StandardEtaleH1`, 5 for `EtaleH1Descent`, and 29 for `EtaleSmoothDescent`,
with zero errors and a successful dependency build. These are explicitly
separate from the warning-free retained leaf; no pinned upstream source
was edited to hide them.

## Boundary

The conclusions concern actual chart and coinvariant **algebras**. The actual
quotient scheme's structure map additionally requires the literal raw-ring
scalar alignment and geometric factorization triangle. No global quotient
smoothness or relative dimension is asserted in this leaf.

The cotangent `H1` obstruction above is not coherent sheaf
`H¹(O_C)` or `H¹(O_C([0]))`. Its vanishing provides no genus-one or
pointed Weierstrass model by itself. A quotient elliptic curve record,
target `j`, and modular polynomial comparison remain separate goals.

## Current 132-line raw-ring extension

The retained source now has 132 lines, SHA-256
`89803a6654740134a57bab10ed17990141e35c88b7d40ffdec6f4b5fdf405bfd`.
The reviewer independently verified that retained and isolated copies are equal,
that the original 87-line namespace tail is preserved byte-for-byte, and that
the accepted 49-line raw-smooth probe's namespace body, checks, and examples
were appended byte-for-byte. The remaining changes are the frozen local
finite-type import, namespace opening, and scope documentation.

The two additional declarations concern the literal raw equalizer subring.
`quotientRing_smooth` explicitly uses
`(P.quotientBaseHom).toAlgebra`, obtains canonical coinvariant smoothness from
`chartCoinvariants_smooth`, and applies `Algebra.Smooth.of_equiv` to
`quotientCoinvariantsAlgEquiv P` in the inverse direction. The equivalence is
over the same base-patch ring, so the scalar structure is preserved.
`quotientBaseHom_smooth` converts that algebra property to the smoothness of
the actual scalar ring homomorphism using `RingHom.smooth_algebraMap`.
The hypotheses remain patch freeness, explicit subgroup projection étaleness,
and a Noetherian base-patch ring; there is no assumed chart smoothness.

Named emission **67229 closed with exit 0**. The current full log
`/private/tmp/xyin-y0-hopf-smooth.log` has exactly 24 checks: 23 use the standard
three axioms, and `Subalgebra.isScalarTower_mid` uses exactly `propext` and
`Quot.sound`. All four sanity examples pass, with zero own diagnostics and
no `sorryAx`. The current setup has the correct
`AINTLIBDrafts.YZeroCoarseHopfSmooth` module name, both implicit options false,
and empty plugin and dynamic-library lists.

The reviewer checked all seven current artifact sizes recorded by
`/private/tmp/YZeroCoarseHopfSmooth-receipt.json`: `.olean` 30344,
`.olean.private` 31656, `.olean.server` 3640, `.ilean` 21603, `.ir` 1976,
`.ir.sig` 176, and `.c` 4563 bytes. This receipt records sizes; no artifact
SHA comparison is claimed. The historical snapshot and its separate receipt
remain available under the `before-raw` paths.

This extension proves the actual raw quotient's **algebra** smoothness for its
fixed scalar map. Passing to the actual quotient scheme structure map still
uses the separately proved geometric factorization triangle and local
gluing. Relative dimension one and a pointed Weierstrass model are further
claims, not conclusions of these four algebra declarations.
