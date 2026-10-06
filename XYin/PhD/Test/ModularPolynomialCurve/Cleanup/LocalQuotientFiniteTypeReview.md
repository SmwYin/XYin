# Actual local quotient finite type: independent review

Review date: 2026-10-04. **PASS for the frozen retained source and named strict
receipt.** The reviewer read the exact Artin--Tate API, geometric scalar
instances, source/retention deltas, full log, setup, and artifact hashes.
No Lean source was edited and no compiler was started by this reviewer.

## Frozen source and exact delta

[YZeroCoarseLocalQuotientFiniteType.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseLocalQuotientFiniteType.lean)
has 137 lines, SHA-256
`323e93e57d5bb8d95c350879aeedf039d40235d927c7904f3beaa8e9fa558022`.
Retained and isolated copies are byte-equal. Apart from header/module docs,
the complete program differs from the green 108-line source probe only by
replacing the chart signature `#check` with an unconditional actual-patch
example and removing the raw-quotient signature `#check`. All theorem
statements, proofs, scalar definitions, and eleven axiom prints are unchanged.

## Actual source finite type and Artin--Tate

The general subalgebra wrapper uses the exact root theorem
`fg_of_fg_of_fg` (`Mathlib/RingTheory/Adjoin/Tower.lean:144`). Its Noetherian
base, ambient finite-type algebra, finite extension, and injective subtype
inputs match `Algebra.FiniteType.out`, `Module.Finite.fg_top`, and
`Subtype.val_injective`. No domain assumption is needed.

For an actual patch, `chartRing_finiteType` derives smoothness of `E.π`
from the actual elliptic curve record. `E.π.finiteType_appLE P.hV P.hU
P.hover` then proves finite type for exactly the scalar map defining
`Algebra P.baseRing P.chartRing` in `StableCharts.lean:120`.
There is no assumed chart-ring finite-type hypothesis in this actual API.

The coinvariant result installs that derived finite type and the checked
`chartCoinvariants_finite` extension. Artin--Tate applies to the canonical
subalgebra tower. The actual quotient results therefore require only the
existing free group-patch condition and Noetherian base-patch ring.
The product `ℂ × ℂ` sanity check confirms the intended non-domain scope.

## Literal raw quotient scalars

The actual quotient ring begins as a `Subring`. `quotientBaseHom` uses
`codRestrict` of the existing geometric `algebraMap`, with its image condition
proved by the literal `quotientRing_eq_coinvariants` and
`coinvariants.algebraMap_mem`. Its subtype-composition theorem equals the
actual `(E.π.appLE P.V P.U P.hover).hom`, elementwise by `rfl`.

The local `let Algebra := quotientBaseHom.toAlgebra` explicitly fixes raw
quotient scalars. The existing subring congruence and `coinvSubringEquiv`
become an algebra equivalence with an actual `commutes'` proof; its inverse
correctly transfers finite type from coinvariants to the raw quotient ring.
The ring-hom theorem is for that exact `quotientBaseHom`. No broad global
algebra instance or unproved scheme-alignment record is installed.

For later geometric application, a locally Noetherian base supplies the
Noetherian ring condition via
`IsLocallyNoetherian.component_noetherian ⟨P.V, P.hV⟩`. This fact is separate
from the need to identify the actual descended chart structure morphism with
the `Spec` map of `quotientBaseHom`; that scheme-level triangle is not asserted
in this leaf.

## Named strict receipt

Named emission **58951 closed with exit 0**. The actual log
`/private/tmp/xyin-y0-local-quotient-finite-type-check.log` contains eleven
exact standard-three axiom checks, no diagnostics or `sorryAx`, and three
passing examples: unconditional actual chart finite type, the non-domain
product-base Artin--Tate fixture, and actual raw scalar-map finite type.
Log SHA-256 is
`37e92a892bf4f4e7c6cbf349771649ab1c528420176df01e6d6383ad418eb0aa`.

The actual correctly named setup has both implicit options false, no plugins
or dynamic libraries, and SHA-256
`80ebc92fecfb8d9acc0d69cbfd01e61883ed29eb91049a4545d9ef39de09f6dc`.
Every recorded artifact size and SHA in
`/private/tmp/xyin-y0-local-quotient-finite-type-receipt.json` was independently
checked: `.olean` 94400 bytes, `.olean.private` 32240,
`.olean.server` 5392, `.ilean` 26922, `.ir` 1784, `.ir.sig` 176.

The first 97-line probe's unknown-name recovery output and its mid-cumulative
unavailable-dependency emission are excluded. The later clean temporary
emission and strengthened source probe have separate receipts; they are not
substituted for this correctly named verification.

## Boundary

This is finite type of actual local algebras and their literal scalar ring
homomorphisms. It claims no global quotient finite type, LFP, properness,
smoothness, quotient elliptic curve structure, or target `j`.
No sorried `SmoothDescent` finite-presentation gate is used. Once actual
scheme-level finite type is established over a locally Noetherian base,
mathlib's existing clean Noetherian finite-type-to-LFP instance can be used
separately.
