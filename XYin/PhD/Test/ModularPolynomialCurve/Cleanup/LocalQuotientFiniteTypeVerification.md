# Actual local quotient finite-type algebra: verification receipt

Retained module: `AINTLIBDrafts/YZeroCoarseLocalQuotientFiniteType.lean`.
It is 137 lines, maximum width 99, SHA256
`323e93e57d5bb8d95c350879aeedf039d40235d927c7904f3beaa8e9fa558022`.
The retained and isolated source bytes are identical. Retention adds the standard
license/module documentation, removes two diagnostic `#check` commands, and
replaces the source-chart signature check with an unconditional actual-patch
example. All proof bodies and scalar definitions are preserved from the approved
108-line source-backed fixture (`a99c6fc92bf6cd5c04e21873a4ca625a2f27db358a2ee81f2007c75f4924f37d`).

## Exact mathematical scope

For an actual affine chart patch `P` of a finite locally free subgroup of a given
elliptic curve, `chartRing_finiteType` proves
`Algebra.FiniteType P.baseRing P.chartRing` with no extra hypotheses. Its existing
algebra structure is the actual `(E.π.appLE P.V P.U P.hover).hom.toAlgebra`.
The elliptic curve's smooth structure gives local finite type of `E.π`, and
`finiteType_appLE` with the actual affine base/chart witnesses gives the required
finite-type algebra-map assertion.

Under `[Module.Free P.baseRing P.groupRing]` and
`[IsNoetherianRing P.baseRing]`, `chartCoinvariants_finiteType` proves finite type
of the literal chart coinvariants over this base. The already verified finite
coinvariant extension gives module finiteness. Artin--Tate is the exact root
mathlib theorem `fg_of_fg_of_fg`; the inclusion's injectivity is the literal
subalgebra subtype map. No additional domain, nontriviality, étale, or faithfully
flat hypothesis is introduced. Faithful flatness is already used internally by
the independent finite-extension proof.

The generic `subalgebra_finiteType_of_moduleFinite` wrapper keeps its ambient
finite-type hypothesis. The actual patch wrappers derive that input from the
curve, instead of assuming it. No Noetherianity of the entire base scheme is
assumed: only the actual affine base-patch section ring is required Noetherian.

## Scalar and raw quotient API

The actual raw quotient is a subring of `P.chartRing`, initially without an
`P.baseRing`-algebra instance. `quotientBaseHom` is the codomain restriction of
the existing geometric algebra map; membership follows from the proved actual
`quotientRing_eq_coinvariants`. The theorem `quotientBaseHom_comp_subtype` states
that its composite with raw-ring inclusion is exactly the actual `E.π.appLE`
ring homomorphism.

`quotientCoinvariantsAlgEquiv` upgrades the existing raw-subring/coinvariant ring
equivalence to an algebra equivalence over these explicitly fixed scalars.
`quotientRing_finiteType` exposes the raw algebra conclusion with the scalar
structure in a `let`, and `quotientBaseHom_finiteType` gives the corresponding
finite-type ring-hom assertion. No global raw-ring algebra instances are added.
The scalar-definition/equivalence section remains byte-identical to the original
97-line approved fixture.

## Final named strict check

Named artifact emission session 58951 closed with exit code 0. It used the exact
Lean 4.35.0-rc3 binary, correct setup name
`AINTLIBDrafts.YZeroCoarseLocalQuotientFiniteType`, and both `autoImplicit` and
`relaxedAutoImplicit` false. The final log
`/private/tmp/xyin-y0-local-quotient-finite-type-check.log` contains exactly eleven
axiom prints, every one with only `propext`, `Classical.choice`, and `Quot.sound`.
There are no errors or warnings.

All three sanities pass: the unconditional actual source-chart finite-type
example, the non-domain product-base Artin--Tate example, and the actual raw
quotient scalar ring-hom example. The exact command, closed exit, source/setup/log
hashes, and inspected correct-name `.olean`, `.olean.private`, `.olean.server`,
`.ilean`, `.ir.sig`, and `.ir` artifacts are saved in
`/private/tmp/xyin-y0-local-quotient-finite-type-receipt.json`.

The old 97-line temporary source and its temporary-named artifacts remain frozen
for the separately supervised geometric structure-map proof. Their source and
`.olean` hashes were rechecked unchanged. They are not imported by this retained
module. The original staged unknown Artin--Tate namespace log and the temporary
mid-rebuild unavailable-dependency emission log remain separate from all green
receipts; neither is used as a verification result.

## Use and remaining conclusions

This supplies the actual finite-type scalar algebra and its verified underlying
geometric section map. A future structure-map triangle must still identify the
resulting `Spec` morphism with the actual quotient base map before concluding a
scheme-level property. No scheme-level finite-type/finite-presentation assertion,
quotient properness, smoothness, local Weierstrass construction, quotient elliptic
curve, target-j, or modular polynomial relation is claimed by this module. No held
`NIsogeny` quotient geometry theorem is used.
