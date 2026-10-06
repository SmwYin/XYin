# Actual subgroup quotient: finite type, finite presentation, and properness

The source is AINTLIB's actual raw subgroup quotient. The auxiliary
`AffineChartPatch.quotientToBase` is the Spec map of the previously proved
`quotientBaseHom`, followed by the actual base patch's affine isomorphism.
`localQuotientOpenπ_quotientToBase` proves its structure triangle with the
original chart. The proof uses the literal subtype/scalar formula, the
contravariant Spec composition, and the original `toSpecΓ` naturality square.
This map is not merely an independently chosen candidate with assumed
compatibility.

`gluedQuotientι_gluedQuotientS` proves that the real global structure map
restricts to `quotientToBase` followed by the base open immersion. Its proof
cancels the real local quotient projection, using its proved epimorphism
property and the original glued projection triangle. These two formulas also
supply the common scalar-to-scheme API for future smoothness checks.

Over a locally Noetherian base scheme S, the base section ring of each affine
patch is Noetherian. The actual patch's quotient scalar hom is finite type by
the checked Artin--Tate leaf. Source-locality on the actual quotient chart
cover gives `gluedQuotientS_locallyOfFiniteType`. Mathlib's clean Noetherian
instance gives local finite presentation; the proved separation and universal
closedness then provide the three fields of the real `IsProper` record.
No subgroup etaleness, domain, or Noetherianity of the quotient is assumed.
The public wrappers use the same actual `killN` and `killN_spec`; the literal
axis wrapper works over any Noetherian base ring with the existing invertible
level and full marking. Generic chosen-killing and actual complex level-3
examples pass.

The Noetherian condition is the scope of this Artin--Tate proof. It is not
claimed to be necessary for the mathematical finite-locally-free quotient.
The retained source avoids the sorried general source-precomposition
finite-presentation descent and the held `NIsogeny` quotient geometry gates.
It does not prove smooth relative dimension one, a Weierstrass model, genus
one, or quotient-j. Properness and a section alone do not imply these models.

Strict named compilation closed session 90232 with exit 0: thirteen exact
standard-three axiom checks, two examples, and no diagnostics. The retained
source is 218 lines, SHA-256
`f60f224d08800a83f55af35b8faf37a80cc2b5614a1354b72051e4568b38e2c3`.
Its mathematical program is identical to the independently reviewed 189-line
temporary version; differences are documentation and relocated axiom prints.
Source copies are byte-identical, and six named artifacts exist. The log is
`/private/tmp/xyin-y0-subgroup-quotient-finite-type.log`; the individual receipt
is `/private/tmp/xyin-y0-subgroup-quotient-finite-type-receipt.json`.
The cumulative receipt must separately include this new module.

Runtime: Lean v4.35.0-rc3; AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`; mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`. Both implicit flags are false.
The XYin toolchain is unchanged.
