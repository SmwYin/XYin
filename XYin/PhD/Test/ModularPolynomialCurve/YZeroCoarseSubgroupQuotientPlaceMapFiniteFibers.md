# Finite fibers of the actual quotient place map

`AINTLIBDrafts.YZeroCoarseSubgroupQuotientPlaceMapFiniteFibers` proves that the raw and public quotient place restriction maps have finite fibers. The base field is arbitrary; the actual subgroup structure map must be etale, with an actual killing datum (or the public `HasKillingInt` instance). The original geometric constant algebras and native function-field maps are used.

A nonempty fiber chooses a genuine closed-point representative on the source elliptic curve. The checked closed-point formula and target closed-point-place injectivity force every source representative into the same finite scheme fiber. Pulling that fiber to the closed-point subtype and taking its place image bounds the whole place fiber. No characteristic-zero hypothesis, representation of every target place, or quotient place equivalence is needed.

The retained mathematical suffix is byte-identical to the accepted 115-line temporary probe. Only the license and scope documentation were added. Strict named compilation session **57329** was owner-polled **CLOSED, exit 0**. All eleven axiom checks use only `propext`, `Classical.choice`, and `Quot.sound`; both raw/public API examples pass, with no diagnostics. Six canonical artifacts and the C output were emitted under the exact module name.

Current source SHA256: `68d2a06e1a79b0ab9bf89e566b2cb6794394ce744e157941c36c67648190b436`.

Full log: `/private/tmp/xyin-y0-subgroup-quotient-place-map-finite-fibers.log`.
Full provenance receipt: `/private/tmp/xyin-y0-subgroup-quotient-place-map-finite-fibers-receipt.json`.

The two earlier temporary failures were pre-elaboration import-catalog failures, not green proof receipts. They are preserved separately; the Lean source stayed unchanged while the setup's checked direct import closure was repaired. The final named source is frozen. Divisor compatibility, place-map surjectivity, genus and a quotient model remain separate proof obligations.
