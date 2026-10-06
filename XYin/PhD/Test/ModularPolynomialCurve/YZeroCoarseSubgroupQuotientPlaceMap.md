# Actual subgroup quotient place map

The raw `gluedQuotientPlaceMap N hkill` and public `quotientPlaceMap` send each intrinsic source place to the unique target place whose normalized valuation agrees on the literal native function-field pullback. The helper `FunctionField.Place.valuation_injective` proves that equality of normalized valuations determines the place, using the native valuation-subring recovery theorem.

`gluedQuotientPlaceMap_valuation` / `quotientPlaceMap_valuation` expose the exact pullback formula. `gluedQuotientPlaceMap_closedPoint` / `quotientPlaceMap_closedPoint` identify the map of a genuine closed-point place with the place of its actual quotient image. Both geometric constant algebras are the independently defined structure-map algebras. The hypotheses are an arbitrary base field, the actual subgroup etaleness, and the raw killing datum or public chosen killing integer; there is no characteristic-zero or target-place representation premise.

Finite fibers, place-map surjectivity, quotient genus and a quotient model are not conclusions of this file.

Verification: strict correct-name emission session 91268, owner-polled CLOSED exit 0. Twelve exact axiom checks (eleven standard triples; `Valuation.ext` uses `propext` and `Quot.sound`), two raw/public API examples and no diagnostics. The accepted 152-line temporary mathematical suffix is byte-preserved; only the license and scope header were added. All six canonical artifacts and the C output are recorded in `/private/tmp/xyin-y0-subgroup-quotient-place-map-receipt.json`.
