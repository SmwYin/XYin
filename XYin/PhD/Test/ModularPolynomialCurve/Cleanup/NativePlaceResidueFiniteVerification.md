# Every native elliptic place has finite residue

`NativePlaceResidueFinite.lean` removes the explicit chart inputs from the generic
residue-finiteness theorem when the field is that of an actual native elliptic
curve. Its base algebra is independently defined by the geometric structure map.
The already proved native polynomial/RatFunc towers, finite FunctionField
structure and separability supply every chart premise. The theorem holds over
an arbitrary field. A second theorem gives positive residue degree.

The two examples exercise a native curve and an actual Weierstrass model.
Temporary41550 and named66655 were owner-polled CLOSED, exit0, first attempts.
The full named log has eight exact standard-three axiom checks, two API examples,
zero diagnostics and no `sorryAx`. Retained/work source SHA
`0032658a38843a6b938c98ba2ffb77e9d6635a4f52a00c401fb28f9a5c886d65`.
The root recomputed all six canonical artifacts and C hashes against
`/private/tmp/NativePlaceResidueFinite-receipt.json` after closure. Both implicit
flags remain false and plugins/dynlibs are empty. This independent check follows
the historical99-module checkpoint. It does not assert geometric surjectivity,
point injectivity or a place bijection.
