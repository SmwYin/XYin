# Canonical stalk points over independently geometric constants

`StalkPointOverBase.lean` proves the literal base triangle of `X.fromSpecStalk x`
for every point of any scheme over a field. Its scalar map is the independently
defined structure-map/appTop/germ algebra. The proof uses the actual stalk-point
appTop formula, ΓSpec naturality, cancellation and affine-target extensionality.
There is no integrality, irreducibility or affineness assumption on the scheme.
Two clients check the point itself and arbitrary spectrum precomposition.

The first temporary41124 exited0 with an unused-integrality warning; its complete
source and log are preserved separately. Removing only that unnecessary section
binder gave temporary33689 and named63250, both owner-polled CLOSED exit0, six
exact standard-three checks, two APIs, zero diagnostics and no `sorryAx`.
Retained/work source SHA
`7faeee008a1097ead9c82f6764298b2044825e385fe0eab327ddb784b0843885`.
Root and independent reviewer checked complete source/log/strictsetup and all
six canonical artifacts plus C against `/private/tmp/StalkPointOverBase-receipt.json`.
Strict implicit flags remain false with no plugins/dynlibs. This leaf follows
the historical99-module checkpoint and is not counted in that receipt.
