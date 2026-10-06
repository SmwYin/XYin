# Scalars of a new transcendental parameter

`RatFuncParameterScalars.lean` proves the actual polynomial/RatFunc/function-field
tower for evaluation at an arbitrary transcendental element. The original base
algebra remains the one supplied by the caller. The polynomial algebra is the
explicitly typed `Polynomial.aeval t`; the rational-function algebra is the
already checked `RatFunc.algHomOfTranscendental t ht`.

The proof uses its literal polynomial restriction. Existing
`IsScalarTower.of_algHom` supplies base-field towers, so no redundant constructor
is added. Two examples check polynomial evaluation and the original constants.

Temporary session55484 and correct-name session43432 were owner-polled CLOSED,
exit0. The complete named log has five exact permitted axiom checks, two examples,
zero diagnostics and no `sorryAx`. All six canonical artifacts and the C output
were independently rehashed by the root after closure. Retained/work source SHA
`181736a18eb25c66e122498561c0b9af5ee18f7c20ce1a054aae7f1deece809c`;
receipt `/private/tmp/RatFuncParameterScalars-receipt.json`, SHA
`7c85c44fca13c069ad4d958f476cf99c1a8726ca9d8fb27b6b90ce3bb0c643e9`.

The initial failed probe and full log remain separate. Its errors were an
untyped polynomial evaluation algebra and the incorrect primitive name
`AlgHom.isScalarTower`; neither failed output is counted as verification.
Strict implicit flags remain false, with no plugins or dynlibs. This leaf is
outside the historical99-module checkpoint until the next cumulative build.
