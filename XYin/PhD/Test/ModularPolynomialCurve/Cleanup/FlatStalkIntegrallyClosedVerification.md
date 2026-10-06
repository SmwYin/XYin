# Flat surjective stalk normality descent

`AINTLIBDrafts.FlatStalkIntegrallyClosed` is retained and frozen. Named
compiler session **20245 CLOSED, exit 0** in the pinned isolated environment.
Source SHA256:
`eeb8dff44ff15fefee3ef470d5981f960975f0d31c263f509c3d429cd4363c16`.

The full named log `/private/tmp/xyin-y0-flat-stalk-integrally-closed.log`
contains seven exact standard-three axiom checks, two API examples and zero
diagnostics. `/private/tmp/FlatStalkIntegrallyClosed-receipt.json` records
source, correct-name strict setup, full log and six canonical outputs plus C
hashes. Copies agree. The examples exercise identity and a flat surjective
map with supplied source stalk normality. Independent full source and output
review accepted the successful temporary proof.

The proof equips the actual source stalk with the algebra of `f.stalkMap x`.
Flatness and the scheme morphism's local-hom property make this map faithfully
flat, so the separately checked algebraic descent lemma applies. Surjectivity
then supplies a source point over each target point. No finite, étale,
Noetherian or scheme-integrality hypothesis is added.

Two temporary failures only concerned naming/application of the surjectivity
projection; their sources and logs are archived separately. The final proof
uses `f.surjective y`. An initial named command had a mistyped executable path
and never invoked Lean; the corrected named invocation above is the receipt.
This new leaf is outside the cumulative 76-module checkpoint.
