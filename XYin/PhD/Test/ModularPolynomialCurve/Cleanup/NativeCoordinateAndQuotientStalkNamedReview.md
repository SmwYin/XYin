# Independent named coordinate-field and quotient-stalk review

This is a read-only cross-audit of complete named source, full logs, strict
setups, receipts and actual outputs, performed before the cumulative-76 build
replaces old artifacts. No Lean source was edited and no compiler was run.
Closed exit statuses below are taken from the corresponding owner/root receipts;
this reviewer independently checked the files and hashes.

## Coordinate fraction field

Read all 116 lines of `AINTLIBDrafts.NativeCoordinateFractionField` and the full
nine-print log. Verdict: **PASS**. The coordinate map is literally the inverse
of the already proved native field comparison composed with the coordinate
ring's fraction-field embedding. The independent source constant algebra is
preserved. `IsScalarTower.of_algebraMap_eq` uses the inverse comparison's actual
commutes law in the correct symmetric direction. The coordinate-ring AlgEquiv
uses that same ring map; its linearity is definitional, and fraction-ring
transfer is therefore along the actual coordinate algebra. There is no field
model, generic embedding, polynomial scalar, full-constant, or genus assumption
substituted for the native comparison.

Owner receipt `/private/tmp/xyin-y0-native-coordinate-fraction-field-receipt.json`
records named session 77344 CLOSED exit 0. Source SHA
`f0d3c86b5cc1c789a1bddc804eff12ab186321fb45f36ece0f10527961d4cdfa`,
setup SHA `2c9d9908c4ba2c1c84b3f5e44d90e7a20c3c31b9edd04465dc4c57da5a050dc1`,
log SHA `47ccee170d62fde46dc0e0c95d86aa175f733d1794dc32cd2db10fbe02b3fd9a`
were independently verified. Retained/work source copies and the accepted probe
suffix agree byte for byte. The nine prints are six standard-three checks and
three permitted subsets: `propext`, `propext, Quot.sound`, and `Quot.sound`.
Two actual model/constant examples and zero diagnostics remain. All six
canonical outputs plus C match receipt hashes and sizes:
45328, 28712, 3688, 18511, 1800, 176, 3599 bytes.

## Actual subgroup quotient stalk map

Read all 99 lines of `AINTLIBDrafts.YZeroCoarseSubgroupQuotientStalkMap`, its
complete twelve-print log, and the complete generic `StalkMapMaximalIdeal`
source used by the wrappers. Verdict: **PASS**. The generic primitive installs
the algebra of the literal stalk ring map, obtains its actual local-map,
essentially finite-type and formally-unramified inputs, and applies the ring
maximal-ideal theorem. The actual quotient wrapper supplies the genuinely proved
étale projection; étale provides the generic primitive's weaker hypotheses.
The public chosen-killing and literal marked-axis wrappers retain the same
stalk map, with their actual killing and subgroup étale inputs. No domain,
Noetherian, DVR, normality, ramification-index, or quotient-model premise is
hidden in this formula.

Root receipt `/private/tmp/xyin-y0-subgroup-quotient-stalk-map-receipt.json`
records session 43740 CLOSED exit 0. Source SHA
`d6b9e0a9fbae53be916b239098d4ff1bdd0aac48984cb3e7b4de3f211e8e6e3b`,
setup SHA `0bde01a9b88922c098119a504d458b3cd1b22284f77e9e7a8d5a4bf00abd59bf`,
log SHA `7769153eb907ba149bafd8aa9497fc8a6eb57234b734fd852c05740dd0c46bd5`
were independently verified. Retained/work copies and the accepted temporary
suffix agree byte for byte. All twelve axiom prints are exactly standard-three;
two actual public/level-three examples remain, with zero diagnostics. All six
canonical outputs plus C match receipt hashes and sizes:
33328, 7904, 2800, 21092, 1576, 176, 3591 bytes.

Both setups have the correct full module name, `autoImplicit=false`,
`relaxedAutoImplicit=false`, no plugins and no dynlibs. Source files remain
frozen; historical artifact checks above precede the cumulative build's fresh
output replacement. Root was notified READY after all hashes were checked.
