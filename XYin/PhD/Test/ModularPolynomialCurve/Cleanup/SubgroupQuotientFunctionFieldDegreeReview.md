# Independent actual quotient function-field degree review

Read the complete root-owned temporary source `/private/tmp/xyin-y0-aintlib-work/YZeroSubgroupQuotientFunctionFieldDegreeProbe.lean`, 92 lines, SHA
`aff2b30a7ee2c585437d2c39a077d32088d7d4f44eceb9abf4b199907d3926f7`, the full first log `/private/tmp/YZeroSubgroupQuotientFunctionFieldDegreeProbe-first.log` (SHA `44c8773d813556ed25c0a36b5861c1eaee5542f6a685275f66ac31282fbca793`),
and the actual strict setup (SHA `20b5ad12dbca2230193a49f2d06b475c5c931a6a8f04fd03c14d753688943f92`). Root's exact receipt
`/private/tmp/YZeroSubgroupQuotientFunctionFieldDegreeProbe-receipt.json` confirms session 22605 CLOSED exit 0. This reviewer
performed no source edit or compiler call and makes no named artifact claim.

Verdict: **PASS** for the precise native degree statement. The source curve is
an actual `EllipticCurve (Spec k)` over any field, whose genuine integral-scheme
instance is available from the checked upstream field theorem. The raw quotient's
integrality, projection surjectivity, finiteness and flatness are the retained
actual construction theorems, rather than assumptions about a new quotient curve.
Surjectivity supplies dominance for the actual native pullback.

The module structure is explicitly `functionFieldAlgebra` of the literal
`G.gluedQuotientπ N hkill`, hence the existing native dominant
`functionFieldMap.hom.toAlgebra`. The exact generic finite-flat degree theorem
compares this same scalar structure with the scheme fibre rank. Its symmetric
equality, evaluated at the genuine target generic point, followed by the proved
actual global subgroup-rank equality has the correct direction: native field
extension finrank equals the supplied `G.HasRank r` value. No convenient arbitrary
field embedding or desired-degree comparison is substituted.

The public wrapper is definitionally the same construction at the genuine
chosen killing integer. Its explicit integral/surjective/algebra lets align with
the actual public quotient/projection definitions by proof irrelevance. The
marked-axis specialization uses its proved rank `N` and actual killing datum;
it does not postulate a cyclic subgroup/quotient elliptic model. The native
complex level-three example uses the literal pulled-back native curve and its
actual full-level marking, with the same field-extension scalar.

All 11 actual printed declarations depend exactly on `propext`,
`Classical.choice`, `Quot.sound`; no `sorryAx`, errors or warnings occur. The two
examples check the public ranked subgroup and actual native complex level-three
axis. Both implicit-variable options in the correct temporary setup are false.

This is the degree of the actual native `E → E/G` function-field map. It does
not identify `Y_0`'s function field with a modular-polynomial function field, nor
prove a quotient genus/model/j-invariant, unramifiedness at every place, or a
modular polynomial relation.

## Independent named follow-up before the cumulative-76 rebuild

Read the complete retained 114-line named source and complete named log, then
independently checked `/private/tmp/YZeroCoarseSubgroupQuotientFunctionFieldDegree-receipt.json`
against the actual files. The named source SHA is
`fa8c23229cde4cda6adab461dbcdbab22970a00b4d2deb3ec294f0b1b86a44ac`;
retained and isolated copies agree, and the entire accepted 92-line mathematical
suffix is byte-preserved. The correct module name is
`AINTLIBDrafts.YZeroCoarseSubgroupQuotientFunctionFieldDegree`.
Both implicit-variable options are false, and the setup has no plugins or dynlibs.
The setup SHA is `97a7cffdf113ac0075ee48fa8a1326bd61d8a961b2f3323322347077e4be7366`.

The supplied closed process receipt records 87582, exit 0. The full named log
has 11 exact standard-three prints, two examples, zero errors/warnings and no
`sorryAx`; its SHA is the same as the accepted temporary log above. All six
correctly named canonical artifacts and C were present and independently
size/SHA-checked against the receipt before cumulative-76 output deletion:
32760, 14800, 2928, 23017, 1720, 176, and 4298 bytes respectively. No compiler was
run by this reviewer. Verdict: **PASS** for both mathematics and named provenance.
These are historical leaf artifacts; the subsequent fresh cumulative build
supersedes them rather than invalidating this time-specific check.
