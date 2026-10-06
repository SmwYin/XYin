# Actual quotient divisor pullback

**Verified and frozen.** The retained 125-line `AINTLIBDrafts.YZeroCoarseSubgroupQuotientDivisorPullback` defines `gluedQuotientDivisorPullback` and the literal chosen-killing wrapper `quotientDivisorPullback`. Each is an additive homomorphism from actual quotient divisors to source divisors. The coefficient theorems state exactly

```lean
G.gluedQuotientDivisorPullback N hkill D v = D (G.gluedQuotientPlaceMap N hkill v)
G.quotientDivisorPullback D v = D (G.quotientPlaceMap v)
```

The underlying divisor type is the actual native abbreviation `FunctionField.Divisor k K := Place k K →₀ ℤ`. Applying the checked finite-fiber Finsupp additive hom to the proved actual place-map finite fibers supplies finite support. Place restriction has direction `Place(E) → Place(Q)`; consequently the divisor map has direction `Divisor(Q) →+ Divisor(E)`. Both independently geometric constant algebras are the original `E.π` and `Qπ` algebras. Actual quotient integrality and surjectivity are proved inputs installed locally, rather than external hypotheses.

Scope is **any field** and the actual subgroup étaleness input, with a genuine nonzero killing integer/witness or the public native killing datum. No characteristic-zero, chart parameter, field-pack, principal-divisor, degree, genus or quotient-model premise is used here. In particular, this coefficient pullback alone does not claim principal-divisor compatibility or a degree formula. Its coefficients have no ramification factor; compatibility requires the separate genuine place-valuation identity.

The raw sanity verifies the coefficient of the pullback of a sum, using the actual quotient map. The public sanity verifies its coefficient formula with the actual chosen killing datum. Both are checked under the original geometric algebras.

## Closed verification receipts

Temporary source: `/private/tmp/xyin-y0-aintlib-work/YZeroSubgroupQuotientDivisorPullbackProbe.lean`, 105 lines, source SHA `be0673ff647a316a43b8404b9d6f06ddb87af41f55a31c2f698a7da246a0a84c`. Owner **76438 CLOSED exit 0**, first attempt, no failed runs, no outputs emitted. Root reviewed full source and full nine-print log before promotion; the independent sibling source review also passed.

Named owner **13877 CLOSED exit 0**, confirmed by an owner process poll. All **nine exact standard-three axiom prints**, **two actual API examples**, **zero diagnostics**. Ordered newline-bounded parsing agrees with the receipt. Correct module name, both implicit flags false, empty plugins/dynlibs. The complete accepted expose suffix is byte-exact, and retained/work sources agree. Promotion changed only license/scope documentation.

- Source SHA: `0264e701538f96da6902740f917a0b628574b5254e4638cc53cc8c776d6421f1`.
- Setup: `/private/tmp/xyin-y0-aintlib-work/YZeroCoarseSubgroupQuotientDivisorPullback.setup.json`, SHA `d97cfdf3ad22363d9583587ff74c3e940d9f198bee7d654a756229820b433a21`.
- Full named log: `/private/tmp/YZeroCoarseSubgroupQuotientDivisorPullback-named.log`, SHA `efca39aa82e6e54d394e9a108fbb599d134df95dfc12d45e71385835df9fcf4d`.
- Receipt: `/private/tmp/YZeroCoarseSubgroupQuotientDivisorPullback-receipt.json`, SHA `4eb2ec7291e7667064b6a22eddc0fbd036509de0e71c9707e6fed14a830eb110`.

The six canonical artifacts under `/private/tmp/xyin-y0-aintlib-work/.lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientDivisorPullback` have sizes **72176 / 21456 / 2472 / 23020 / 2016 / 176** for `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, `.ir.sig`. The C output at the corresponding `.lake/build/ir/AINTLIBDrafts/` path has **4365** bytes. All seven sizes and SHA hashes are saved in the receipt. This named check is after cumulative126; no cumulative inclusion is claimed until the next fresh gate.

No other retained Lean source, model, settings, pinned dependency or existing named receipt was changed. All owned Lean/config/receipt mutation and compiler work is now frozen pending the parent gate.
