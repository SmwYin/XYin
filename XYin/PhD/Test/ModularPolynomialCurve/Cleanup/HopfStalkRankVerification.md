# Hopf--Galois stalk-rank comparison: verification receipt

Retained module: `AINTLIBDrafts/YZeroCoarseHopfStalkRank.lean`. Retained and
isolated sources are byte-identical: 76 lines, maximum width 95, SHA256
`94cd6216c8567120a45cc5a6b42988b43af62aafb81e0ff1a0642ce1206b34e4`.
Retention adds only the standard license and short module documentation.
The mathematical suffix, all eight axiom prints, and both API examples are
byte-identical to the approved 52-line fixture, SHA256
`6343abac126e176a4ebc1f8b2e4e2c29b31dc438fe497fb20b1fa81b8b29c753`.

## Precise statement and scalar direction

The generic inputs are commutative algebras `A` and `B` over `R`, the actual
map `ρ : B →ₐ[R] B ⊗[R] A`, and `h : IsHopfGalois ρ`. Write
`C = coinvariants ρ`, with its canonical inclusion into `B`.
`HopfGaloisLeft.coinvariants_rankAtStalk_eq` requires exactly
`[Module.Finite R A]` and `[Module.Flat R A]`. For a given prime `q` of `B` it proves

```lean
Module.rankAtStalk (R := C) B (q.comap (algebraMap C B)) =
  Module.rankAtStalk (R := R) A (q.comap (algebraMap R B))
```

The same actual prime `q` occurs on both sides before the two scalar comaps.
There is no extra freeness, domain, Noetherian, étale, smoothness, group-rank,
or constant-rank hypothesis. No new comparison record or replacement action
is introduced. The existing Hopf--Galois datum supplies all action information.

## Actual proof inputs

The frozen `galoisEquivOverLeft h` is a `B`-algebra equivalence
`B ⊗[C] B ≃ₐ[B] B ⊗[R] A`. Its linear equivalence gives equality of the two
stalk-rank functions. `congrFun` evaluates this equality at the actual `q`.
The two `Module.rankAtStalk_baseChange` rewrites identify the left function
with the rank of `B/C`, and the right with the rank of `A/R`, at their respective
comaps.

The base-change theorem's finite and flat hypotheses on `B/C` come from the
retained `coinvariants_finite h` and the literal `h.faithfullyFlat` field.
The corresponding hypotheses on `A/R` are the two explicit generic inputs.
Thus there is no hidden freeness or ring-domain premise in either rewrite.

The first example exercises the generic API. The second specializes to the
coefficient identity algebra `A = R`, whose stalk rank is one; the genuine
`IsHopfGalois` input remains explicit. Its lifted prime supplies nontriviality
of `R`. No ready concrete trivial Hopf fixture was found or manufactured, and
this example does not claim that arbitrary coactions are Hopf--Galois.

## Strict named verification

Named emission closed as session 1622 with exit code 0. It used the exact
pinned Lean 4.35.0-rc3 binary, correct setup name
`AINTLIBDrafts.YZeroCoarseHopfStalkRank`, and both `autoImplicit` and
`relaxedAutoImplicit` false. The setup has 9455 normalized import entries.
All eight selected own and primitive axiom prints use exactly `propext`,
`Classical.choice`, and `Quot.sound`. Both examples pass with no errors or
warnings. The final named log is byte-identical to the clean first temporary
log, SHA256 `99c9c88db1b2dcc2d86b575b5286cc44153791302dd585394eb5de53432032d0`.
The temporary proof also passed on its first strict invocation, session 17609,
without source repair.

All six correct-name artifacts were inspected in the isolated
`.lake/build/lib/lean/AINTLIBDrafts/` directory: `.olean`, `.olean.private`,
`.olean.server`, `.ilean`, `.ir.sig`, and `.ir`. Exact sizes, hashes,
source/setup/log provenance, command, closed exit, and complete primitive list
are saved in `/private/tmp/xyin-y0-hopf-stalk-rank-receipt.json`.

## Scope boundary

This is a stalk-rank comparison at a lifted prime. Faithful-flat prime lifting,
constant-rank descent, the actual group-chart `HasRank` adapter, local/global
scheme fibre rank, and the native function-field extension degree remain
separate proof steps. It does not introduce a quotient elliptic curve or
prove quotient-j, a modular-polynomial relation, or a genus statement. No held
NIsogeny quotientCurve or quotient-geometry statement is used.
