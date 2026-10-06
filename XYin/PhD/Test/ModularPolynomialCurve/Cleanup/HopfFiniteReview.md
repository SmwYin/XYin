# HopfFinite independent review

Review date: 2026-10-04. **Verdict: PASS for the retained source and named strict
receipt.** Only this review document was edited; no Lean proof edits or compiler
invocations were performed by the reviewer.

## Frozen source

[YZeroCoarseHopfFinite.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseHopfFinite.lean)
has 77 lines and SHA-256
`fae6683c1c80fbbefd618bcd998960f86c10d7667c04c1aba46a49d0e357eb77`.
The accepted temporary source had 54 lines and SHA-256
`9eb6b81a6d8fc4d514e48d98c16f7dd51c9a1a087d4b932f97b269797efa5b0e`.
The retained diff contains only the license, module exposition, and two
docstrings. Statements, proofs, two sanity checks, imports, and eight axiom
prints are unchanged. Retained and isolated copies were independently checked
byte-equal.

## Actual descent argument

The generic result is

```lean
theorem coinvariants_finite [Module.Finite R0 A] (h : IsHopfGalois ρ) :
    Module.Finite (coinvariants ρ) B
```

Set `S = coinvariants ρ`. Base change of the finite `R0`-module `A` makes
`B ⊗[R0] A` finite over its **left** `B` factor. The previously checked
`galoisEquivOverLeft h`, used in its inverse direction as a `B`-linear
equivalence, transfers this finite-module structure to `B ⊗[S] B`.
The actual field `h.faithfullyFlat` supplies `Module.FaithfullyFlat S B`.
Faithfully flat descent then yields `Module.Finite S B`.

The exact descent primitive at mathlib `RingTheory/Finiteness/Descent.lean:34`
requires `Module.FaithfullyFlat R T` and `Module.Finite T (T ⊗[R] M)`. Here
`R = S`, `T = B`, and `M = B`: the factors and scalar structures align with the
checked left-factor equivalence. The base-change primitive is at
`RingTheory/TensorProduct/Finite.lean:79`. No domain, Noetherian, field, or
already-finite coinvariant-extension premise is present.

The actual `chartCoinvariants_finite` specialization keeps the canonical
`AffineChartPatch` algebra instances. Its coefficient algebra is the actual
`P.groupRing`, finite over `P.baseRing` by pinned `StableChartData.lean:85`
from the genuine finite subgroup structure map. The coaction is literally
`P.chartCoaction`; `P.isHopfGalois_chartCoaction` at `:146` needs the explicitly
retained `Module.Free P.baseRing P.groupRing` prerequisite. No substituted
coaction or desired geometric conclusion is assumed.

## Named strict verification and boundary

Named emission session 62043 closed exit 0. The actual log
`/private/tmp/xyin-y0-hopf-finite.log` contains eight axiom checks, each with
exactly `propext`, `Classical.choice`, and `Quot.sound`, and no diagnostics.
The algebra-map finiteness sanity and actual chart-module sanity both pass.

The actual setup `/private/tmp/YZeroCoarseHopfFinite.setup.json` names
`AINTLIBDrafts.YZeroCoarseHopfFinite`, sets both implicit-variable options to
`false`, and has no plugins or dynamic libraries. Canonical artifact sizes
were independently checked: `.olean` 24168 bytes, `.olean.private` 20072,
`.olean.server` 2656, `.ilean` 9458, `.ir` 2240, and `.ir.sig` 176.
The environment retains AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`,
mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.

The first mathematical-green temporary run had three `letI` style warnings;
its log is preserved at `/private/tmp/YZeroHopfFiniteProbe.kernel-green-warnings.log`.
The final temporary run 48949 closed exit 0 with the same eight standard-three
prints and no diagnostics. Its only cleanup changed the three `letI` binders
to `let`; no mathematical input or proof route changed.

This leaf proves module finiteness of the actual chart sections over their
coinvariants. It does not yet identify the local quotient scheme map as a
finite morphism, or prove the global glued quotient projection finite. It
claims no étaleness, properness, or quotient Weierstrass model.
