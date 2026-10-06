# Standard smooth dimension from one stalk rank

Verified 2026-10-04 with AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
**The named strict emission is CLOSED with exit 0; the source is frozen.**

## Statement and scope

[YZeroCoarseStandardSmoothRankConverse.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseStandardSmoothRankConverse.lean)
exports `RelativeDimension.isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk`
in the `ModularPolynomialCurveTest.AINTLIB` namespace:

```lean
(R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
(n : ℕ) [Algebra.IsStandardSmooth R A] (P : PrimeSpectrum A)
(hrank : Module.rankAtStalk (R := A) Ω[A⁄R] P = n) :
Algebra.IsStandardSmoothOfRelativeDimension n R A
```

A prime supplies `Nontrivial A`. Standard smoothness supplies finite
presentation and a free differential module; finite presentation supplies
finite differentials. The free-module stalk-rank formula gives the global
finrank from `hrank`, and `Module.finrank_eq_rank` gives the cardinal rank
used by the existing standard-smooth dimension characterization.

There is no additional Noetherian, field, domain, or nontriviality hypothesis.
One prime suffices because the original algebra is globally standard smooth.
The identity-dimension-zero and one-variable-polynomial examples use actual
instances and actual rank inputs. No full local-condition converse, local
chart construction, scheme relative-dimension descent, or elliptic quotient
model is proved in this module.

## Source and exact receipt

The source has 69 lines, maximum width 87, SHA-256
`a8a185937346d05cbddfc22dbdfed22516eee961d4996f6a97bef27c449fb6eb`.
Retained and isolated copies are byte-equal. The parent-reviewed 49-line
temporary proof's mathematical namespace, hypotheses, examples, and checks
are preserved byte-for-byte; only license and accurate scope documentation
were added.

Named emission **43166 closed with exit 0**, using the exact command below
from `/private/tmp/xyin-y0-aintlib-work`:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/YZeroCoarseStandardSmoothRankConverse.lean --setup YZeroCoarseStandardSmoothRankConverse.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseStandardSmoothRankConverse.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseStandardSmoothRankConverse.ilean > /private/tmp/xyin-y0-standard-smooth-rank-converse-check.log 2>&1
```

The actual named setup has both implicit options false and empty plugin and
dynamic-library lists. Setup hash:
`2fd082e687150f2e4010c6c8d9db76df3a97e07fcba105566165e65c58d3052a`.
The complete log has eight exact standard-three checks, zero diagnostics,
no `sorryAx`, and both examples pass. Log hash:
`132b42acb0677ecfeca4b57f2d24fd9cb29ddc47e049fa5878f5b02355088d05`.

All six correct-name artifacts were read and their sizes and hashes recorded
in `/private/tmp/xyin-y0-standard-smooth-rank-converse-receipt.json`:
`.olean` 9960, `.olean.private` 14800, `.olean.server` 2136, `.ilean` 7313,
`.ir` 1848, and `.ir.sig` 176 bytes.

The first temporary compile failed only on constant-function rank evaluation
and a missing explicit identity standard-smooth instance. Its source and log
were preserved, and compiler-recovery `sorryAx` output is excluded. The
targeted repairs did not change the statement or hypotheses. This newly
retained leaf is outside the earlier cumulative47 checkpoint; its verification
is the separate named receipt above.
