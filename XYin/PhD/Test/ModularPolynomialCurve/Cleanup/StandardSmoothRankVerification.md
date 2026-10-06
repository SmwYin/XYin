# Standard smooth differential stalk rank

Verified 2026-10-04 against AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
**The named strict check is CLOSED with exit 0; the source is frozen.**

## Statement and scope

[YZeroCoarseStandardSmoothRank.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseStandardSmoothRank.lean)
exports `ModularPolynomialCurveTest.AINTLIB.RelativeDimension.kaehler_rankAtStalk_eq_of_standardSmooth`:

```lean
(R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
(n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R A]
(P : PrimeSpectrum A) : Module.rankAtStalk (R := A) Ω[A⁄R] P = n
```

`P.nontrivial` supplies the nontriviality needed by the existing global
differential rank theorem. Standard smoothness supplies a free differential
module. The proof then uses the free-module stalk-rank formula and
`Module.finrank_eq_of_rank_eq`; it introduces no Noetherian, field, domain,
or separate nontriviality hypothesis.

Two actual instances are checked: the identity algebra has rank zero at each
prime, and `MvPolynomial (Fin 1) R` has rank one at each prime. Neither example
assumes the result as a premise.

This is a globally standard-smooth algebra statement. No adapter from locally
standard smoothness, relative-dimension descent, scheme quotient upgrade,
genus computation, or Weierstrass presentation is included.

## Retention and exact compiler receipt

The retained source has 60 lines, maximum width 89, SHA-256
`6cbf56b6b03e609df4094cec270c4f387b39e049e5f19f63c381435410ef9ef2`.
Its isolated copy is byte-equal. The mathematical namespace, theorem,
hypotheses, two examples, and six axiom-print checks are byte-identical to
the parent-reviewed 38-line temporary proof. Only the standard license and
accurate module scope documentation were added.

Named emission **48679 closed with exit 0** using the following exact command
from `/private/tmp/xyin-y0-aintlib-work`:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/YZeroCoarseStandardSmoothRank.lean --setup YZeroCoarseStandardSmoothRank.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseStandardSmoothRank.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseStandardSmoothRank.ilean > /private/tmp/xyin-y0-standard-smooth-rank-check.log 2>&1
```

The actual setup names `AINTLIBDrafts.YZeroCoarseStandardSmoothRank`, sets
`autoImplicit=false` and `relaxedAutoImplicit=false`, and has no plugins or
dynamic libraries. Setup SHA-256:
`e7f549fff0caa60b86435862461d1aa5af02780b55d26dff38cbedb01b309fa5`.

The full actual log contains six exact standard-three axiom checks, including
the own theorem and all five printed primitives. Both examples pass; there
are zero warnings/errors and no `sorryAx`. Log SHA-256:
`eaf05322b279a3d39abe9e065b31d85c1d0c6e63fe805651020d8262fbb847b6`.

All six correct-name artifacts were read and their sizes and SHA-256 hashes
recorded in `/private/tmp/xyin-y0-standard-smooth-rank-receipt.json`:
`.olean` 9512, `.olean.private` 8592, `.olean.server` 2232, `.ilean` 5179,
`.ir` 1848, and `.ir.sig` 176 bytes. This individual leaf receipt does not
claim a new cumulative build of all retained modules.
