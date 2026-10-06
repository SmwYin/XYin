# Smooth differential-rank criterion: verification

The retained generic module proves three APIs for a smooth `R`-algebra `S`:

- `exists_notMem_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk` gives a standard smooth localization of dimension `n` containing each prescribed prime when all differential stalk ranks are `n`.
- `locally_isStandardSmoothOfRelativeDimension_of_kaehler_rankAtStalk` assembles these point-indexed localizations into the actual `RingHom.Locally` condition.
- `locally_isStandardSmoothOfRelativeDimension_iff_kaehler_rankAtStalk` combines the converse with the retained forward rank API.

The localization witness comes from the actual smooth-at-prime theorem. The selected element avoids the given prime, so its localization has a genuinely lifted prime. The checked differential base-change comparison transfers the rank, and the smallest standard-smooth converse fixes the local relative dimension. For the full cover, each prime lies in its own selected basic open; `PrimeSpectrum.iSup_basicOpen_eq_top_iff` proves that the selected elements span the unit ideal. The structural scalar composition is converted by the literal `IsScalarTower.algebraMap_eq` identity.

No `Nontrivial S`, domain, Noetherian, or assumed local standard presentation is required. Nontriviality at the only needed calculation follows from the lifted prime. The arbitrary-`n` subsingleton example also verifies the empty-spectrum case: `RingHom.Locally` permits an empty unit-span cover when the ring is zero. This does not assert that a zero localization itself has a standard presentation of every dimension.

The five examples are the per-prime identity/rank-zero and one-variable polynomial/rank-one checks, their full-cover counterparts, and the arbitrary-`n` zero-ring/vacuous-spectrum check. This module contains no scheme gluing, quotient relative-dimension statement, genus computation, or Weierstrass-model construction.

## Exact named receipt

- Source: `AINTLIBDrafts/YZeroCoarseSmoothRankCriterion.lean`, 139 lines, maximum width 95.
- Source SHA256: `166737e182a18330d0946d307580cf28f42335f55636a786acc76e96dcfa4b6d`.
- Strict session `2460` is **CLOSED, exit 0**.
- Complete named output: `/private/tmp/xyin-y0-smooth-rank-criterion-check.log`; SHA256 `639a525bc22e2b9ce93331b5f53a2a63c0d35ea873e80e017d301940bf4ae377`.
- All **11** printed own/primitive checks depend only on `propext`, `Classical.choice`, and `Quot.sound`; all five examples pass; zero warnings/errors or `sorryAx`.
- Correct setup name `AINTLIBDrafts.YZeroCoarseSmoothRankCriterion`, `autoImplicit=false`, `relaxedAutoImplicit=false`; SHA256 `bf3b826e308f50ca64fbd78b08ae2ba30a0a1b71cb908102010c75927a483ce6`.
- Retained and isolated sources are byte-equal. The accepted 117-line temporary mathematical suffix, all checks, and all sanity bodies are preserved exactly; the retention delta consists only of license and module scope documentation.
- All six canonical named artifacts (`.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, `.ir.sig`) and the generated C output exist, have nonzero size, and have independently recorded hashes in `/private/tmp/xyin-y0-smooth-rank-criterion-receipt.json`.

Literal invocation, cwd `/private/tmp/xyin-y0-aintlib-work`:

```text
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/YZeroCoarseSmoothRankCriterion.lean --setup YZeroCoarseSmoothRankCriterion.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSmoothRankCriterion.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSmoothRankCriterion.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseSmoothRankCriterion.c > /private/tmp/xyin-y0-smooth-rank-criterion-check.log 2>&1
```

The earlier per-prime-only 65-line receipt remains separate at `/private/tmp/YZeroSmoothRankLocalWitnessProbe-receipt.json`; the accepted full 117-line first-attempt receipt is `/private/tmp/YZeroSmoothRankLocalWitnessProbe-full-receipt.json`. No failed full-proof staging output is being used: both full temporary and named checks passed on their first elaboration. Existing model/toolchain settings were preserved. The named source and artifacts are frozen.
