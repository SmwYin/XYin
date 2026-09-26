# Core proof cleanup

Baseline: `/tmp/xyin-proof-cleanup-before/XYin`, captured at the start of this turn.
All files below were read in full; changes target proof bodies and reuse of pinned mathlib APIs.
Final cumulative build and independent review receipts are recorded separately in verification.md.

| File | Before | After | Removed |
|---|---:|---:|---:|
| `XYin/PhD/Modularforms/BigO.lean` | 149 | 61 | 88 |
| `XYin/PhD/Modularforms/multipliable_lems.lean` | 149 | 81 | 68 |
| `XYin/PhD/Modularforms/upperhalfplane.lean` | 21 | 17 | 4 |
| `XYin/PhD/Modularforms/IsCuspForm.lean` | 181 | 152 | 29 |
| `XYin/PhD/Modularforms/qExpansion_lems.lean` | 205 | 113 | 92 |
| `XYin/PhD/Modularforms/csqrt.lean` | 79 | 57 | 22 |
| `XYin/PhD/Modularforms/Summability/Basic.lean` | 363 | 206 | 157 |
| `XYin/PhD/Modularforms/E2.lean` | 181 | 109 | 72 |
| `XYin/PhD/Modularforms/clog_arg_lems.lean` | 180 | 94 | 86 |
| `XYin/PhD/Modularforms/Delta.lean` | 598 | 408 | 190 |
| `XYin/PhD/Modularforms/SlashActionAuxil.lean` | 310 | 287 | 23 |
| `XYin/PhD/Modularforms/Eisenstein.lean` | 940 | 692 | 248 |
| `XYin/PhD/Modularforms/NormNumI.lean` | 207 | 205 | 2 |
| `XYin/PhD/ModularFunctions/MeromorphicField.lean` | 662 | 658 | 4 |
| `XYin/PhD/ModularFunctions/JInvariant.lean` | 68 | 57 | 11 |
| `XYin/PhD/Cox/ModularFunctionField.lean` | 197 | 186 | 11 |
| `XYin/PhD/Cox/UpperHalfPlaneFunctionField.lean` | 293 | 264 | 29 |
| `XYin/PhD/Cox/ModularFunction.lean` | 449 | 439 | 10 |
| `XYin/PhD/Cox/ModularFunction/LevelJ.lean` | 331 | 329 | 2 |
| `XYin/PhD/qExpansion_tactic/link.lean` | 438 | 408 | 30 |
| `XYin/uniqueness.lean` | 334 | 297 | 37 |

## Changes and rationale

- BigO shares the vector norm argument in one private helper; integer reindexing uses injective filter maps.
- Infinite products use summability, geometric-product, tprod powers and nonvanishing APIs already in mathlib.
- Cusp-form and q-expansion proofs use cusp limits, coefficient uniqueness and standard derivative/product APIs.
  Three formerly admitted q-expansion results now have proofs.
- Reciprocal square roots reuse one power identity; logarithm argument bounds share a private eventual-bound
  helper and cofinite equality handles finitely many exceptional terms.
- Summability.Basic uses integer/positive-natural reindexing and divisor/Lambert sum APIs, removing hand-built
  equivalences and repeated Fubini summability obligations.
- E2 uses the public Eisenstein E2 transformation and q-expansion identities.
- Delta bridges the unchanged local definition to mathlib's discriminant once; S/T invariance, boundedness,
  the infinite product, and vanishing at the cusp then reuse established discriminant results.
- Eisenstein uses public Fourier coefficient and Bernoulli APIs, q-coordinate inversion, geometric majorants,
  and the discriminant cusp function and leading coefficient. `E4E6_coeff_zero_eq_zero`, previously
  admitted, is now proved from q-expansion linearity, powers, and the constant coefficients of E4/E6.
- SlashActionAuxil reuses the row-reduction and SL2 generator proofs rather than reconstructing matrix witnesses.
- MeromorphicField simplifies the inverse-law zero-germ argument. Its field definition and normal forms are unchanged.
- The bundled j holomorphy proof reuses the new shared global `j_mdifferentiable` theorem,
  which proves differentiability of E4 cubed divided by nonvanishing Delta.
- Cox field proofs use ring-hom extensionality, polynomial finite-sum evaluation, coefficient comparison,
  and Nat modular equivalence. The new bundled modular-function statements remain unchanged.
- Cox ModularFunction uses polynomial composition for holomorphy and direct integer order arithmetic.
  LevelJ uses natAbs multiplicativity for its determinant product.
- The q-expansion computation link shares its existing fold/sum lemma and applies homomorphism laws directly;
  it retains the original computational definitions and native-evaluation trust documentation.
- Complex lattice uniqueness applies iterated-derivative rules directly and compares sums of equal local
  power series. Its mathematical proof, hypotheses and conclusions are unchanged.
- NormNumI.split_mul, previously admitted, is now proved by Complex.ext and the multiplication formulas.

## Protection and scope

Existing public declaration signatures are unchanged (lexical signature audit plus Lean compilation).
The three new core helpers are private: `linear_bigO_of_norm_le`, `delta_eq_discriminant`,
`eventually_arg_pow`. Existing mathematical definitions are unchanged. No axioms, native proofs,
resource-limit increases, or profiler scaffolding were introduced.

Copyright/module/doc comments are preserved. Five removed block comments were obsolete attempted
proofs beside the five core admissions now filled; the actual proofs replace those attempts. Mathematical
comments in the lattice uniqueness proof remain next to their shortened derivations.

No rename was needed. The concise ModularFunctions core, import facades, q-expansion tactic engine,
and coefficient examples were inspected and retained where shortening would only obscure the API.

## Verification

All root files passed direct source compilation and profiling. The final source of Eisenstein
was checked again after filling its coefficient lemma. See `root-profiler.json` and `verification.md`
for the separate final cumulative build, axiom audit, and independent review results.
