# Broader proof cleanup — 2026-09-21

Baseline: `/tmp/xyin-proof-cleanup-before/XYin`, captured **after** the earlier structural refactor.
This pass addresses proof bodies across the existing project; earlier migration/splitting changes are not counted again.

Inspected 83 Lean files. Changed 56; retained 27 after inspection.
Source lines: 23837 → 19649 (net −4188).
Normalized theorem-body comparison records 353 changed existing lemma/theorem bodies.
Lines include code, comments, and spacing; the line reduction is not presented as a proof-performance metric.
Active `sorry` tokens: 15 → 1.

## Main outcomes

- Reused pinned mathlib derivative, Eisenstein/Fourier, discriminant, dimension, infinite-sum/product, and polynomial APIs.
- Consolidated repeated Laurent coefficient, imaginary-axis restriction, logarithm-argument and j-holomorphy proofs.
- Simplified Cox matrix, sublattice, polynomial-descent and modular-function field proofs while preserving the new bundled modular-function API.
- Filled 14 existing admissions: 3 q-expansion lemmas, complex multiplication, the E4/E6 constant coefficient, and 9 dimension/discriminant results.
- Removed 6 unused private helpers (including 5 identified in independent review). No public declaration was removed or changed in type.
- Preserved mathematical definitions and data; 8 bundled-definition proof fields were simplified.

## Per-file coverage

| File | Before | After | Net reduction | Result |
| --- | ---: | ---: | ---: | --- |
| `XYin/Basic.lean` | 1 | 1 | 0 | Inspected; retained |
| `XYin/PhD/Cox/Arithmetic.lean` | 359 | 346 | 13 | Proof changes |
| `XYin/PhD/Cox/CoxMatrices/Basic.lean` | 897 | 822 | 75 | Proof changes |
| `XYin/PhD/Cox/CoxMatrices/Cardinality.lean` | 299 | 278 | 21 | Proof changes |
| `XYin/PhD/Cox/CoxMatrices/LaurentExpansion.lean` | 438 | 354 | 84 | Proof changes |
| `XYin/PhD/Cox/CoxMatrices.lean` | 14 | 14 | 0 | Inspected; retained |
| `XYin/PhD/Cox/CyclicSublattice/Classification.lean` | 423 | 370 | 53 | Proof changes |
| `XYin/PhD/Cox/CyclicSublattice.lean` | 671 | 541 | 130 | Proof changes |
| `XYin/PhD/Cox/DiagonalLaurent.lean` | 370 | 293 | 77 | Proof changes |
| `XYin/PhD/Cox/FormalCoxProduct.lean` | 272 | 228 | 44 | Proof changes |
| `XYin/PhD/Cox/HermiteNormalForm.lean` | 473 | 408 | 65 | Proof changes |
| `XYin/PhD/Cox/Kronecker.lean` | 793 | 771 | 22 | Proof changes |
| `XYin/PhD/Cox/KroneckerFrobenius.lean` | 241 | 233 | 8 | Proof changes |
| `XYin/PhD/Cox/LatticeJ.lean` | 691 | 632 | 59 | Proof changes |
| `XYin/PhD/Cox/LaurentPolynomialEvaluation.lean` | 176 | 151 | 25 | Proof changes |
| `XYin/PhD/Cox/LevelThree.lean` | 878 | 858 | 20 | Proof changes |
| `XYin/PhD/Cox/ModularFunction/CuspData.lean` | 154 | 154 | 0 | Inspected; retained |
| `XYin/PhD/Cox/ModularFunction/LevelJ.lean` | 331 | 329 | 2 | Proof changes |
| `XYin/PhD/Cox/ModularFunction.lean` | 449 | 439 | 10 | Proof changes |
| `XYin/PhD/Cox/ModularFunctionField.lean` | 197 | 186 | 11 | Proof changes |
| `XYin/PhD/Cox/ModularPolynomial/AnalyticSupport.lean` | 106 | 96 | 10 | Proof changes |
| `XYin/PhD/Cox/ModularPolynomial/Construction.lean` | 445 | 379 | 66 | Proof changes |
| `XYin/PhD/Cox/ModularPolynomial/IntegralDescent.lean` | 372 | 305 | 67 | Proof changes |
| `XYin/PhD/Cox/ModularPolynomial/Interpolation.lean` | 649 | 498 | 151 | Proof changes |
| `XYin/PhD/Cox/ModularPolynomial/Irreducibility.lean` | 158 | 141 | 17 | Proof changes |
| `XYin/PhD/Cox/ModularPolynomial.lean` | 16 | 16 | 0 | Inspected; retained |
| `XYin/PhD/Cox/Section11BC.lean` | 22 | 22 | 0 | Inspected; retained |
| `XYin/PhD/Cox/SingularModuli.lean` | 250 | 238 | 12 | Proof changes |
| `XYin/PhD/Cox/SymmetricCubicLaurent.lean` | 452 | 391 | 61 | Proof changes |
| `XYin/PhD/Cox/UpperHalfPlaneFunctionField.lean` | 293 | 264 | 29 | Proof changes |
| `XYin/PhD/IntegralPowerSeries/IntegralPowerSeries.lean` | 240 | 229 | 11 | Proof changes |
| `XYin/PhD/LaurentQExpansion/Algebra.lean` | 451 | 439 | 12 | Proof changes |
| `XYin/PhD/LaurentQExpansion/LaurentQExpansion.lean` | 810 | 706 | 104 | Proof changes |
| `XYin/PhD/ModularFunctions/Basic.lean` | 97 | 97 | 0 | Inspected; retained |
| `XYin/PhD/ModularFunctions/Congruence.lean` | 150 | 150 | 0 | Inspected; retained |
| `XYin/PhD/ModularFunctions/CuspGrowth.lean` | 114 | 114 | 0 | Inspected; retained |
| `XYin/PhD/ModularFunctions/CuspPeriod.lean` | 62 | 62 | 0 | Inspected; retained |
| `XYin/PhD/ModularFunctions/Cusps.lean` | 88 | 88 | 0 | Inspected; retained |
| `XYin/PhD/ModularFunctions/FieldAction.lean` | 149 | 149 | 0 | Inspected; retained |
| `XYin/PhD/ModularFunctions/GrowthAtCusp.lean` | 73 | 73 | 0 | Inspected; retained |
| `XYin/PhD/ModularFunctions/JInvariant.lean` | 68 | 57 | 11 | Proof changes |
| `XYin/PhD/ModularFunctions/MeromorphicField.lean` | 662 | 658 | 4 | Proof changes |
| `XYin/PhD/ModularFunctions/NormalFormGrowth.lean` | 66 | 66 | 0 | Inspected; retained |
| `XYin/PhD/ModularFunctions/NormalFormSlash.lean` | 97 | 97 | 0 | Inspected; retained |
| `XYin/PhD/Modularforms/AtImInfty.lean` | 27 | 27 | 0 | Inspected; retained |
| `XYin/PhD/Modularforms/BigO.lean` | 149 | 61 | 88 | Proof changes |
| `XYin/PhD/Modularforms/Delta.lean` | 598 | 408 | 190 | Proof changes |
| `XYin/PhD/Modularforms/DimensionFormulas.lean` | 509 | 200 | 309 | Proof changes |
| `XYin/PhD/Modularforms/E2.lean` | 181 | 109 | 72 | Proof changes |
| `XYin/PhD/Modularforms/Eisenstein.lean` | 940 | 692 | 248 | Proof changes |
| `XYin/PhD/Modularforms/Eisensteinqexpansions.lean` | 343 | 155 | 188 | Proof changes |
| `XYin/PhD/Modularforms/ForMathlib_Cusps.lean` | 21 | 21 | 0 | Inspected; retained |
| `XYin/PhD/Modularforms/IsCuspForm.lean` | 181 | 152 | 29 | Proof changes |
| `XYin/PhD/Modularforms/NormNumI.lean` | 207 | 205 | 2 | Proof changes |
| `XYin/PhD/Modularforms/ResToImagAxis.lean` | 480 | 403 | 77 | Proof changes |
| `XYin/PhD/Modularforms/SlashActionAuxil.lean` | 310 | 287 | 23 | Proof changes |
| `XYin/PhD/Modularforms/Summability/Basic.lean` | 363 | 206 | 157 | Proof changes |
| `XYin/PhD/Modularforms/Summability/QExpansion.lean` | 748 | 296 | 452 | Proof changes |
| `XYin/PhD/Modularforms/Summability/Reciprocal.lean` | 688 | 297 | 391 | Proof changes |
| `XYin/PhD/Modularforms/clog_arg_lems.lean` | 180 | 94 | 86 | Proof changes |
| `XYin/PhD/Modularforms/csqrt.lean` | 79 | 57 | 22 | Proof changes |
| `XYin/PhD/Modularforms/equivs.lean` | 46 | 46 | 0 | Inspected; retained |
| `XYin/PhD/Modularforms/eta.lean` | 172 | 81 | 91 | Proof changes |
| `XYin/PhD/Modularforms/exp_lems.lean` | 36 | 29 | 7 | Proof changes |
| `XYin/PhD/Modularforms/iteratedderivs.lean` | 169 | 72 | 97 | Proof changes |
| `XYin/PhD/Modularforms/multipliable_lems.lean` | 149 | 81 | 68 | Proof changes |
| `XYin/PhD/Modularforms/qExpansion_lems.lean` | 205 | 113 | 92 | Proof changes |
| `XYin/PhD/Modularforms/summable_lems.lean` | 16 | 16 | 0 | Inspected; retained |
| `XYin/PhD/Modularforms/tsumderivWithin.lean` | 138 | 138 | 0 | Inspected; retained |
| `XYin/PhD/Modularforms/upperhalfplane.lean` | 21 | 17 | 4 | Proof changes |
| `XYin/PhD/Tactic2/LaurentQExpSimpTests.lean` | 63 | 63 | 0 | Inspected; retained |
| `XYin/PhD/Tactic2/QExpSimpAttr.lean` | 3 | 3 | 0 | Inspected; retained |
| `XYin/PhD/Tactic2/QExpSimpConditionTests.lean` | 55 | 55 | 0 | Inspected; retained |
| `XYin/PhD/Tactic2/qexp_simp.lean` | 207 | 207 | 0 | Inspected; retained |
| `XYin/PhD/jFunction/Deltaqexpansions.lean` | 337 | 300 | 37 | Proof changes |
| `XYin/PhD/jFunction/jInvariantLink.lean` | 81 | 81 | 0 | Inspected; retained |
| `XYin/PhD/jFunction/jLevelN.lean` | 212 | 193 | 19 | Proof changes |
| `XYin/PhD/jFunction/jfunction.lean` | 602 | 504 | 98 | Proof changes |
| `XYin/PhD/jFunction/qexp_coeffs.lean` | 163 | 163 | 0 | Inspected; retained |
| `XYin/PhD/qExpansion_tactic/Examples.lean` | 65 | 65 | 0 | Inspected; retained |
| `XYin/PhD/qExpansion_tactic/Qj.lean` | 304 | 304 | 0 | Inspected; retained |
| `XYin/PhD/qExpansion_tactic/link.lean` | 438 | 408 | 30 | Proof changes |
| `XYin/uniqueness.lean` | 334 | 297 | 37 | Proof changes |

## Evidence

See `verification.md` for cumulative build and axiom results, `independent-review.md` for the fresh review,
`source-gates.json` for signature/trust checks, and the batch reports in this directory for declaration-level changes and profiling.
The remaining admission is `dim_gen_cong_levels` in `DimensionFormulas.lean`; it was not silently assumed solved.
