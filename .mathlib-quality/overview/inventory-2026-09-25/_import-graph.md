# Project-internal import graph (2026-09-25)

Computed from `import` / `public import` lines. `Mathlib` column: `Mathlib` = whole-library import, else count of targeted `Mathlib.*` imports.

| Module | Imports (project) | Imported by | Mathlib |
|---|---|---|---|
| `XYin` | `Basic`, `PhD.IntegralPowerSeries.IntegralPowerSeries`, `PhD.LaurentQExpansion.LaurentQExpansion`, `PhD.ModularFunctions.Basic`, `PhD.ModularFunctions.JInvariant`, `PhD.Modularforms.AtImInfty`, `PhD.Modularforms.BigO`, `PhD.Modularforms.Delta`, `PhD.Modularforms.DimensionFormulas`, `PhD.Modularforms.E2`, `PhD.Modularforms.Eisenstein`, `PhD.Modularforms.Eisensteinqexpansions`, `PhD.Modularforms.ForMathlib_Cusps`, `PhD.Modularforms.IsCuspForm`, `PhD.Modularforms.NormNumI`, `PhD.Modularforms.ResToImagAxis`, `PhD.Modularforms.SlashActionAuxil`, `PhD.Modularforms.clog_arg_lems`, `PhD.Modularforms.csqrt`, `PhD.Modularforms.equivs`, `PhD.Modularforms.eta`, `PhD.Modularforms.exp_lems`, `PhD.Modularforms.iteratedderivs`, `PhD.Modularforms.multipliable_lems`, `PhD.Modularforms.qExpansion_lems`, `PhD.Modularforms.summable_lems`, `PhD.Modularforms.tsumderivWithin`, `PhD.Modularforms.upperhalfplane`, `PhD.Tactic2.LaurentQExpSimpTests`, `PhD.Tactic2.QExpSimpAttr`, `PhD.Tactic2.QExpSimpConditionTests`, `PhD.Tactic2.qexp_simp`, `PhD.Cox.Section11BC`, `PhD.jFunction.Deltaqexpansions`, `PhD.jFunction.jInvariantLink`, `PhD.jFunction.jLevelN`, `PhD.jFunction.jfunction`, `PhD.jFunction.qexp_coeffs`, `PhD.qExpansion_tactic.Examples`, `PhD.qExpansion_tactic.Qj`, `PhD.qExpansion_tactic.link` | — (orphan) | 0 |
| `XYin.Basic` | — | `XYin` | 0 |
| `XYin.PhD.Cox.Arithmetic` | `PhD.Cox.CyclicSublattice.Classification`, `PhD.Cox.LevelThree` | `PhD.Cox.SingularModuli`, `PhD.Cox.Section11BC` | 0 |
| `XYin.PhD.Cox.CoxMatrices` | `PhD.Cox.CoxMatrices.Cardinality`, `PhD.Cox.CoxMatrices.LaurentExpansion` | `PhD.Cox.FormalCoxProduct`, `PhD.Cox.UpperHalfPlaneFunctionField` | 0 |
| `XYin.PhD.Cox.CoxMatrices.Basic` | `PhD.Cox.HermiteNormalForm`, `PhD.Cox.ModularFunction.LevelJ` | `PhD.Cox.ModularPolynomial.AnalyticSupport`, `PhD.Cox.CoxMatrices.LaurentExpansion`, `PhD.Cox.CoxMatrices.Cardinality` | 0 |
| `XYin.PhD.Cox.CoxMatrices.Cardinality` | `PhD.Cox.CoxMatrices.Basic` | `PhD.Cox.CoxMatrices` | 3 |
| `XYin.PhD.Cox.CoxMatrices.LaurentExpansion` | `PhD.Cox.CoxMatrices.Basic` | `PhD.Cox.CoxMatrices` | 2 |
| `XYin.PhD.Cox.CyclicSublattice` | `PhD.Cox.HermiteNormalForm`, `PhD.Cox.LatticeJ` | `PhD.Cox.CyclicSublattice.Classification` | 1 |
| `XYin.PhD.Cox.CyclicSublattice.Classification` | `PhD.Cox.CyclicSublattice`, `PhD.Cox.ModularPolynomial` | `PhD.Cox.Arithmetic` | 0 |
| `XYin.PhD.Cox.DiagonalLaurent` | `PhD.Cox.LaurentPolynomialEvaluation`, `PhD.Cox.ModularPolynomial` | `PhD.Cox.Kronecker` | 0 |
| `XYin.PhD.Cox.FormalCoxProduct` | `PhD.Cox.CoxMatrices` | `PhD.Cox.ModularPolynomial.Construction` | 1 |
| `XYin.PhD.Cox.HermiteNormalForm` | — | `PhD.Cox.CyclicSublattice`, `PhD.Cox.CoxMatrices.Basic` | 5 |
| `XYin.PhD.Cox.Kronecker` | `PhD.Cox.DiagonalLaurent`, `PhD.Cox.LaurentPolynomialEvaluation` | `PhD.Cox.KroneckerFrobenius` | 1 |
| `XYin.PhD.Cox.KroneckerFrobenius` | `PhD.Cox.Kronecker` | `PhD.Cox.LevelThree` | 2 |
| `XYin.PhD.Cox.LatticeJ` | `PhD.Modularforms.ForMathlib_Cusps`, `PhD.ModularFunctions.JInvariant`, `uniqueness` | `PhD.jFunction.jInvariantLink`, `PhD.Cox.ModularFunction`, `PhD.Cox.UpperHalfPlaneFunctionField`, `PhD.Cox.CyclicSublattice` | 2 |
| `XYin.PhD.Cox.LaurentPolynomialEvaluation` | — | `PhD.Cox.Kronecker`, `PhD.Cox.SymmetricCubicLaurent`, `PhD.Cox.DiagonalLaurent`, `PhD.Cox.ModularPolynomial.IntegralDescent` | 1 |
| `XYin.PhD.Cox.LevelThree` | `PhD.Cox.KroneckerFrobenius`, `PhD.Cox.SymmetricCubicLaurent`, `PhD.qExpansion_tactic.link` | `PhD.Cox.Arithmetic` | 3 |
| `XYin.PhD.Cox.ModularFunction` | `PhD.Cox.LatticeJ`, `PhD.Cox.ModularFunction.LevelJ` | `PhD.Cox.ModularPolynomial.Construction` | 1 |
| `XYin.PhD.Cox.ModularFunction.CuspData` | `PhD.ModularFunctions.Congruence` | `PhD.Cox.ModularFunction.LevelJ` | 1 |
| `XYin.PhD.Cox.ModularFunction.LevelJ` | `PhD.Cox.ModularFunction.CuspData`, `PhD.jFunction.jLevelN` | `PhD.Cox.ModularFunction`, `PhD.Cox.CoxMatrices.Basic` | 0 |
| `XYin.PhD.Cox.ModularFunctionField` | `PhD.Cox.ModularPolynomial.Interpolation` | `PhD.Cox.Section11BC` | 1 |
| `XYin.PhD.Cox.ModularPolynomial` | `PhD.Cox.ModularPolynomial.Construction`, `PhD.Cox.ModularPolynomial.IntegralDescent`, `PhD.Cox.ModularPolynomial.Interpolation`, `PhD.Cox.ModularPolynomial.Irreducibility` | `PhD.Cox.SymmetricCubicLaurent`, `PhD.Cox.DiagonalLaurent`, `PhD.Cox.CyclicSublattice.Classification` | 0 |
| `XYin.PhD.Cox.ModularPolynomial.AnalyticSupport` | `PhD.Cox.CoxMatrices.Basic` | `PhD.Cox.ModularPolynomial.Construction` | 0 |
| `XYin.PhD.Cox.ModularPolynomial.Construction` | `PhD.Cox.FormalCoxProduct`, `PhD.Cox.ModularFunction`, `PhD.Cox.ModularPolynomial.AnalyticSupport` | `PhD.Cox.ModularPolynomial`, `PhD.Cox.ModularPolynomial.Interpolation`, `PhD.Cox.ModularPolynomial.IntegralDescent`, `PhD.Cox.ModularPolynomial.Irreducibility` | 0 |
| `XYin.PhD.Cox.ModularPolynomial.IntegralDescent` | `PhD.Cox.LaurentPolynomialEvaluation`, `PhD.Cox.ModularPolynomial.Construction`, `PhD.LaurentQExpansion.Algebra` | `PhD.Cox.ModularPolynomial` | 1 |
| `XYin.PhD.Cox.ModularPolynomial.Interpolation` | `PhD.Cox.ModularPolynomial.Construction`, `PhD.Cox.UpperHalfPlaneFunctionField` | `PhD.Cox.ModularPolynomial`, `PhD.Cox.ModularFunctionField` | 1 |
| `XYin.PhD.Cox.ModularPolynomial.Irreducibility` | `PhD.Cox.ModularPolynomial.Construction`, `PhD.Cox.UpperHalfPlaneFunctionField` | `PhD.Cox.ModularPolynomial` | 1 |
| `XYin.PhD.Cox.Section11BC` | `PhD.Cox.Arithmetic`, `PhD.Cox.ModularFunctionField`, `PhD.Cox.SingularModuli` | `XYin` | 0 |
| `XYin.PhD.Cox.SingularModuli` | `PhD.Cox.Arithmetic` | `PhD.Cox.Section11BC` | 0 |
| `XYin.PhD.Cox.SymmetricCubicLaurent` | `PhD.Cox.LaurentPolynomialEvaluation`, `PhD.Cox.ModularPolynomial` | `PhD.Cox.LevelThree` | 0 |
| `XYin.PhD.Cox.UpperHalfPlaneFunctionField` | `PhD.ModularFunctions.FieldAction`, `PhD.ModularFunctions.JInvariant`, `PhD.Cox.CoxMatrices`, `PhD.Cox.LatticeJ` | `PhD.Cox.ModularPolynomial.Interpolation`, `PhD.Cox.ModularPolynomial.Irreducibility` | 1 |
| `XYin.PhD.IntegralPowerSeries.IntegralPowerSeries` | — | `PhD.jFunction.Deltaqexpansions`, `PhD.jFunction.jfunction`, `XYin` | 1 |
| `XYin.PhD.LaurentQExpansion.Algebra` | `PhD.LaurentQExpansion.LaurentQExpansion` | `PhD.Cox.ModularPolynomial.IntegralDescent` | 1 |
| `XYin.PhD.LaurentQExpansion.LaurentQExpansion` | — | `PhD.LaurentQExpansion.Algebra`, `PhD.Tactic2.LaurentQExpSimpTests`, `PhD.jFunction.jfunction`, `XYin` | 5 |
| `XYin.PhD.ModularFunctions.Basic` | `PhD.ModularFunctions.MeromorphicField`, `PhD.ModularFunctions.Cusps` | `PhD.ModularFunctions.JInvariant`, `XYin` | 1 |
| `XYin.PhD.ModularFunctions.Congruence` | `PhD.ModularFunctions.JInvariant` | `PhD.Cox.ModularFunction.CuspData` | 0 |
| `XYin.PhD.ModularFunctions.CuspGrowth` | — | `PhD.ModularFunctions.GrowthAtCusp` | 2 |
| `XYin.PhD.ModularFunctions.CuspPeriod` | — | `PhD.ModularFunctions.Cusps` | 1 |
| `XYin.PhD.ModularFunctions.Cusps` | `PhD.ModularFunctions.GrowthAtCusp`, `PhD.ModularFunctions.NormalFormGrowth`, `PhD.ModularFunctions.NormalFormSlash`, `PhD.ModularFunctions.CuspPeriod` | `PhD.ModularFunctions.Basic` | 0 |
| `XYin.PhD.ModularFunctions.FieldAction` | `PhD.ModularFunctions.MeromorphicField` | `PhD.Cox.UpperHalfPlaneFunctionField` | 2 |
| `XYin.PhD.ModularFunctions.GrowthAtCusp` | `PhD.ModularFunctions.CuspGrowth` | `PhD.ModularFunctions.Cusps` | 1 |
| `XYin.PhD.ModularFunctions.JInvariant` | `PhD.ModularFunctions.Basic`, `PhD.jFunction.jfunction` | `PhD.ModularFunctions.Congruence`, `PhD.Cox.LatticeJ`, `PhD.Cox.UpperHalfPlaneFunctionField`, `XYin` | 0 |
| `XYin.PhD.ModularFunctions.MeromorphicField` | — | `PhD.ModularFunctions.Basic`, `PhD.ModularFunctions.FieldAction` | 6 |
| `XYin.PhD.ModularFunctions.NormalFormGrowth` | — | `PhD.ModularFunctions.Cusps` | 3 |
| `XYin.PhD.ModularFunctions.NormalFormSlash` | — | `PhD.ModularFunctions.Cusps` | 4 |
| `XYin.PhD.Modularforms.AtImInfty` | — | `PhD.Modularforms.ResToImagAxis`, `XYin` | 2 |
| `XYin.PhD.Modularforms.BigO` | — | `PhD.Modularforms.Summability.Reciprocal`, `XYin` | 4 |
| `XYin.PhD.Modularforms.Delta` | `PhD.Modularforms.SlashActionAuxil`, `PhD.Modularforms.clog_arg_lems`, `PhD.Modularforms.eta`, `PhD.Modularforms.multipliable_lems`, `PhD.Modularforms.ResToImagAxis`, `PhD.Modularforms.NormNumI`, `PhD.Modularforms.ForMathlib_Cusps` | `PhD.Modularforms.Eisensteinqexpansions`, `XYin` | 2 |
| `XYin.PhD.Modularforms.DimensionFormulas` | `PhD.Modularforms.Eisenstein` | `XYin` | 4 |
| `XYin.PhD.Modularforms.E2` | `PhD.Modularforms.SlashActionAuxil` | `PhD.Modularforms.eta`, `XYin` | 1 |
| `XYin.PhD.Modularforms.Eisenstein` | `PhD.Modularforms.Eisensteinqexpansions`, `PhD.Modularforms.IsCuspForm`, `PhD.Modularforms.Summability.Basic` | `PhD.Modularforms.DimensionFormulas`, `PhD.jFunction.Deltaqexpansions`, `XYin` | 0 |
| `XYin.PhD.Modularforms.Eisensteinqexpansions` | `PhD.Modularforms.Delta`, `PhD.Modularforms.Summability.QExpansion` | `PhD.Modularforms.Eisenstein`, `XYin` | 2 |
| `XYin.PhD.Modularforms.ForMathlib_Cusps` | — | `PhD.Modularforms.IsCuspForm`, `PhD.Modularforms.Delta`, `PhD.Cox.LatticeJ`, `XYin` | 1 |
| `XYin.PhD.Modularforms.IsCuspForm` | `PhD.Modularforms.ForMathlib_Cusps`, `PhD.Modularforms.qExpansion_lems` | `PhD.Modularforms.Eisenstein`, `XYin` | 2 |
| `XYin.PhD.Modularforms.NormNumI` | — | `PhD.Modularforms.Delta`, `XYin` | 1 |
| `XYin.PhD.Modularforms.ResToImagAxis` | `PhD.Modularforms.AtImInfty`, `PhD.Modularforms.SlashActionAuxil` | `PhD.Modularforms.Delta`, `XYin` | 2 |
| `XYin.PhD.Modularforms.SlashActionAuxil` | — | `PhD.Modularforms.ResToImagAxis`, `PhD.Modularforms.E2`, `PhD.Modularforms.Delta`, `XYin` | 5 |
| `XYin.PhD.Modularforms.Summability.Basic` | `PhD.Modularforms.exp_lems`, `PhD.Modularforms.equivs` | `PhD.Modularforms.multipliable_lems`, `PhD.Modularforms.Eisenstein`, `PhD.Modularforms.Summability.Reciprocal` | 2 |
| `XYin.PhD.Modularforms.Summability.QExpansion` | `PhD.Modularforms.Summability.Reciprocal`, `PhD.Modularforms.tsumderivWithin` | `PhD.Modularforms.Eisensteinqexpansions`, `PhD.Modularforms.summable_lems` | 1 |
| `XYin.PhD.Modularforms.Summability.Reciprocal` | `PhD.Modularforms.Summability.Basic`, `PhD.Modularforms.BigO`, `PhD.Modularforms.upperhalfplane` | `PhD.Modularforms.Summability.QExpansion` | 1 |
| `XYin.PhD.Modularforms.clog_arg_lems` | — | `PhD.Modularforms.Delta`, `XYin` | 6 |
| `XYin.PhD.Modularforms.csqrt` | — | `PhD.Modularforms.eta`, `XYin` | 8 |
| `XYin.PhD.Modularforms.equivs` | — | `PhD.Modularforms.Summability.Basic`, `XYin` | 5 |
| `XYin.PhD.Modularforms.eta` | `PhD.Modularforms.E2`, `PhD.Modularforms.csqrt`, `PhD.Modularforms.upperhalfplane` | `PhD.Modularforms.Delta`, `XYin` | 1 |
| `XYin.PhD.Modularforms.exp_lems` | — | `PhD.Modularforms.tsumderivWithin`, `PhD.Modularforms.Summability.Basic`, `XYin` | 2 |
| `XYin.PhD.Modularforms.iteratedderivs` | — | `PhD.Modularforms.tsumderivWithin`, `XYin` | 8 |
| `XYin.PhD.Modularforms.multipliable_lems` | `PhD.Modularforms.Summability.Basic` | `PhD.Modularforms.Delta`, `XYin` | 1 |
| `XYin.PhD.Modularforms.qExpansion_lems` | — | `PhD.Modularforms.IsCuspForm`, `XYin` | 5 |
| `XYin.PhD.Modularforms.summable_lems` | `PhD.Modularforms.Summability.QExpansion` | `XYin` | 0 |
| `XYin.PhD.Modularforms.tsumderivWithin` | `PhD.Modularforms.exp_lems`, `PhD.Modularforms.iteratedderivs` | `PhD.Modularforms.Summability.QExpansion`, `XYin` | 4 |
| `XYin.PhD.Modularforms.upperhalfplane` | — | `PhD.Modularforms.eta`, `PhD.Modularforms.Summability.Reciprocal`, `XYin` | 2 |
| `XYin.PhD.Tactic2.LaurentQExpSimpTests` | `PhD.LaurentQExpansion.LaurentQExpansion` | `XYin` | 0 |
| `XYin.PhD.Tactic2.QExpSimpAttr` | — | `PhD.Tactic2.qexp_simp`, `XYin` | 1 |
| `XYin.PhD.Tactic2.QExpSimpConditionTests` | `PhD.Tactic2.qexp_simp`, `PhD.jFunction.Deltaqexpansions` | `XYin` | 0 |
| `XYin.PhD.Tactic2.qexp_simp` | `PhD.Tactic2.QExpSimpAttr` | `PhD.Tactic2.QExpSimpConditionTests`, `XYin` | 2 |
| `XYin.PhD.jFunction.Deltaqexpansions` | `PhD.IntegralPowerSeries.IntegralPowerSeries`, `PhD.Modularforms.Eisenstein` | `PhD.Tactic2.QExpSimpConditionTests`, `PhD.jFunction.jfunction`, `XYin` | 1 |
| `XYin.PhD.jFunction.jInvariantLink` | `PhD.Cox.LatticeJ` | `XYin` | 1 |
| `XYin.PhD.jFunction.jLevelN` | `PhD.jFunction.jfunction` | `PhD.Cox.ModularFunction.LevelJ`, `XYin` | 0 |
| `XYin.PhD.jFunction.jfunction` | `PhD.IntegralPowerSeries.IntegralPowerSeries`, `PhD.jFunction.Deltaqexpansions`, `PhD.LaurentQExpansion.LaurentQExpansion` | `PhD.qExpansion_tactic.link`, `PhD.ModularFunctions.JInvariant`, `PhD.jFunction.jLevelN`, `XYin` | 2 |
| `XYin.PhD.jFunction.qexp_coeffs` | `PhD.qExpansion_tactic.link` | `XYin` | 0 |
| `XYin.PhD.qExpansion_tactic.Examples` | `PhD.qExpansion_tactic.Qj` | `XYin` | 0 |
| `XYin.PhD.qExpansion_tactic.Qj` | — | `PhD.qExpansion_tactic.link`, `PhD.qExpansion_tactic.Examples`, `XYin` | 3 |
| `XYin.PhD.qExpansion_tactic.link` | `PhD.jFunction.jfunction`, `PhD.qExpansion_tactic.Qj` | `PhD.jFunction.qexp_coeffs`, `PhD.Cox.LevelThree`, `XYin` | 0 |
| `XYin.uniqueness` | — | `PhD.Cox.LatticeJ` | 3 |

Reachable from root `XYin.lean`: 84/84. Not reachable: none
