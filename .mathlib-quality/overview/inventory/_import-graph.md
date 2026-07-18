# Cross-file import graph (project-internal, Modularforms excluded)

## Layering (leaves first)

**Layer 0 (no project imports):**
- XYin/Basic.lean (stub)
- XYin/PhD/ModularFunctions/Basic.lean (empty)
- XYin/PhD/IntegralPowerSeries/IntegralPowerSeries.lean
- XYin/PhD/Tactic2/QExpSimpAttr.lean
- XYin/uniqueness.lean
- XYin/PhD/Cox/HermiteNormalForm.lean

**IntegralPowerSeries / q-expansion foundation:**
- HasIntegralQExpansion ← IntegralPowerSeries
- LaurentQExpansion/LaurentQExpansion ← HasIntegralQExpansion
- LaurentQExpansion/Algebra ← LaurentQExpansion
- Tactic2/qexp_simp ← QExpSimpAttr
- Tactic2/QExpSimpConditionTests ← qexp_simp, jFunction/Deltaqexpansions [test]
- Tactic2/LaurentQExpSimpTests ← LaurentQExpansion [test]

**jFunction:**
- Deltaqexpansions ← IntegralPowerSeries
- jfunction ← HasIntegralQExpansion, Deltaqexpansions, LaurentQExpansion
- jLevelN ← jfunction
- jInvariantLink ← Cox/LatticeJ
- qexp_coeffs ← qExpansion_tactic/link

**qExpansion_tactic:**
- Qj (leaf w.r.t. project? imports none listed → check worker report)
- link ← jfunction, Qj
- Examples ← Qj [test/demo]

**Cox chain:**
- LatticeJ ← jfunction, uniqueness
- ModularFunction ← LatticeJ, jLevelN
- CoxMatrices/Basic ← HermiteNormalForm, ModularFunction
- CoxMatrices/Cardinality ← CoxMatrices/Basic
- CoxMatrices/LaurentExpansion ← CoxMatrices/Basic
- CoxMatrices (umbrella) ← Cardinality, LaurentExpansion
- FormalCoxProduct ← CoxMatrices
- UpperHalfPlaneFunctionField ← CoxMatrices
- ModularPolynomial/AnalyticSupport ← CoxMatrices/Basic
- ModularPolynomial/Construction ← FormalCoxProduct, AnalyticSupport
- ModularPolynomial/Interpolation ← Construction, UpperHalfPlaneFunctionField
- ModularPolynomial/Irreducibility ← Construction, UpperHalfPlaneFunctionField
- ModularPolynomial/IntegralDescent ← Construction, LaurentQExpansion/Algebra
- ModularPolynomial (umbrella) ← Construction, IntegralDescent, Interpolation, Irreducibility
- DiagonalLaurent ← ModularPolynomial
- LaurentPolynomialEvaluation (leaf? check worker report)
- Kronecker ← DiagonalLaurent, LaurentPolynomialEvaluation
- KroneckerFrobenius ← Kronecker
- SymmetricCubicLaurent ← LaurentPolynomialEvaluation, ModularPolynomial
- LevelThree ← KroneckerFrobenius, SymmetricCubicLaurent, qExpansion_tactic/link
- CyclicSublattice ← HermiteNormalForm, LatticeJ
- CyclicSublattice/Classification ← CyclicSublattice, ModularPolynomial
- Arithmetic ← Classification, LevelThree
- SingularModuli ← Arithmetic
- ModularFunctionField ← ModularPolynomial/Interpolation
- Section11BC (umbrella) ← Arithmetic, ModularFunctionField, SingularModuli

**Root:** XYin.lean imports Basic, IntegralPowerSeries both, LaurentQExpansion/LaurentQExpansion (NOT Algebra directly — reachable transitively via Cox), ModularFunctions/Basic (empty), Tactic2 all, Section11BC, jFunction all, qExpansion_tactic all.

## Orphans / oddities
- **ScratchGS.lean**: imports Cox/LatticeJ; nothing imports it; not in root. Scratch file — junk candidate.
- **uniqueness.lean**: reachable only via Cox/LatticeJ. Placed at XYin/ root — odd location.
- Test files (Tactic2/*Tests, qExpansion_tactic/Examples) are imported by the root XYin.lean — mathlib convention would put tests outside the library root.
