# Inventory: XYin/PhD/Cox/Section11BC.lean  (22 lines)

Umbrella module for Cox, Chapter 11, Sections B–C: it only imports `XYin.PhD.Cox.Arithmetic`,
`XYin.PhD.Cox.ModularFunctionField` and `XYin.PhD.Cox.SingularModuli` and carries a module docstring.
It is the single Cox entry point of `XYin.lean` (line 33).

## Declarations

(none — the file contains three `import` lines and a `/-! … -/` docstring; the anti-skim grep count is 0)

## File Summary
- Total declarations: 0 (0 defs, 0 lemmas/theorems, 0 instances, 0 other)
- Key API: none
- Unused declarations: none
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations (evidence for the analysis phases)

### Mathlib API candidates
- n/a (no declarations).

### Missing API / repeated patterns
- **Reachability (checked by a script following `import XYin.…` lines transitively from `Section11BC`)**: all 29 modules under `XYin/PhD/Cox/` (including the five `ModularPolynomial/*`, three `CoxMatrices/*`, `CyclicSublattice/Classification`, `ModularFunction/CuspData`, `ModularFunction/LevelJ`) are reachable. **Cox files NOT transitively imported: none.** The closure also pulls in 22 non-Cox modules (`IntegralPowerSeries.IntegralPowerSeries`, `LaurentQExpansion.{Algebra,LaurentQExpansion}`, `ModularFunctions.{Basic,Congruence,CuspGrowth,CuspPeriod,Cusps,FieldAction,GrowthAtCusp,JInvariant,MeromorphicField,NormalFormGrowth,NormalFormSlash}`, `Modularforms.{Eisenstein,ForMathlib_Cusps}`, `jFunction.{Deltaqexpansions,jLevelN,jfunction}`, `qExpansion_tactic.{Qj,link}`, `XYin.uniqueness`), i.e. 51 project modules in total.
- The three direct imports are the minimal set: `Arithmetic` (→ LevelThree, CyclicSublattice.Classification, …), `ModularFunctionField` (→ ModularPolynomial.Interpolation, UpperHalfPlaneFunctionField, …), `SingularModuli` (→ Arithmetic). `ModularFunctionField` is *not* reachable from the other two, so it is genuinely needed.

### Junk candidates
- Docstring (L13–19) is incomplete/stale relative to the imported content: it lists "Lemma 11.10 and Theorem 11.9; Lemma 11.11 and (11.12)–(11.17); Theorem 11.18(i)–(v) and (11.22); Theorem 11.23 and Lemma 11.24; lattice `j` classification and HNF API" but omits the singular-moduli result (`Cox.singularModulus_isIntegral`, Report Theorem 5.9 / Cox Theorem 11.1 direction) that `SingularModuli` contributes, and the Kronecker congruence / Frobenius material (Kronecker.lean, KroneckerFrobenius.lean — where `theorem_11_18_v` actually lives, KroneckerFrobenius.lean:221). Numbered declarations that exist in the closure: `theorem_11_9_i` (ModularFunction.lean:431), `theorem_11_9_ii` (ModularFunctionField.lean:176), `theorem_11_9_ii_pointwise` (Interpolation.lean:488), `theorem_11_18_i/ii/iii/iv_leadingCoeff/iv_degree` (Arithmetic.lean), `theorem_11_18_v` (KroneckerFrobenius.lean:221), `theorem_11_23` (Classification.lean:345). No declaration named `lemma_11_10`, `lemma_11_11` or `lemma_11_24` exists (grep `(theorem|lemma)_11_`), so the docstring's item names are not backed by same-named declarations.

### Moral duplicates within this batch
- none.

### Generalization notes
- none.
