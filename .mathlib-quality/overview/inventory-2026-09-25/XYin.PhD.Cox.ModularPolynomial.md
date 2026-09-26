# Inventory: XYin/PhD/Cox/ModularPolynomial.lean  (16 lines)

Umbrella module: imports `ModularPolynomial.Construction`, `.IntegralDescent`, `.Interpolation`, `.Irreducibility` and contains a 5-line module docstring. It does not import `ModularPolynomial.AnalyticSupport` directly, but `Construction.lean:8` does, so AnalyticSupport is reachable transitively.

## Declarations

(none — import-only module; the anti-skim regex count for this file is 0)

## File Summary
- Total declarations: 0 (0 defs, 0 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): none
- Unused declarations (not used by anything in this file): none
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- none (no declarations).
### Missing API / repeated patterns
- none.
### Junk candidates
- The docstring (L11–16) lists "construction, interpolation theorem, irreducibility theorem, and integral descent" and omits the analytic-support module; either add `import XYin.PhD.Cox.ModularPolynomial.AnalyticSupport` for explicitness (harmless, already transitively imported) or mention it in the docstring.
### Moral duplicates within this batch
- none.
### Generalization notes
- Reachability from `XYin.lean` (verified by grep): `XYin.lean:33` imports `XYin.PhD.Cox.Section11BC`, which imports `Cox.Arithmetic`, `Cox.ModularFunctionField`, `Cox.SingularModuli` (Section11BC.lean:6–8); `Arithmetic.lean:6` imports `Cox.CyclicSublattice.Classification`, which imports the umbrella `XYin.PhD.Cox.ModularPolynomial` (Classification.lean:7); `ModularFunctionField.lean:8` imports `ModularPolynomial.Interpolation` directly; `DiagonalLaurent.lean:12` and `SymmetricCubicLaurent.lean:7` import the umbrella. Hence all five files of this batch, including AnalyticSupport (via Construction.lean:8), are compiled into `XYin.lean`.
- Direct importers of batch files: umbrella (Construction, IntegralDescent, Interpolation, Irreducibility); Interpolation/Irreducibility/IntegralDescent each import Construction; Construction imports AnalyticSupport; ModularFunctionField imports Interpolation; Classification, DiagonalLaurent, SymmetricCubicLaurent import the umbrella. Note the module-order consequence: DiagonalLaurent.lean is downstream of IntegralDescent.lean, so the duplicated width-1/width-`m` Laurent lemmas (IntegralDescent.lean:25–70 vs DiagonalLaurent.lean:31–55,152–185,219–224) can be unified by moving general versions into LaurentQExpansion/Algebra.lean (upstream of both).
