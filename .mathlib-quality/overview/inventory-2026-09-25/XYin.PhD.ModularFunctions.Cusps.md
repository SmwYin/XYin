# Inventory: XYin/PhD/ModularFunctions/Cusps.lean  (88 lines)

Assembles the previous files: for a function in meromorphic normal form on ℍ, exponential growth (`IsOfExponentialGrowth`) is equivalent to meromorphy of `cuspFunction h f` at 0 for any positive period `h` (using NormalFormGrowth for holomorphy high in ℍ and NormalFormSlash to keep normal form under the slash action). Defines the cusp-level predicate `OnePoint.IsMeromorphicAt` and proves, for slash-invariant forms on discrete `±1`-determinant groups, `IsOfExponentialGrowthAt c f ↔ IsMeromorphicAt c f` (periods from CuspPeriod).

## Declarations

### `theorem UpperHalfPlane.isOfExponentialGrowth_iff_meromorphicAt_cuspFunction_of_meromorphicNFOn`
- **Type**: `{f} (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet) {h} (hh : 0 < h) (hper : Periodic (f ∘ ofComplex) h) : IsOfExponentialGrowth f ↔ MeromorphicAt (cuspFunction h f) 0`
- **What**: for normal-form functions the holomorphy-high-in-ℍ hypothesis of `isOfExponentialGrowth_iff_meromorphicAt_cuspFunction` is automatic from the growth bound.
- **How**: (→) `eventually_mdifferentiableAt_of_meromorphicNFOn_of_exponential_bound` supplies `hfhol`, then CuspGrowth's iff; (←) `isOfExponentialGrowth_of_meromorphicAt_cuspFunction`.
- **Hypotheses**: normal form on ℍ, `h > 0`, `h`-periodic.
- **Uses from project**: `isOfExponentialGrowth_iff_meromorphicAt_cuspFunction`, `eventually_mdifferentiableAt_of_meromorphicNFOn_of_exponential_bound`, `isOfExponentialGrowth_of_meromorphicAt_cuspFunction`, `IsOfExponentialGrowth`
- **Used by**: `OnePoint.isOfExponentialGrowthAt_iff_meromorphicAt_cuspFunction`
- **Visibility**: public
- **Lines**: 25–33, proof body ≈ 3 lines
- **Notes**: —

### `def OnePoint.IsMeromorphicAt`
- **Type**: `(c : OnePoint ℝ) (f : ℍ → ℂ) : Prop := ∀ g : GL (Fin 2) ℝ, g • ∞ = c → ∃ h : ℝ, 0 < h ∧ Periodic ((f ∣[(0:ℤ)] g) ∘ ofComplex) h ∧ MeromorphicAt (cuspFunction h (f ∣[(0:ℤ)] g)) 0`
- **What**: `f` is meromorphic at the cusp `c`: every scaling transform is periodic with some positive period and its cusp function is meromorphic at 0.
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `isOfExponentialGrowthAt_iff_isMeromorphicAt`
- **Visibility**: public
- **Lines**: 39–44
- **Notes**: no mathlib analogue (searched `IsMeromorphicAt`, `MeromorphicAtCusp`, `meromorphic` in `Mathlib/NumberTheory/ModularForms/{QExpansion,Basic}.lean`). Unlike `IsOfExponentialGrowthAt`, it has no `smul_iff`/`_iff` (one-matrix) lemmas; those follow only via the growth equivalence. Used by Basic.lean:85.

### `theorem OnePoint.isOfExponentialGrowthAt_iff_meromorphicAt_cuspFunction`
- **Type**: `{c} {f} (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet) {g} (hg : g • ∞ = c) {h} (hh : 0 < h) (hper : Periodic ((f ∣[(0:ℤ)] g) ∘ ofComplex) h) : c.IsOfExponentialGrowthAt f ↔ MeromorphicAt (cuspFunction h (f ∣[(0:ℤ)] g)) 0`
- **What**: growth at the cusp `c` ⇔ meromorphy of the cusp function in any positive-period chart `g`.
- **How**: `isOfExponentialGrowthAt_iff hg` then the previous theorem applied to `f ∣[0] g`, whose normal form comes from `meromorphicNFOn_slash_zero`.
- **Hypotheses**: normal form; chart `g`; period `h > 0`.
- **Uses from project**: `OnePoint.isOfExponentialGrowthAt_iff`, `isOfExponentialGrowth_iff_meromorphicAt_cuspFunction_of_meromorphicNFOn`, `meromorphicNFOn_slash_zero`, `OnePoint.IsOfExponentialGrowthAt`
- **Used by**: `isOfExponentialGrowthAt_iff_isMeromorphicAt`
- **Visibility**: public
- **Lines**: 46–55, proof body ≈ 3 lines
- **Notes**: used by Basic.lean:94.

### `theorem OnePoint.isOfExponentialGrowthAt_iff_isMeromorphicAt`
- **Type**: `{Γ} [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] (f : SlashInvariantForm Γ 0) (hf : MeromorphicNFOn ((f : ℍ → ℂ) ∘ ofComplex) upperHalfPlaneSet) {c} (hc : IsCusp c Γ) : c.IsOfExponentialGrowthAt f ↔ c.IsMeromorphicAt f`
- **What**: for a normal-form slash-invariant form, growth at a cusp ⇔ meromorphy at that cusp.
- **How**: (→) for each chart `g`, `exists_pos_period_at_cusp` gives a period and the previous iff gives meromorphy; (←) `isOfExponentialGrowth_of_meromorphicAt_cuspFunction` on the given chart data.
- **Hypotheses**: `Γ` discrete, determinants `±1`; `c` a cusp; normal form.
- **Uses from project**: `OnePoint.IsMeromorphicAt`, `OnePoint.IsOfExponentialGrowthAt`, `SlashInvariantForm.exists_pos_period_at_cusp`, `isOfExponentialGrowthAt_iff_meromorphicAt_cuspFunction`, `isOfExponentialGrowth_of_meromorphicAt_cuspFunction`
- **Used by**: `SlashInvariantForm.exponential_growth_at_cusps_iff`
- **Visibility**: public
- **Lines**: 57–72, proof body ≈ 8 lines
- **Notes**: used by Basic.lean:86.

### `theorem SlashInvariantForm.exponential_growth_at_cusps_iff`
- **Type**: `{Γ} [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] (f : SlashInvariantForm Γ 0) (hf : MeromorphicNFOn …) : (∀ c, IsCusp c Γ → c.IsOfExponentialGrowthAt f) ↔ ∀ c, IsCusp c Γ → c.IsMeromorphicAt f`
- **What**: the all-cusps versions are equivalent.
- **How**: `forall_congr'` twice over the previous theorem.
- **Hypotheses**: as above.
- **Uses from project**: `OnePoint.isOfExponentialGrowthAt_iff_isMeromorphicAt`, `OnePoint.IsMeromorphicAt`, `OnePoint.IsOfExponentialGrowthAt`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 78–86, proof body ≈ 2 lines
- **Notes**: unused project-wide; one-line wrapper. `by exact` could be a term.

## File Summary
- Total declarations: 5 (1 def, 4 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): none
- Unused declarations (not used by anything in this file): `exponential_growth_at_cusps_iff` (unused project-wide)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations
### Mathlib API candidates
- No mathlib notion of meromorphy at a cusp; the closest mathlib material is `ModularFormClass.bdd_at_infty`/`CuspFormClass.zero_at_infty` (`Mathlib/NumberTheory/ModularForms/Basic.lean:734,738`) and the q-expansion API (`QExpansion.lean`: `differentiableAt_cuspFunction`, `analyticAt_cuspFunction_zero`, `hasFPowerSeriesOnBall_cuspFunction`). The equivalence proved here (growth ⇔ meromorphic q-expansion for normal-form functions) is the meromorphic counterpart of mathlib's "bounded ⇔ holomorphic cusp function" (`Function.Periodic.boundedAtFilter_cuspFunction`, `Periodic.lean:192`; `differentiableAt_cuspFunction_zero`, `:202`) and is a plausible upstream target once `IsOfExponentialGrowth` is in `IsBigO` form.
### Missing API / repeated patterns
- `OnePoint.IsMeromorphicAt` lacks `smul_iff`, `infty_iff`, `_iff` (chart-independence) — currently only obtainable through `isOfExponentialGrowthAt_iff_isMeromorphicAt` under group hypotheses. Since the period-`h` cusp function determines the period-`mh` one, chart independence is provable directly.
- `IsMeromorphicAt` quantifies an existential period inside a `∀ g`; a bundled `MeromorphicAtCusp c f` structure with chosen period (`Γ'.strictWidthInfty`) would match the mathlib `qExpansion` style.
### Junk candidates
- `SlashInvariantForm.exponential_growth_at_cusps_iff` (78–86): unused; `Basic.meromorphic_at_cusps` covers the pointwise form (also unused).
### Moral duplicates within this batch
- `isOfExponentialGrowth_iff_meromorphicAt_cuspFunction_of_meromorphicNFOn` (25) is `CuspGrowth.isOfExponentialGrowth_iff_meromorphicAt_cuspFunction` (83) with one hypothesis discharged; both are kept, which is reasonable.
### Generalization notes
- All results are weight 0 because `IsOfExponentialGrowthAt`/`meromorphicNFOn_slash_zero` are; both generalise to weight `k` (see GrowthAtCusp.md, NormalFormSlash.md), which would give "meromorphic modular forms of weight k".
