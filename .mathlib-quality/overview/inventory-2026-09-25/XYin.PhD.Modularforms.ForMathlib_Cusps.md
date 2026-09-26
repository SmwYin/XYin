# Inventory: XYin/PhD/Modularforms/ForMathlib_Cusps.lean  (21 lines)

Two wrappers reducing "vanishes / is bounded at a cusp `c` of an arithmetic subgroup `𝒢`" to "vanishes / is bounded at i∞ after slashing by every `A ∈ 𝒮ℒ`", by combining mathlib's `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z` with `OnePoint.isZeroAt_iff_forall_SL2Z` / `isBoundedAt_iff_forall_SL2Z`. Genuinely used: IsCuspForm.lean (×2), Delta.lean:189/235, Cox/LatticeJ.lean:565. Mathlib itself performs this two-step reduction inline in several places but has no named lemma for it.

## Declarations

### `theorem zero_at_cusps_of_zero_at_infty`
- **Type**: `{f : ℍ → ℂ} {c : OnePoint ℝ} {k : ℤ} {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] (hc : IsCusp c 𝒢) (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsZeroAtImInfty (f ∣[k] A)) : c.IsZeroAt f k`
- **What**: If `f ∣[k] A → 0` at i∞ for every `A ∈ SL(2,ℤ)`, then `f` vanishes at every cusp `c` of an arithmetic group `𝒢`.
- **How**: `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z` (`Mathlib/NumberTheory/ModularForms/Cusps.lean:147`) turns `IsCusp c 𝒢` into `IsCusp c 𝒮ℒ`; then `OnePoint.isZeroAt_iff_forall_SL2Z hc` (`Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean:116`) reduces to the `∀ γ : SL(2,ℤ), mapGL ℝ γ • ∞ = c → IsZeroAtImInfty (f ∣[k] γ)` form, discharged by `hb A ⟨A, rfl⟩`.
- **Hypotheses**: `𝒢` arithmetic, `c` a cusp of `𝒢`, slash-translates of `f` by all of `𝒮ℒ` vanish at i∞.
- **Uses from project**: []
- **Used by**: unused in file; externally IsCuspForm.lean:108/129, Delta.lean:189, Cox/LatticeJ.lean:565
- **Visibility**: public
- **Lines**: 9–14, body 2 lines
- **Notes**: mathlib does exactly these two rewrites inline in `Discriminant.lean:246`, `CuspFormSubmodule.lean:116–117`, `LevelOne/DimensionFormula.lean:69–71`, so a named lemma is a real (small) ForMathlib contribution. Hypothesis `hb` is stronger than needed (all `A ∈ 𝒮ℒ`, not just those with `A • ∞ = c`) — fine for the `Γ(1)` use cases where `f ∣[k] A = f`.

### `theorem bounded_at_cusps_of_bounded_at_infty`
- **Type**: same as above with `IsBoundedAtImInfty` / `c.IsBoundedAt f k`
- **What**: Boundedness analogue.
- **How**: identical, with `OnePoint.isBoundedAt_iff_forall_SL2Z` (`BoundedAtCusp.lean:110`).
- **Hypotheses**: as above with boundedness.
- **Uses from project**: []
- **Used by**: unused in file; externally Delta.lean:235
- **Visibility**: public
- **Lines**: 16–21, body 2 lines
- **Notes**: same remarks.

## File Summary
- Total declarations: 2 (0 defs; 2 theorems; 0 instances; 0 other)
- Key API (used by 3+ others in the file): none in-file; `zero_at_cusps_of_zero_at_infty` has 4 external call sites
- Unused declarations (not used by anything in this file): both (in-file only); both are used externally
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations

### Mathlib API candidates
- Both theorems are 2-line compositions of `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z` (`Cusps.lean:147`) and `OnePoint.isZeroAt_iff_forall_SL2Z` / `isBoundedAt_iff_forall_SL2Z` (`BoundedAtCusp.lean:116/:110`). Mathlib has no named wrapper (searched `isZeroAt_of`, `of_zero_at_infty`, `IsZeroAt.of_forall` in `BoundedAtCusp.lean`, `Cusps.lean`); since mathlib repeats the pattern inline three times, upstreaming these under `OnePoint.isZeroAt_of_forall_SL2Z_isZeroAtImInfty`-style names is reasonable. The header says "ForMathlib" and this is the one file in the batch that fits the label.
- The `𝒮ℒ`-relative form of `hb` matches mathlib's `isCusp_iff_isCusp_SL2Z`; a version quantifying only over `γ` with `γ • ∞ = c` (mathlib's own iff) is strictly stronger but the current callers all supply the uniform hypothesis.

### Missing API / repeated patterns
- Callers IsCuspForm.lean:107–111 and :128–132 repeat the same 4 lines to instantiate `hb` for `Γ(1)`-invariant `f` (`intro A ⟨A', hA'⟩; rw [slash_action_eq' …]; exact _`); a `Γ(1)`-specialised corollary `zero_at_cusps_of_zero_at_infty_of_SL_invariant (hf : ∀ γ : SL(2,ℤ), f ∣[k] γ = f) (h : IsZeroAtImInfty f)` would remove the repetition (mathlib's `isZeroAt_of_coeffZero_eq_zero`, `CuspFormSubmodule.lean:113`, is this specialised further to `a₀ = 0`).

### Junk candidates
- None; both theorems are live.

### Moral duplicates within this batch
- The two theorems are the same proof with `Zero`↔`Bounded`; against mathlib, they duplicate the inline rewrites at `Discriminant.lean:246`, `CuspFormSubmodule.lean:116–117`, `LevelOne/DimensionFormula.lean:69–71`.

### Generalization notes
- Already stated at mathlib's generality (`𝒢 : Subgroup (GL (Fin 2) ℝ)` `[𝒢.IsArithmetic]`); the weight `k : ℤ` and `f : ℍ → ℂ` are unconstrained. The only possible strengthening is weakening `hb` to `∀ γ : SL(2,ℤ), mapGL ℝ γ • ∞ = c → …` (mathlib's iff), which is what the underlying lemmas give.
