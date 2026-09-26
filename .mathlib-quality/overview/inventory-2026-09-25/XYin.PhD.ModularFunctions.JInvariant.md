# Inventory: XYin/PhD/ModularFunctions/JInvariant.lean  (57 lines)

Bundles the project's `j`-function (XYin/PhD/jFunction/jfunction.lean) as a level-one `ModularFunction 𝒮ℒ`: holomorphy gives the field element via `MeromorphicField.ofHolomorphic`, and the existing meromorphy of `cuspFunction 1 j` at 0 gives exponential growth at ∞, transported to all SL₂(ℤ)-cusps.

## Declarations

### `theorem ModularFunction.j_mdifferentiable`
- **Type**: `MDiff j`
- **What**: `j` is holomorphic on ℍ.
- **How**: `exact _root_.j_mdifferentiable`.
- **Hypotheses**: none.
- **Uses from project**: `j`, `_root_.j_mdifferentiable` (jfunction.lean:54)
- **Used by**: `jModularFunction`
- **Visibility**: public
- **Lines**: 23–25
- **Notes**: pure re-export of the root lemma under a second name; junk.

### `theorem ModularFunction.j_periodic`
- **Type**: `Periodic (j ∘ UpperHalfPlane.ofComplex) 1`
- **What**: `j` has period 1 (as a function on ℂ via `ofComplex`).
- **How**: builds an ad-hoc `SlashInvariantForm 𝒮ℒ 0` from `j_slash_invariant` and applies mathlib `SlashInvariantFormClass.periodic_comp_ofComplex` with `1 ∈ 𝒮ℒ.strictPeriods` by `simp`.
- **Hypotheses**: none.
- **Uses from project**: `j`, `j_slash_invariant` (jfunction.lean:60)
- **Used by**: `j_isOfExponentialGrowth`
- **Visibility**: public
- **Lines**: 27–31, proof body ≈ 3 lines
- **Notes**: used by Cox/Kronecker, Cox/DiagonalLaurent, Cox/ModularFunction/LevelJ, Cox/CoxMatrices/LaurentExpansion. The inline `SlashInvariantForm` (29–30) duplicates `jModularFunction.slash_action_eq'` (43–45).

### `theorem ModularFunction.j_isOfExponentialGrowth`
- **Type**: `IsOfExponentialGrowth j`
- **What**: `j` grows at most exponentially at ∞.
- **How**: `isOfExponentialGrowth_of_meromorphicAt_cuspFunction` (CuspGrowth.lean) with `j_periodic` and `j_cuspFunction_meromorphicAt`.
- **Hypotheses**: none.
- **Uses from project**: `IsOfExponentialGrowth`, `isOfExponentialGrowth_of_meromorphicAt_cuspFunction`, `j_periodic`, `j_cuspFunction_meromorphicAt` (jfunction.lean:455)
- **Used by**: `jModularFunction`
- **Visibility**: public
- **Lines**: 33–36
- **Notes**: —

### `def jModularFunction`
- **Type**: `ModularFunction 𝒮ℒ`
- **What**: the modular invariant as a bundled level-one modular function.
- **How**: `toFun := j`; invariance from `j_slash_invariant`; `meromorphic'` from `MeromorphicField.ofHolomorphic`/`toFun_ofHolomorphic`; growth at a cusp `c`: `isCusp_SL2Z_iff'` gives `c = γ • ∞`, `OnePoint.isOfExponentialGrowthAt_iff` reduces to growth of `j ∣[0] γ = j`.
- **Hypotheses**: none.
- **Uses from project**: `ModularFunction`, `j`, `j_slash_invariant`, `MeromorphicField.ofHolomorphic`, `MeromorphicField.toFun_ofHolomorphic`, `ModularFunction.j_mdifferentiable`, `OnePoint.isOfExponentialGrowthAt_iff`, `IsOfExponentialGrowth`, `ModularFunction.j_isOfExponentialGrowth`
- **Used by**: `coe_jModularFunction`
- **Visibility**: public
- **Lines**: 40–54, body ≈ 13 lines
- **Notes**: root namespace (not `ModularFunction.`); used by Cox/UpperHalfPlaneFunctionField and Cox/ModularFunction/CuspData.

### `theorem coe_jModularFunction`
- **Type**: `(jModularFunction : ℍ → ℂ) = j`
- **What**: the underlying function is `j`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `jModularFunction`, `j`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 56–57
- **Notes**: `@[simp]`; unused project-wide.

## File Summary
- Total declarations: 5 (1 def, 4 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): none
- Unused declarations (not used by anything in this file): `coe_jModularFunction` (unused project-wide)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations
### Mathlib API candidates
- `j_periodic` (27): uses `SlashInvariantFormClass.periodic_comp_ofComplex` (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:120`) correctly; mathlib has no `j`.
- `jModularFunction.bdd_at_cusps'` (48–54): reduction "cusp of SL₂(ℤ) ⇒ `γ • ∞`" via `isCusp_SL2Z_iff'` (`Mathlib/NumberTheory/ModularForms/Cusps.lean:133`) is the pattern mathlib packages as `isBoundedAt_iff_exists_SL2Z` (`BoundedAtCusp.lean:94`) for boundedness; the exponential-growth analogue is missing (see GrowthAtCusp.md).
### Missing API / repeated patterns
- `rintro _ ⟨γ, rfl⟩; exact j_slash_invariant γ` appears at 30 and 44–45; a `jSlashInvariantForm : SlashInvariantForm 𝒮ℒ 0` (or using `jModularFunction.toSlashInvariantForm` in `j_periodic`) removes one copy.
- The `bdd_at_cusps'` proof skeleton (49–54) is repeated in Congruence.lean:126–140 (`ofGamma0CuspData`) and Cox/ModularPolynomial/Construction.lean:270–273; a lemma `OnePoint.isOfExponentialGrowthAt_of_forall_SL2Z (h : ∀ γ : SL(2,ℤ), IsOfExponentialGrowth (f ∣[0] γ)) (hc : IsCusp c 𝒮ℒ) : c.IsOfExponentialGrowthAt f` collapses all three.
### Junk candidates
- `ModularFunction.j_mdifferentiable` (23–25): duplicate name for `_root_.j_mdifferentiable`; replace uses at 46–47 by the root lemma and delete.
- `coe_jModularFunction` (56): unused; keep only if the `@[simp]` normal form is wanted.
- `open Complex Function UpperHalfPlane Matrix.SpecialLinearGroup` (16): `Complex` and `Matrix.SpecialLinearGroup` appear unused.
### Moral duplicates within this batch
- `j_periodic` (27–31) vs `Congruence.periodic_comp_sl2_gamma0` at `N = 1`, `γ = 1` (Congruence.lean:87) — same statement up to `Function.comp` unfolding.
### Generalization notes
- `jModularFunction.bdd_at_cusps'` only uses that `j ∣[0] γ = j` for all `γ ∈ SL(2,ℤ)` and growth at ∞; this is the general statement "an SL₂(ℤ)-invariant function with exponential growth at ∞ has exponential growth at all cusps".
