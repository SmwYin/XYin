# Inventory: XYin/PhD/ModularFunctions/GrowthAtCusp.lean  (73 lines)

Transports `IsOfExponentialGrowth` (CuspGrowth.lean) from ∞ to arbitrary cusps `c : OnePoint ℝ`, following mathlib's `OnePoint.IsBoundedAt` (`Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`) verbatim: invariance under upper-triangular matrices, the definition `IsOfExponentialGrowthAt c f := ∀ g, g • ∞ = c → IsOfExponentialGrowth (f ∣[0] g)`, and the "one scaling matrix suffices" lemma.

## Declarations

### `lemma UpperHalfPlane.IsOfExponentialGrowth.slash`
- **Type**: `{f} {g : GL (Fin 2) ℝ} (hf : IsOfExponentialGrowth f) (hg : g 1 0 = 0) : IsOfExponentialGrowth (f ∣[(0 : ℤ)] g)`
- **What**: exponential growth is preserved by the weight-0 slash action of upper-triangular matrices (they scale `im` by `|g₀₀/g₁₁|`).
- **How**: `im (g • τ) = a · im τ` (`im_smul`, `num`, `denom`); compose the bound with `tendsto_smul_atImInfty hg`; unfold `isBoundedAtImInfty_iff` and absorb the constant `|det g|⁻¹` (`slash_apply`, `norm_σ`, `zpow_neg_one`).
- **Hypotheses**: `g` upper triangular.
- **Uses from project**: `IsOfExponentialGrowth`
- **Used by**: `isOfExponentialGrowthAt_infty_iff`
- **Visibility**: public
- **Lines**: 23–42, proof body ≈ 17 lines
- **Notes**: analogue of mathlib `IsBoundedAtImInfty.slash` (`BoundedAtCusp.lean:35`). Manual `∃ M A` bookkeeping at 36–42.

### `def OnePoint.IsOfExponentialGrowthAt`
- **Type**: `(c : OnePoint ℝ) (f : ℍ → ℂ) : Prop := ∀ g : GL (Fin 2) ℝ, g • ∞ = c → IsOfExponentialGrowth (f ∣[(0 : ℤ)] g)`
- **What**: exponential growth at the cusp `c`, tested through every scaling matrix.
- **How**: definition; copy of `OnePoint.IsBoundedAt` (`BoundedAtCusp.lean:50`) at weight 0.
- **Hypotheses**: none.
- **Uses from project**: `IsOfExponentialGrowth`
- **Used by**: `IsOfExponentialGrowthAt.smul_iff`, `isOfExponentialGrowthAt_infty_iff`, `isOfExponentialGrowthAt_iff`
- **Visibility**: public
- **Lines**: 48–51
- **Notes**: used by Basic.lean (structure field) and Cusps.lean.

### `lemma OnePoint.IsOfExponentialGrowthAt.smul_iff`
- **Type**: `IsOfExponentialGrowthAt (g • c) f ↔ IsOfExponentialGrowthAt c (f ∣[(0 : ℤ)] g)`
- **What**: equivariance under change of cusp.
- **How**: reindex the `∀ g'` by `Equiv.mulLeft g⁻¹`, `mul_smul`, `SlashAction.slash_mul`.
- **Hypotheses**: none.
- **Uses from project**: `IsOfExponentialGrowthAt`
- **Used by**: `isOfExponentialGrowthAt_iff`
- **Visibility**: public
- **Lines**: 55–60, proof body ≈ 3 lines
- **Notes**: copy of `IsBoundedAt.smul_iff` (`BoundedAtCusp.lean:58`).

### `lemma OnePoint.isOfExponentialGrowthAt_infty_iff`
- **Type**: `IsOfExponentialGrowthAt ∞ f ↔ IsOfExponentialGrowth f`
- **What**: at ∞ the cusp condition is the plain growth condition.
- **How**: (→) test with `g = 1`; (←) any `g` fixing ∞ is upper triangular (`smul_infty_eq_self_iff`) so `IsOfExponentialGrowth.slash`.
- **Hypotheses**: none.
- **Uses from project**: `IsOfExponentialGrowthAt`, `IsOfExponentialGrowth.slash`, `IsOfExponentialGrowth`
- **Used by**: `isOfExponentialGrowthAt_iff`
- **Visibility**: public
- **Lines**: 62–65, proof body ≈ 2 lines
- **Notes**: copy of `isBoundedAt_infty_iff` (`BoundedAtCusp.lean:74`).

### `lemma OnePoint.isOfExponentialGrowthAt_iff`
- **Type**: `(hg : g • ∞ = c) : IsOfExponentialGrowthAt c f ↔ IsOfExponentialGrowth (f ∣[(0 : ℤ)] g)`
- **What**: one scaling matrix suffices.
- **How**: `smul_iff` + `infty_iff`.
- **Hypotheses**: `g • ∞ = c`.
- **Uses from project**: `IsOfExponentialGrowthAt`, `IsOfExponentialGrowthAt.smul_iff`, `isOfExponentialGrowthAt_infty_iff`, `IsOfExponentialGrowth`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 67–71, proof body ≈ 2 lines
- **Notes**: copy of `isBoundedAt_iff` (`BoundedAtCusp.lean:82`); used by Cusps, JInvariant, Congruence, Cox/ModularPolynomial/Construction.

## File Summary
- Total declarations: 5 (1 def, 4 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `IsOfExponentialGrowthAt`
- Unused declarations (not used by anything in this file): `isOfExponentialGrowthAt_iff` (used by 4 other files)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations
### Mathlib API candidates
- The whole file is `Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean:35–82` with `IsBoundedAtImInfty` replaced by `IsOfExponentialGrowth` and weight fixed to 0. Mathlib's file additionally has `isBoundedAt_iff_exists_SL2Z` (`:94`, cusps of `𝒮ℒ` via `isCusp_SL2Z_iff'`) — the missing analogue is exactly what three consumer proofs re-derive by hand (JInvariant.lean:48–54, Congruence.lean:126–140, Cox/ModularPolynomial/Construction.lean:270–273).
- If mathlib's `IsBoundedAt` were generalised over a "growth class" predicate `P : (ℍ → ℂ) → Prop` stable under `.slash`, both files would be instances; alternatively, in `IsBigO` form `IsOfExponentialGrowth.slash` is `hf.comp_tendsto (tendsto_smul_atImInfty hg)` (`FunctionsBoundedAtInfty.lean:90`) times a constant (`IsBigO.const_mul_left`).
### Missing API / repeated patterns
- `OnePoint.isOfExponentialGrowthAt_iff_exists_SL2Z` / `isOfExponentialGrowthAt_of_forall_SL2Z` (see above).
- `IsOfExponentialGrowthAt.add/mul/…` (none; cf. missing `IsOfExponentialGrowth.add/mul`).
- Manual `∃ M A` unfolding at 36–42 (shared pattern with CuspGrowth.lean:96–104, NormalFormGrowth.lean:43–64).
### Junk candidates
- none.
### Moral duplicates within this batch
- none within the batch; the file duplicates mathlib's `BoundedAtCusp.lean` structurally.
### Generalization notes
- `IsOfExponentialGrowth.slash` is stated at weight 0 only; for upper-triangular `g`, `denom g τ = g 1 1` is constant, so the same proof works for any weight `k` (as mathlib's `IsBoundedAtImInfty.slash` does). Fixing `k = 0` everywhere in this folder is a design choice (modular functions), not a proof limitation.
