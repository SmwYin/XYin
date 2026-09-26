# Inventory: XYin/PhD/Modularforms/BigO.lean  (61 lines)

Big-O estimates `(mz+n)⁻¹ = O(|n|⁻¹)` (and `(nz+m)⁻¹`, powers, ℕ-restriction) along `cofinite` for `z ∈ ℍ`, derived from mathlib's Eisenstein-series `summand_bound`, plus two generic `IsBigO` transport lemmas (ℤ → ℕ, `n ↦ -n`). **Entirely dead code**: imported only by `Summability/Reciprocal.lean` (and `XYin.lean`), but Reciprocal.lean uses none of these names — it calls mathlib's `isBigO_linear_add_const_vec` / `summable_of_isBigO_rpow_norm` directly. Every result here now has a named mathlib counterpart in `Mathlib/NumberTheory/ModularForms/EisensteinSeries/Summable.lean` or `Mathlib/Analysis/Asymptotics/Defs.lean`.

## Declarations

### `lemma norm_symm`
- **Type**: `(x y : ℤ) : ‖![x, y]‖ = ‖![y,x]‖`
- **What**: The sup-norm on `Fin 2 → ℤ` is symmetric under swapping coordinates.
- **How**: `EisensteinSeries.norm_eq_max_natAbs` (`EisensteinSeries/Summable.lean:32`) + `max_comm`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 16–19, body 3 lines
- **Notes**: unused anywhere; root-namespace name `norm_symm` is dangerously generic.

### `private lemma linear_bigO_of_norm_le`
- **Type**: `(z : ℍ) (v : ℤ → Fin 2 → ℤ) (hv : ∀ n : ℤ, |(n : ℝ)| ≤ ‖v n‖) : (fun n ↦ ((v n 0 : ℂ) * z + v n 1)⁻¹) =O[cofinite] (fun n ↦ |(n : ℝ)|⁻¹)`
- **What**: If a family of lattice vectors `v n` has norm at least `|n|`, then `(v n 0 · z + v n 1)⁻¹ = O(|n|⁻¹)`.
- **How**: `IsBigO.of_bound (r z)⁻¹` on `eventually_cofinite_ne 0`, using mathlib `EisensteinSeries.summand_bound z zero_le_one (v n)` (`Summable.lean:143`, `k = 1`, `Real.rpow_neg_one`) and `inv_anti₀` with `hv`, `r_pos`.
- **Hypotheses**: `|n| ≤ ‖v n‖` for all `n`.
- **Uses from project**: []
- **Used by**: linear_bigO, linear_bigO'
- **Visibility**: private
- **Lines**: 22–32, body ≈ 8 lines
- **Notes**: a reasonable abstraction, but mathlib's `linear_inv_isBigO_right/left` (`Summable.lean:186/190`) are proved via `IsTheta` instead and are more general (`z : ℂ`, `z ≠ 0`).

### `lemma linear_bigO`
- **Type**: `(m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite] fun n => (|(n : ℝ)|⁻¹)`
- **What**: `(mz+n)⁻¹ = O(|n|⁻¹)` as `n → ∞` in ℤ.
- **How**: `linear_bigO_of_norm_le` with `v n = ![m, n]`, norm bound by `norm_eq_max_natAbs`.
- **Hypotheses**: none.
- **Uses from project**: linear_bigO_of_norm_le
- **Used by**: linear_bigO_pow, linear_bigO_nat
- **Visibility**: public
- **Lines**: 34–37, body 2 lines
- **Notes**: unused anywhere. **Mathlib**: `EisensteinSeries.linear_inv_isBigO_right (c : ℤ) (z : ℂ) : (fun d : ℤ ↦ (c * z + d)⁻¹) =O[cofinite] fun n ↦ (n : ℝ)⁻¹` (`Summable.lean:186`); the exact statement here is `(linear_inv_isBigO_right m z).abs_right.congr_right fun n => abs_inv _` — verified by scratch typecheck this session.

### `lemma linear_bigO_pow`
- **Type**: `(m : ℤ) (z : ℍ) (k : ℕ) : (fun (n : ℤ) => ((((m : ℂ) * z + n)) ^ k )⁻¹) =O[cofinite] fun n => ((|(n : ℝ)| ^ k)⁻¹)`
- **What**: `(mz+n)^{-k} = O(|n|^{-k})`.
- **How**: `inv_pow` + `Asymptotics.IsBigO.pow` of `linear_bigO`.
- **Hypotheses**: none.
- **Uses from project**: linear_bigO
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 39–43, body 2 lines
- **Notes**: unused anywhere; mathlib does this inline as `(linear_inv_isBigO_right c z).abs_right.pow k` in `linear_right_summable` (`Summable.lean:236–240`).

### `lemma Asymptotics.IsBigO.zify`
- **Type**: `{α β : Type*} [Norm α] [Norm β] {f : ℤ → α} {g : ℤ → β} (hf : f =O[cofinite] g) : (fun (n : ℕ) => f n) =O[cofinite] fun n => g n`
- **What**: A cofinite big-O on ℤ restricts to ℕ.
- **How**: `hf.comp_tendsto Nat.cast_injective.tendsto_cofinite` (`Function.Injective.tendsto_cofinite`, `Mathlib/Order/Filter/Cofinite.lean:252`).
- **Hypotheses**: none beyond the big-O.
- **Uses from project**: []
- **Used by**: linear_bigO_nat
- **Visibility**: public
- **Lines**: 45–48, body 1 line
- **Notes**: unused anywhere; one-line wrapper; misnamed (`zify` is a tactic converting ℕ→ℤ, this goes ℤ→ℕ); declared into mathlib's `Asymptotics.IsBigO` namespace.

### `lemma Asymptotics.IsBigO.of_neg`
- **Type**: `… (hf : f =O[cofinite] g) : (fun n => f (-n)) =O[cofinite] fun n => g (-n)`
- **What**: Cofinite big-O on ℤ is invariant under `n ↦ -n`.
- **How**: `hf.comp_tendsto (Equiv.neg ℤ).injective.tendsto_cofinite`.
- **Hypotheses**: none beyond the big-O.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 50–52, body 1 line
- **Notes**: unused anywhere. **Exact duplicate of mathlib `Asymptotics.IsBigO.comp_neg_int`** (`Mathlib/Analysis/Asymptotics/Defs.lean:439`). Note this file already uses `Equiv.neg ℤ` — the same object `equivs.lean` re-defines as `negEquiv`.

### `lemma linear_bigO_nat`
- **Type**: `(m : ℤ) (z : ℍ) : (fun (n : ℕ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite] fun n => (|(n : ℝ)|⁻¹)`
- **What**: ℕ-indexed version of `linear_bigO`.
- **How**: `(linear_bigO m z).zify`.
- **Hypotheses**: none.
- **Uses from project**: linear_bigO, Asymptotics.IsBigO.zify
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 54–56, body 1 line
- **Notes**: unused anywhere; mathlib's related `tendsto_zero_inv_linear` (`Summable.lean:194`) derives the ℕ statement from `linear_inv_isBigO_right` via `Int.cofinite_eq`/`Nat.map_cast_int_atTop`.

### `lemma linear_bigO'`
- **Type**: `(m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((n : ℂ) * z + m)⁻¹) =O[cofinite] fun n => (|(n : ℝ)|⁻¹)`
- **What**: `(nz+m)⁻¹ = O(|n|⁻¹)` (variable in the `z`-coefficient).
- **How**: `linear_bigO_of_norm_le` with `v n = ![n, m]`.
- **Hypotheses**: none.
- **Uses from project**: linear_bigO_of_norm_le
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 58–61, body 2 lines
- **Notes**: unused anywhere. **Mathlib**: `EisensteinSeries.linear_inv_isBigO_left (d : ℤ) {z : ℂ} (hz : z ≠ 0)` (`Summable.lean:190`); exact statement is `(linear_inv_isBigO_left m z.ne_zero).abs_right.congr_right fun n => abs_inv _` — verified by scratch typecheck.

## File Summary
- Total declarations: 8 (0 defs; 8 lemmas; 0 instances; 0 other)
- Key API (used by 3+ others in the file): none (linear_bigO_of_norm_le 2, linear_bigO 2)
- Unused declarations (not used by anything in this file): norm_symm, linear_bigO_pow, Asymptotics.IsBigO.of_neg, linear_bigO_nat, linear_bigO' — and project-wide NONE of the 8 declarations is referenced outside this file (Summability/Reciprocal.lean imports the module but uses only mathlib lemmas).
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations

### Mathlib API candidates
- `linear_bigO` (L34) = `EisensteinSeries.linear_inv_isBigO_right` (`Mathlib/NumberTheory/ModularForms/EisensteinSeries/Summable.lean:186`) up to `abs_right`/`abs_inv` — typechecked this session.
- `linear_bigO'` (L58) = `EisensteinSeries.linear_inv_isBigO_left` (`Summable.lean:190`) with `z.ne_zero` — typechecked this session.
- `Asymptotics.IsBigO.of_neg` (L50) = `Asymptotics.IsBigO.comp_neg_int` (`Mathlib/Analysis/Asymptotics/Defs.lean:439`), verbatim.
- `Asymptotics.IsBigO.zify` (L45) = `hf.comp_tendsto Nat.cast_injective.tendsto_cofinite` (`Mathlib/Order/Filter/Cofinite.lean:252`), a one-liner with no mathlib name; mathlib prefers `Int.cofinite_eq`/`isBigO_sup` (`Summable.lean:194–198`).
- `linear_bigO_pow` (L39): inline pattern `(… ).abs_right.pow k` in mathlib `linear_right_summable` (`Summable.lean:236`).
- `norm_symm` (L16): no mathlib analogue found (searched `norm_eq_max_natAbs`, `vecCons … norm`, `swap … norm`); unused.
- `linear_bigO_of_norm_le` (private, L22): the `summand_bound`-based route; mathlib's `IsTheta` route (`linear_isTheta_right_add`, `linear_isTheta_left`, `Summable.lean:160–180`) is more general (`z : ℂ`).

### Missing API / repeated patterns
- None to add — every statement exists in mathlib.

### Junk candidates
- The whole file (L1–61): zero consumers project-wide; `Summability/Reciprocal.lean:10` can drop `import XYin.PhD.Modularforms.BigO` (it needs `Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence` or `…Summable` directly for `isBigO_linear_add_const_vec`; check after removal).
- Stray imports: `Mathlib.Algebra.Order.Ring.Star`, `Mathlib.Analysis.CStarAlgebra.Classes`, `Mathlib.Data.Int.Star` (L3–5) have nothing to do with the content (same boilerplate header appears in equivs.lean, clog_arg_lems.lean, csqrt.lean).
- `norm_symm` (L16) and the generic root-level name.

### Moral duplicates within this batch
- `linear_bigO` / `linear_bigO'` (same proof with `![m, n]` vs `![n, m]`).
- `Asymptotics.IsBigO.zify` / `Asymptotics.IsBigO.of_neg` (both `comp_tendsto` of an injection's `tendsto_cofinite`).
- `Asymptotics.IsBigO.of_neg` vs mathlib `comp_neg_int` (identical); `Equiv.neg ℤ` here vs `negEquiv` in equivs.lean.

### Generalization notes
- `linear_bigO`, `linear_bigO'`, `linear_bigO_pow`, `linear_bigO_nat` are stated for `z : ℍ`; mathlib's versions hold for all `z : ℂ` (right) / `z ≠ 0` (left) — `Im z > 0` is never needed.
- `IsBigO.zify`/`of_neg` hold for any filter and any injective map with `tendsto_cofinite` (that is exactly `IsBigO.comp_tendsto`).
