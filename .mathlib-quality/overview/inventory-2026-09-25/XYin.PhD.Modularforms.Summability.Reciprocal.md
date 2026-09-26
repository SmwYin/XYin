# Inventory: XYin/PhD/Modularforms/Summability/Reciprocal.lean  (297 lines)

Summability and rearrangement of reciprocal lattice sums 1/(mz+n)^k on ℍ: paired sums 1/(z−n)+1/(z+n), a denominator lower bound, the weight-2 (G₂) absolutely-convergent correction term `δ` with its double-sum reindexings, and ℤ ↔ ℕ+ splitting identities used for the E₂ transformation law. Split from `summable_lems`. Only `summable_3` (→ Summability/QExpansion.lean) is used outside this file; the whole `δ`/G₂ block re-proves what mathlib's `EisensteinSeries/E2/Transform.lean` does (there module-private).

## Declarations

### `theorem upp_half_not_ints`
- **Type**: `(z : ℍ) (n : ℤ) : (z : ℂ) ≠ n`
- **What**: A point of the upper half-plane is not an integer.
- **How**: `z.ne_intCast n`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 27–28, proof body ≈ 1 line
- **Notes**: Exact wrapper of mathlib `UpperHalfPlane.ne_intCast` (`Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean:187`). Dead project-wide.

### `lemma aus`
- **Type**: `(a b : ℂ) : a + b ≠ 0 ↔ a ≠ -b`
- **What**: Sum nonzero iff not negatives of each other.
- **How**: `eq_neg_iff_add_eq_zero.symm.not`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 30–31, proof body ≈ 1 line
- **Notes**: Mathlib: `add_eq_zero_iff_eq_neg` (to_additive of `mul_eq_one_iff_eq_inv`, `Mathlib/Algebra/Group/Basic.lean:637`) `.not`. Holds in any `AddGroup`. Dead project-wide.

### `lemma pnat_inv_sub_squares`
- **Type**: `(z : ℍ) : (fun n : ℕ+ => 1 / ((z : ℂ) - n) + 1 / (z + n)) = fun n : ℕ+ => 2 * z.1 * (1 / (z ^ 2 - n ^ 2))`
- **What**: Partial-fraction identity 1/(z−n) + 1/(z+n) = 2z/(z²−n²).
- **How**: `sq_sub_sq` + `field_simp` with nonvanishing of z∓n from `ne_intCast`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 33–42, proof body ≈ 8 lines
- **Notes**: Mathlib `cotTerm_identity` (`Mathlib/Analysis/SpecialFunctions/Trigonometric/Cotangent.lean:203`) is the same identity for `x ∈ ℂ_ℤ`, indexed by ℕ with n+1. Dead project-wide.

### `lemma upper_half_plane_ne_int_pow_two`
- **Type**: `(z : ℍ) (n : ℤ) : (z : ℂ) ^ 2 - n ^ 2 ≠ 0`
- **What**: z² ≠ n² for z ∈ ℍ.
- **How**: `sq_sub_sq` + `mul_ne_zero_iff` + `ne_intCast` at ±n.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 44–47, proof body ≈ 3 lines
- **Notes**: Mathlib `Complex.integerComplement_pow_two_ne_pow_two` (`Mathlib/Analysis/Complex/IntegerCompl.lean:58`) + `UpperHalfPlane.coe_mem_integerComplement` (:37) + `sub_ne_zero`. Dead project-wide.

### `theorem upbnd`
- **Type**: `(z : ℍ) (d : ℤ) : (d ^ 2 : ℝ) * r z ^ 2 ≤ ‖((z : ℂ) ^ 2 - d ^ 2)‖`
- **What**: Lower bound |z² − d²| ≥ d²·r(z)² using the Eisenstein constant r(z).
- **How**: For each n, r(z)|n| ≤ ‖z + n‖ from `norm_le_pi_norm ![1,n] 1` and mathlib `EisensteinSeries.r_mul_max_le` (`EisensteinSeries/Summable.lean:131`); then factor z²−d² = (z+d)(z−d) and multiply the two bounds (`mul_le_mul`, `nlinarith`).
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 49–59, proof body ≈ 10 lines
- **Notes**: No mathlib analogue found (searched `z ^ 2 -`, `pow_two_sub` in `EisensteinSeries/Summable.lean`, `IntegerCompl.lean`). Dead project-wide.

### `theorem lhs_summable`
- **Type**: `(z : ℍ) : Summable fun n : ℕ+ => 1 / ((z : ℂ) - n) + 1 / (z + n)`
- **What**: The cotangent partial-fraction series converges at z ∈ ℍ.
- **How**: `summable_pnat_iff_summable_succ` then mathlib `summable_cotTerm` (`Cotangent.lean:211`) with `coe_mem_integerComplement`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: `summable_3` (238)
- **Visibility**: public
- **Lines**: 62–64, proof body ≈ 2 lines
- **Notes**: Comment line 61 "This is from the mod forms repo". Live only via `summable_3`.

### `lemma neg_div_neg_aux`
- **Type**: `(a b : ℂ) : -a/b = a / -b`
- **What**: Moving a sign between numerator and denominator.
- **How**: `ring`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 66–67, proof body ≈ 1 line
- **Notes**: Mathlib `div_neg_eq_neg_div'` (`Mathlib/Algebra/Ring/Basic.lean:285`: `a / -b = -a / b`) symm; holds in any `DivisionRing`/`HasDistribNeg` monoid. Dead project-wide.

### `theorem summable_diff`
- **Type**: `(z : ℍ) (d : ℤ) : Summable fun m : ℕ+ ↦ 1 / (-(d : ℂ) / ↑z - ↑↑m) + 1 / (-↑d / ↑z + ↑↑m)`
- **What**: The cotangent series at the point −d/z converges.
- **How**: If d = 0 the terms vanish; else `-d/z ∈ ℂ_ℤ` by `UpperHalfPlane.int_div_mem_integerComplement` (`IntegerCompl.lean:68`) and `summable_cotTerm`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 69–77, proof body ≈ 7 lines
- **Notes**: Dead project-wide.

### `lemma arg1`
- **Type**: `(a b c d e f g h : ℂ) : e / f + g / h - a / b - c / d = e / f + g / h + a / -b + c / -d`
- **What**: Eight-variable sign-shuffling identity.
- **How**: `ring`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `sum_int_pnat3` (91)
- **Visibility**: public
- **Lines**: 79–80, proof body ≈ 1 line
- **Notes**: Junk; `ring_nf` at the use site does it.

### `lemma sum_int_pnat3`
- **Type**: `(z : ℍ) (d : ℤ) : ∑' m : ℕ+, ((1/(m z − d) + 1/(−m z − d)) − 1/(m z + d) − 1/(−m z + d)) = (2 / z) * ∑' m : ℕ+, (1/(−d/z − m) + 1/(−d/z + m))`
- **What**: Rescale the paired reciprocal sum by 1/z to move it to the point −d/z.
- **How**: `tsum_mul_left` + `tsum_congr`; termwise `arg1`, `ring_nf`, `field_simp [z.ne_zero]`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `arg1`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 82–94, proof body ≈ 7 lines
- **Notes**: E₂-transform bookkeeping; mathlib does the analogous step in the private `aux_sum_Ico_S_identity` (`EisensteinSeries/E2/Summable.lean:151`). Dead project-wide.

### `lemma pow_max`
- **Type**: `(x y : ℕ) : (max x y)^2 = max (x^2) (y ^ 2)`
- **What**: Squaring commutes with max on ℕ.
- **How**: `(monotone_id.pow_const 2).map_max`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 96–97, proof body ≈ 1 line
- **Notes**: One-liner over mathlib `Monotone.map_max` (`Mathlib/Order/MinMax.lean:150`). Dead project-wide.

### `theorem extracted_abs_norm_summable`
- **Type**: `(z : ℍ) (i : ℤ) : Summable fun m ↦ 1 / (r z ^ 2 * 2⁻¹ * ‖![m, i]‖ ^ 2)`
- **What**: ∑_m 1/‖(m,i)‖² converges (fixed second coordinate).
- **How**: Majorant ∑ 1/m² from `Real.summable_one_div_int_pow` (`Mathlib/Analysis/PSeries.lean:335`), then `Summable.of_norm_bounded_eventually` (`Mathlib/Analysis/Normed/Group/InfiniteSum.lean:172`) off m = 0 using `norm_le_pi_norm ![m,i] 0`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 99–114, proof body ≈ 15 lines
- **Notes**: Hand-rolled comparison; mathlib's `EisensteinSeries.linear_inv_isBigO_right` (`Summable.lean:186`) + `summable_of_isBigO` is the idiomatic route. Name is an `extract_goal` artefact. Dead project-wide.

### `lemma summable_hammerTime_nat`
- **Type**: `{α : Type} [NormedField α] [CompleteSpace α] (f : ℕ → α) (a : ℝ) (hab : 1 < a) (hf : (fun n => (f n)⁻¹) =O[cofinite] fun n => (|(n : ℝ)| ^ (a : ℝ))⁻¹) : Summable fun n => (f n)⁻¹`
- **What**: A sequence that is O(n^{−a}), a > 1, is summable.
- **How**: `summable_of_isBigO` (`Mathlib/Analysis/Asymptotics/Lemmas.lean:773`) + `Real.summable_nat_rpow_inv` (`PSeries.lean:280`).
- **Hypotheses**: a > 1, big-O bound.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 116–121, proof body ≈ 2 lines
- **Notes**: Mathlib `summable_of_isBigO_nat` (`Asymptotics/Lemmas.lean:778`) is the same shape; `NormedField` unnecessary (any complete `SeminormedAddCommGroup`). Junk name. Dead project-wide.

### `theorem summable_diff_denom`
- **Type**: `(z : ℍ) (i : ℤ) : Summable fun (m : ℤ) ↦ ((m : ℂ) * ↑z + ↑i + 1)⁻¹ * ((m : ℂ) * ↑z + ↑i)⁻¹`
- **What**: ∑_m 1/((mz+i)(mz+i+1)) converges.
- **How**: mathlib `summable_linear_left_mul_linear_left` (`EisensteinSeries/Summable.lean:262`).
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 123–126, proof body ≈ 2 lines
- **Notes**: Wrapper. Dead project-wide.

### `lemma summable_pain`
- **Type**: `(z : ℍ) (i : ℤ) : Summable (fun m : ℤ ↦ 1 / ((m : ℂ) * ↑z + ↑i) - 1 / (↑m * ↑z + ↑i + 1))`
- **What**: The telescoping difference series converges.
- **How**: mathlib `summable_left_one_div_linear_sub_one_div_linear` (`EisensteinSeries/E2/Summable.lean:134`).
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 128–130, proof body ≈ 1 line
- **Notes**: Wrapper. Dead project-wide.

### `theorem vector_norm_bound`
- **Type**: `(b : Fin 2 → ℤ) (hb : b ≠ 0) (HB1 : b ≠ ![0, -1]) : ‖![b 0, b 1 + 1]‖ ^ (-1 : ℝ) * ‖b‖ ^ (-2 : ℝ) ≤ 2 * ‖b‖ ^ (-3 : ℝ)`
- **What**: Shifting the second coordinate by 1 changes the sup-norm by at most a factor 2 (rpow form).
- **How**: `norm_eq_max_natAbs` (`EisensteinSeries/Summable.lean:32`) + `omega` for ‖b‖ ≤ 2‖b'‖; then `le_mul_inv_iff₀`, `Real.rpow_neg_one`, `Real.rpow_add`.
- **Hypotheses**: b ≠ 0, b ≠ (0,−1).
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 132–156, proof body ≈ 24 lines
- **Notes**: Superseded by mathlib `EisensteinSeries.vec_add_const_isTheta` (`Summable.lean:285`) / `isBigO_linear_add_const_vec` (:291), which `G_2_alt_summable` already uses. Dead project-wide.

### `lemma G_2_alt_summable`
- **Type**: `(z : ℍ) : Summable fun (m : Fin 2 → ℤ) => 1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1))`
- **What**: The absolutely convergent G₂ double series (Hecke's trick term) is summable.
- **How**: `EisensteinSeries.summable_of_isBigO_rpow_norm (a := 3)` (`Summable.lean:296`) with the product of three `isBigO_linear_add_const_vec` bounds.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: `G_2_alt_summable_δ` (178), `G2_prod_summable1` (194)
- **Visibility**: public
- **Lines**: 158–163, proof body ≈ 4 lines
- **Notes**: Identical to the inner `H` of mathlib `EisensteinSeries.G2Term_summable` (`EisensteinSeries/E2/Transform.lean:95`, module-private: declared before `public section` at :183).

### `def δ`
- **Type**: `(a b : ℤ) : ℂ := if a = 0 ∧ b = 0 then 1 else if a = 0 ∧ b = -1 then 2 else 0`
- **What**: Correction term making the G₂ double sum absolutely convergent (1 at (0,0), 2 at (0,−1), else 0).
- **How**: `if` definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `δ_eq`, `δ_eq2`, `δ_neq`, `G_2_alt_summable_δ`, `G2_prod_summable1_δ`, `G2_alt_indexing_δ`, `G2_alt_indexing2_δ`
- **Visibility**: public
- **Lines**: 165
- **Notes**: `noncomputable`. Mathlib `EisensteinSeries.δ (x : Fin 2 → ℤ)` (`E2/Transform.lean:79`) is the uncurried twin (module-private). The hits for `δ` in Cox/*.lean are local variable names, not this def.

### `lemma δ_eq`
- **Type**: `δ 0 0 = 1`
- **What**: value at (0,0).
- **How**: `simp [δ]`.
- **Hypotheses**: none.
- **Uses from project**: `δ`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 167–168, proof body ≈ 1 line
- **Notes**: `@[simp]`. = mathlib `δ_eq` (Transform.lean:82).

### `lemma δ_eq2`
- **Type**: `δ 0 (-1) = 2`
- **What**: value at (0,−1).
- **How**: `simp [δ]`.
- **Hypotheses**: none.
- **Uses from project**: `δ`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 170–171, proof body ≈ 1 line
- **Notes**: `@[simp]`. = mathlib `δ_eq_two` (Transform.lean:85).

### `lemma δ_neq`
- **Type**: `(a b : ℤ) (h : a ≠ 0) : δ a b = 0`
- **What**: δ vanishes off the column a = 0.
- **How**: `simp [δ, h]`.
- **Hypotheses**: a ≠ 0.
- **Uses from project**: `δ`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 173–174, proof body ≈ 1 line
- **Notes**: Missing `@[simp]` (companions have it). Mathlib uses `δ_eventually_cofinite` (Transform.lean:87) instead. Dead project-wide.

### `lemma G_2_alt_summable_δ`
- **Type**: `(z : ℍ) : Summable fun (m : Fin 2 → ℤ) => (1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) + δ (m 0) (m 1))`
- **What**: Adding the finitely-supported δ keeps the G₂ series summable.
- **How**: `Summable.congr_cofinite` (`Mathlib/Topology/Algebra/InfiniteSum/Group.lean:143`) with `eventually_cofinite_ne` at ![0,0] and ![0,−1]; two `fin_cases` blocks show δ = 0 there.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `G_2_alt_summable`, `δ`
- **Used by**: `G2_prod_summable1_δ` (201), `G2_alt_indexing_δ` (210), `G2_alt_indexing2_δ` (216)
- **Visibility**: public
- **Lines**: 176–190, proof body ≈ 14 lines
- **Notes**: = mathlib `EisensteinSeries.G2Term_summable` (Transform.lean:95, private). The two `fin_cases` blocks (180–189) are what mathlib packages as `δ_eventually_cofinite`.

### `theorem G2_prod_summable1`
- **Type**: `(z : ℍ) (b : ℤ) : Summable fun c : ℤ ↦ ((b : ℂ) * ↑z + ↑c + 1)⁻¹ * (((b : ℂ) * ↑z + ↑c) ^ 2)⁻¹`
- **What**: Each row of the G₂ series is summable.
- **How**: `finTwoArrowEquiv.symm.summable_iff` + `Summable.prod_factor`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `G_2_alt_summable`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 192–197, proof body ≈ 4 lines
- **Notes**: Dead project-wide; mathlib `linear_left_summable` / `(G2Term_prod_summable z).prod_factor`.

### `theorem G2_prod_summable1_δ`
- **Type**: `(z : ℍ) (b : ℤ) : Summable fun c : ℤ ↦ ((b : ℂ) * ↑z + ↑c + 1)⁻¹ * (((b : ℂ) * ↑z + ↑c) ^ 2)⁻¹ + δ b c`
- **What**: Row summability with δ.
- **How**: same as previous from `G_2_alt_summable_δ`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `G_2_alt_summable_δ`, `δ`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 199–204, proof body ≈ 4 lines
- **Notes**: = `(EisensteinSeries.G2Term_prod_summable z).prod_factor b` (Transform.lean:104). Dead project-wide. Same 4-line skeleton as `G2_prod_summable1`.

### `lemma G2_alt_indexing_δ`
- **Type**: `(z : ℍ) : ∑' (m : Fin 2 → ℤ), (… + δ (m 0) (m 1)) = ∑' m : ℤ, ∑' n : ℤ, (… + δ m n)`
- **What**: Unfold the `Fin 2 → ℤ` sum as an iterated sum ∑_m ∑_n.
- **How**: `finTwoArrowEquiv.symm.tsum_eq` + `Summable.tsum_prod`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `G_2_alt_summable_δ`, `δ`
- **Used by**: `G2_alt_indexing2_δ` (215)
- **Visibility**: public
- **Lines**: 206–210, proof body ≈ 2 lines
- **Notes**: = mathlib `tsum_G2Term_eq_tsum` (Transform.lean:168, private).

### `lemma G2_alt_indexing2_δ`
- **Type**: `(z : ℍ) : ∑' (m : Fin 2 → ℤ), (… + δ (m 0) (m 1)) = ∑' n : ℤ, ∑' m : ℤ, (… + δ m n)`
- **What**: Same with the order of summation swapped.
- **How**: `G2_alt_indexing_δ` then `Summable.tsum_comm` on the uncurried summable function.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `G2_alt_indexing_δ`, `G_2_alt_summable_δ`, `δ`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 212–219, proof body ≈ 6 lines
- **Notes**: = mathlib `tsum_G2Term_eq_tsum'` (Transform.lean:173, private). Dead project-wide.

### `theorem summable_1`
- **Type**: `(k : ℕ) (z : ℍ) (hk : 1 ≤ k) : Summable fun (b : ℕ) ↦ (((z : ℂ) - ↑↑b) ^ (k + 1))⁻¹`
- **What**: ∑_b 1/(z−b)^{k+1} converges for k ≥ 1.
- **How**: negative half of `summable_int_iff_summable_nat_and_neg.mp (linear_right_summable z 1)` (`EisensteinSeries/Summable.lean:235`).
- **Hypotheses**: k ≥ 1, z ∈ ℍ.
- **Uses from project**: []
- **Used by**: `summable_3` (240)
- **Visibility**: public
- **Lines**: 221–225, proof body ≈ 3 lines
- **Notes**: Mathlib has the same as private `aux_summable_sub` (`Cotangent.lean:346`, shifted by 1, zpow form).

### `theorem summable_2`
- **Type**: `(k : ℕ) (z : ℍ) (hk : 1 ≤ k) : Summable fun (b : ℕ) ↦ (((z : ℂ) + ↑↑b) ^ (k + 1))⁻¹`
- **What**: ∑_b 1/(z+b)^{k+1} converges for k ≥ 1.
- **How**: positive half of the same split.
- **Hypotheses**: k ≥ 1, z ∈ ℍ.
- **Uses from project**: []
- **Used by**: `summable_3` (241)
- **Visibility**: public
- **Lines**: 227–231, proof body ≈ 3 lines
- **Notes**: Moral duplicate of `summable_1` (sign); mathlib private `aux_summable_add` (`Cotangent.lean:340`).

### `theorem summable_3`
- **Type**: `(m : ℕ) (y : {z : ℂ | 0 < z.im}) : Summable fun n : ℕ+ => (-1 : ℂ) ^ m * ↑m ! * (1 / (y - ↑n) ^ (m + 1)) + (-1) ^ m * ↑m ! * (1 / (y + ↑n) ^ (m + 1))`
- **What**: The m-th termwise derivatives of the cotangent series are summable over ℕ+.
- **How**: m = 0 is `lhs_summable`; m+1: `(summable_1 _).subtype _ |>.add ((summable_2 _).subtype _) |>.mul_left _`.
- **Hypotheses**: y in the open upper half-plane (as a subtype of ℂ).
- **Uses from project**: `lhs_summable`, `summable_1`, `summable_2`
- **Used by**: unused in file; used in Summability/QExpansion.lean:86 (`summable_iter_aut`)
- **Visibility**: public
- **Lines**: 233–242, proof body ≈ 6 lines
- **Notes**: Mathlib: `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm` (`Cotangent.lean:320`) `.summable` plus `eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet` (:276) gives this. Uses the raw set `{z : ℂ | 0 < z.im}` rather than `ℍ'`/`upperHalfPlaneSet`.

### `lemma G2_summable_aux`
- **Type**: `(n : ℤ) (z : ℍ) (k : ℤ) (hk : 2 ≤ k) : Summable fun d : ℤ => ((((n : ℂ) * z) + d) ^ k)⁻¹`
- **What**: Row-summability of the weight-k lattice sum.
- **How**: `exact linear_right_summable z n hk`.
- **Hypotheses**: k ≥ 2.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 244–246, proof body ≈ 1 line
- **Notes**: Exact wrapper of mathlib `EisensteinSeries.linear_right_summable` (`Summable.lean:235`). Dead project-wide.

### `lemma auxf`
- **Type**: `(a b c d : ℂ) : a / b - (c / d) = a / b + (c / -d)`
- **What**: Sign-shuffling identity.
- **How**: `ring`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 249–250, proof body ≈ 1 line
- **Notes**: Comment line 248 "straight from the mod forms repo". Mathlib `sub_eq_add_neg` + `div_neg`. Dead project-wide.

### `theorem summable_diff_right_a`
- **Type**: `(z : ℍ) (d : ℕ+) : Summable fun n : ℕ ↦ 1 / ((n : ℂ) * ↑z - ↑↑d) - 1 / (↑↑n * ↑z + ↑↑d)`
- **What**: ℕ-restriction of the telescoping difference at ±d.
- **How**: `summable_left_one_div_linear_sub_one_div_linear z (-d) d` + `summable_int_iff_summable_nat_and_neg`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 252–255, proof body ≈ 2 lines
- **Notes**: Dead project-wide.

### `theorem summable_diff_right`
- **Type**: `(z : ℍ) (d : ℕ+) : Summable fun m : ℤ ↦ 1 / ((m : ℂ) * ↑z - ↑↑d) - 1 / (↑m * ↑z + ↑↑d)`
- **What**: ℤ-version of the previous.
- **How**: `simpa using summable_left_one_div_linear_sub_one_div_linear z (-d) d`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: `sum_int_pnatt` (265, 273, 282)
- **Visibility**: public
- **Lines**: 257–259, proof body ≈ 1 line
- **Notes**: Wrapper of mathlib `E2/Summable.lean:134`.

### `lemma sum_int_pnatt`
- **Type**: `(z : ℍ) (d : ℕ+) : 2/ d + ∑' (m : ℤ), (1 / ((m : ℂ) * ↑z - d) - 1 / (↑m * ↑z + d)) = ∑' m : ℕ+, ((1/(m z − d) + 1/(−m z − d)) − 1/(m z + d) − 1/(−m z + d))`
- **What**: Split a ℤ-indexed telescoping sum into its m = 0 term (2/d, after sign) and a symmetrised ℕ+ sum.
- **How**: mathlib `tsum_int_eq_zero_add_tsum_pnat` (`NatInt.lean:555`) on `summable_diff_right`, then `Summable.tsum_add` with the two ℕ+-summabilities obtained from `summable_int_iff_summable_nat_and_neg` + `Summable.congr` + `.subtype`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `summable_diff_right`
- **Used by**: `sum_int_pnat2_pnat` (296)
- **Visibility**: public
- **Lines**: 261–290, proof body ≈ 29 lines
- **Notes**: Lines 273–281 and 282–290 are the same 9-line block (nat part / neg part). E₂ bookkeeping; mathlib's private `aux_tsum_identity_1/2` (`E2/Summable.lean:191,209`) play this role.

### `lemma sum_int_pnat2_pnat`
- **Type**: `(z : ℍ) (d : ℕ+) : ∑' (m : ℤ), (…) = -2/d + ∑' m : ℕ+, (…)`
- **What**: Rearrangement of `sum_int_pnatt` solving for the ℤ-sum.
- **How**: `rw [← sum_int_pnatt]; ring`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `sum_int_pnatt`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 292–297, proof body ≈ 2 lines
- **Notes**: Dead project-wide.

## File Summary
- Total declarations: 35 (1 def, 34 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `δ` (7 users), `G_2_alt_summable_δ` (3), `summable_diff_right` (3 uses inside one proof)
- Unused declarations (not used by anything in this file): `upp_half_not_ints`, `aus`, `pnat_inv_sub_squares`, `upper_half_plane_ne_int_pow_two`, `upbnd`, `neg_div_neg_aux`, `summable_diff`, `sum_int_pnat3`, `pow_max`, `extracted_abs_norm_summable`, `summable_hammerTime_nat`, `summable_diff_denom`, `summable_pain`, `vector_norm_bound`, `δ_eq`, `δ_eq2`, `δ_neq`, `G2_prod_summable1`, `G2_prod_summable1_δ`, `G2_alt_indexing2_δ`, `summable_3`, `G2_summable_aux`, `auxf`, `summable_diff_right_a`, `sum_int_pnat2_pnat` (of these only `summable_3` is used elsewhere in the project: Summability/QExpansion.lean:86)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (`sum_int_pnatt` is 29)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- The entire δ/G₂ block (158–219) duplicates mathlib `EisensteinSeries/E2/Transform.lean`: `δ`↔`δ` (:79), `δ_eq`↔`δ_eq` (:82), `δ_eq2`↔`δ_eq_two` (:85), `G_2_alt_summable_δ`↔`G2Term_summable` (:95), `G2_prod_summable1_δ`↔`G2Term_prod_summable.prod_factor` (:104), `G2_alt_indexing_δ`↔`tsum_G2Term_eq_tsum` (:168), `G2_alt_indexing2_δ`↔`tsum_G2Term_eq_tsum'` (:173). Caveat: in the pinned mathlib these sit *before* `@[expose] public section` (Transform.lean:183) so they are NOT importable; only `G2_S_transform`, `G2_T_transform`, `G2_slash_action`, `E2_slash_action` are public. If the project needs the intermediate lemmas it should upstream a PR moving them into the public section rather than keep this copy.
- Exact one-line wrappers: `upp_half_not_ints` (27) = `UpperHalfPlane.ne_intCast`; `G2_summable_aux` (244) = `EisensteinSeries.linear_right_summable`; `summable_diff_denom` (123) = `summable_linear_left_mul_linear_left`; `summable_pain` (128), `summable_diff_right` (257), `summable_diff_right_a` (252) = `summable_left_one_div_linear_sub_one_div_linear` (E2/Summable.lean:134); `lhs_summable` (62), `summable_diff` (69) = `summable_cotTerm` (Cotangent.lean:211) reindexed by `summable_pnat_iff_summable_succ`.
- `pnat_inv_sub_squares` (33) = `cotTerm_identity` (Cotangent.lean:203); `upper_half_plane_ne_int_pow_two` (44) = `integerComplement_pow_two_ne_pow_two` (IntegerCompl.lean:58); `aus` (30) = `add_eq_zero_iff_eq_neg.not`; `neg_div_neg_aux` (66) = `div_neg_eq_neg_div'` (Ring/Basic.lean:285).symm; `pow_max` (96) = `Monotone.map_max`.
- `summable_hammerTime_nat` (116) = `summable_of_isBigO_nat` (Asymptotics/Lemmas.lean:778) + `Real.summable_nat_rpow_inv`.
- `summable_1`/`summable_2` (221/227) = Cotangent.lean private `aux_summable_sub`/`aux_summable_add` (:346/:340); `summable_3` (233) follows from `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm` (:320) + `eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet` (:276).
- `vector_norm_bound` (132) is superseded by `vec_add_const_isTheta`/`isBigO_linear_add_const_vec` (Summable.lean:285/291), already used at 162–163.
- Hand-rolled comparison test: `extracted_abs_norm_summable` (99–114) does a manual `of_norm_bounded_eventually` where `linear_inv_isBigO_right` + `summable_of_isBigO` would do.
- No analogue found: `upbnd` (49) (searched `z ^ 2 -`/`sq_sub_sq` in EisensteinSeries/Summable.lean, IntegerCompl.lean).
### Missing API / repeated patterns
- `sum_int_pnatt` 273–281 vs 282–290: identical 9-line block; a lemma `summable_diff_right_pnat_parts (z d) : Summable (fun n : ℕ+ ↦ …) ∧ Summable (fun n : ℕ+ ↦ …)` or use of `summable_int_iff_summable_nat_and_neg` + `summable_pnat_iff_summable_nat` collapses it.
- `G_2_alt_summable_δ` 180–189: two identical `fin_cases` blocks → mathlib's `δ_eventually_cofinite`-style lemma `δ_eq_zero_of_ne (h₀ : m ≠ ![0,0]) (h₁ : m ≠ ![0,-1]) : δ (m 0) (m 1) = 0`.
- `G2_prod_summable1` and `G2_prod_summable1_δ` (192–204): same 4-line skeleton.
- `δ` lacks `@[simp]` on `δ_neq`; no `δ_eventually_cofinite`.
### Junk candidates
- Dead project-wide: everything except `summable_3` (and its transitive inputs `lhs_summable`, `summable_1`, `summable_2`) — 31 of 35 declarations, including the whole δ/G₂ block and the E₂ splitting identities (`sum_int_pnat3`, `sum_int_pnatt`, `sum_int_pnat2_pnat`).
- Pure `ring` identities as lemmas: `arg1` (79), `auxf` (249), `neg_div_neg_aux` (66).
- Names from `extract_goal`/humour: `extracted_abs_norm_summable`, `summable_hammerTime_nat`, `summable_pain`, `aus`, `upbnd`, `summable_1/2/3`.
- Stale comments: 61, 248 "from the mod forms repo".
### Moral duplicates within this batch
- `summable_1` vs `summable_2` (sign only); `summable_diff_right_a` vs `summable_diff_right` (ℕ vs ℤ); `G2_prod_summable1` vs `G2_prod_summable1_δ`; `G2_alt_indexing_δ` vs `G2_alt_indexing2_δ`; `upp_half_not_ints` vs iteratedderivs.lean `upper_ne_int` (both are `ne_intCast` in disguise); `upper_half_plane_ne_int_pow_two` vs `pnat_inv_sub_squares`'s inline `hsub/hadd`.
### Generalization notes
- `aus`, `neg_div_neg_aux`, `arg1`, `auxf`: stated for ℂ, hold in any `AddGroup` / `DivisionRing`.
- `summable_hammerTime_nat`: `NormedField α` unused beyond `SeminormedAddCommGroup + CompleteSpace`.
- `pnat_inv_sub_squares`, `upper_half_plane_ne_int_pow_two`, `lhs_summable`, `summable_diff`: only `z ∈ ℂ_ℤ` (integer complement) is used, as in mathlib's Cotangent.lean.
- `summable_1`, `summable_2`, `G2_summable_aux`: `linear_right_summable` works for any `z : ℂ` with `z ∉ ℝ`-type hypothesis only through `EisensteinSeries.r`; mathlib states `linear_right_summable (z : ℍ)` too, so no further generality.
