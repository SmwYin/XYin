# Inventory: XYin/PhD/Modularforms/Summability/QExpansion.lean  (296 lines)

Iterated derivatives of the two series π cot(πz) = 1/z + ∑_{n≥1}(1/(z−n)+1/(z+n)) and πi − 2πi ∑ qⁿ on the upper half-plane, and their comparison, yielding the Lipschitz/Eisenstein identity ∑_{d∈ℤ} 1/(z+d)^k = (−2πi)^k/(k−1)! ∑ n^{k−1} qⁿ (`q_exp_iden`). Split from `summable_lems`. Imported by `Eisensteinqexpansions.lean` but NO declaration of this file is referenced anywhere else in the project — the whole file is dead API, and its main result is now mathlib's `EisensteinSeries.qExpansion_identity_pnat`.

## Declarations

### `theorem summable_iter_derv'`
- **Type**: `(k : ℕ) (y : ℍ') : Summable fun n : ℕ => (2 * ↑π * Complex.I * n) ^ k * Complex.exp (2 * ↑π * Complex.I * n * y)`
- **What**: The k-th termwise derivatives (2πin)^k qⁿ of the geometric q-series are summable.
- **How**: `summable_pow_mul_geometric_of_norm_lt_one` with ratio bound `norm_exp_two_pi_I_lt_one` (`Mathlib/Analysis/Complex/UpperHalfPlane/Exp.lean:43`), `.mul_left`, and `Complex.exp_nat_mul`.
- **Hypotheses**: y in the open upper half-plane.
- **Uses from project**: `ℍ'` (tsumderivWithin.lean:30)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 27–32, proof body ≈ 3 lines
- **Notes**: Mathlib `EisensteinSeries.summable_pow_mul_cexp k 1 z` (`EisensteinSeries/QExpansion.lean:192`) + `.mul_left`. Dead project-wide.

### `theorem exp_series_ite_deriv_uexp2`
- **Type**: `(k : ℕ) (x : {z : ℂ | 0 < z.im}) : iteratedDerivWithin k (fun z => ∑' n : ℕ, exp (2πi n z)) {z | 0 < z.im} x = ∑' n : ℕ, iteratedDerivWithin k (fun s => exp (2πi n s)) {z | 0 < z.im} x`
- **What**: Differentiate the q-series termwise k times.
- **How**: mathlib `iteratedDerivWithin_tsum_cexp_eq` (`EisensteinSeries/QExpansion.lean:128`) after `Complex.exp_nat_mul` normalisation.
- **Hypotheses**: x in the open upper half-plane.
- **Uses from project**: []
- **Used by**: `exp_series_ite_deriv_uexp''` (46)
- **Visibility**: public
- **Lines**: 34–40, proof body ≈ 2 lines
- **Notes**: Wrapper.

### `theorem exp_series_ite_deriv_uexp''`
- **Type**: `(k : ℕ) (x : {z : ℂ | 0 < z.im}) : iteratedDerivWithin k (fun z => ∑' n : ℕ, exp (2πi n z)) {z | 0 < z.im} x = ∑' n : ℕ, (2πi n) ^ k * exp (2πi n x)`
- **What**: Closed form of the k-th derivative of the q-series.
- **How**: previous lemma + termwise `exp_iter_deriv_within` (iteratedderivs.lean:65) via `tsum_congr`.
- **Hypotheses**: x in the open upper half-plane.
- **Uses from project**: `exp_series_ite_deriv_uexp2`, `exp_iter_deriv_within`
- **Used by**: `exp_series_ite_deriv_uexp'''` (53), `iter_der_within_add` (69)
- **Visibility**: public
- **Lines**: 42–47, proof body ≈ 2 lines
- **Notes**: Mathlib proves this inside the private `iteratedDerivWithin_tsum_exp_aux_eq` (`EisensteinSeries/QExpansion.lean:146`).

### `theorem exp_series_ite_deriv_uexp'''`
- **Type**: `(k : ℕ) : EqOn (iteratedDerivWithin k (fun z => ∑' n, exp (2πi n z)) ℍ') (fun x => ∑' n, (2πi n)^k * exp (2πi n x)) ℍ'`
- **What**: `EqOn` form of the previous.
- **How**: pointwise from `exp_series_ite_deriv_uexp''`.
- **Hypotheses**: none beyond the set.
- **Uses from project**: `exp_series_ite_deriv_uexp''`, `ℍ'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 49–53, proof body ≈ 1 line
- **Notes**: Dead project-wide.

### `theorem tsum_uexp_contDiffOn`
- **Type**: `(k : ℕ) : ContDiffOn ℂ k (fun z : ℂ => ∑' n : ℕ, exp (2πi n z)) ℍ'`
- **What**: The q-series is C^k on ℍ.
- **How**: mathlib `contDiffOn_tsum_cexp` (`EisensteinSeries/QExpansion.lean:138`).
- **Hypotheses**: none.
- **Uses from project**: `ℍ'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 55–58, proof body ≈ 2 lines
- **Notes**: Wrapper (mathlib version is for `k : ℕ∞`). Dead project-wide.

### `theorem iter_der_within_add`
- **Type**: `(k : ℕ+) (x : {z : ℂ | 0 < z.im}) : iteratedDerivWithin k (fun z => πi − (2πi) • ∑' n, exp (2πi n z)) {…} x = −(2πi) * ∑' n, (2πi n)^k * exp (2πi n x)`
- **What**: k-th derivative (k ≥ 1) of πi − 2πi ∑ qⁿ.
- **How**: `iteratedDerivWithin_const_sub` (`Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean:95`), `iteratedDerivWithin_fun_neg` (:178), `iteratedDerivWithin_const_mul_field` (:139), then `exp_series_ite_deriv_uexp''`.
- **Hypotheses**: k ≥ 1.
- **Uses from project**: `exp_series_ite_deriv_uexp''`
- **Used by**: `iter_exp_eqOn` (81)
- **Visibility**: public
- **Lines**: 60–70, proof body ≈ 5 lines
- **Notes**: = mathlib private `iteratedDerivWithin_tsum_exp_aux_eq` (`EisensteinSeries/QExpansion.lean:146`) modulo normal form.

### `theorem iter_exp_eqOn`
- **Type**: `(k : ℕ+) : EqOn (iteratedDerivWithin k (fun z => πi − (2πi) • ∑' n, exp (2πi n z)) {…}) (fun x => −(2πi) * ∑' n, (2πi n)^k * exp (2πi n x)) {…}`
- **What**: `EqOn` form of `iter_der_within_add`.
- **How**: pointwise.
- **Hypotheses**: k ≥ 1.
- **Uses from project**: `iter_der_within_add`
- **Used by**: `q_exp_iden''` (265)
- **Visibility**: public
- **Lines**: 72–81, proof body ≈ 1 line
- **Notes**: —

### `theorem summable_iter_aut`
- **Type**: `(k : ℕ) (z : ℍ) : Summable fun n : ℕ+ => iteratedDerivWithin k (fun z : ℂ => 1 / (z - n) + 1 / (z + n)) {z | 0 < z.im} z`
- **What**: The k-th termwise derivatives of the cotangent series are summable.
- **How**: `summable_3` (Reciprocal.lean:233) transported by `iter_div_aut_add` (iteratedderivs.lean:50).
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `summable_3`, `iter_div_aut_add`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 83–88, proof body ≈ 3 lines
- **Notes**: Mathlib `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm` (`Cotangent.lean:320`) `.summable`. Dead project-wide.

### `lemma sub_bound`
- **Type**: `(s : ℍ) (A B : ℝ) (hB : 0 < B) (hs : s ∈ verticalStrip A B) (k : ℕ) (n : ℕ+) : ‖(-1)^(k+1) * (k+1)! * (1 / (s - n)^(k+2))‖ ≤ ‖((k+1)! / r ⟨⟨A,B⟩,_⟩ ^ (k+2)) * ((n:ℝ) ^ ((k:ℤ)+2))⁻¹‖`
- **What**: Uniform bound on a vertical strip for the (k+1)-st derivative term 1/(s−n)^{k+2}.
- **How**: mathlib `summand_bound_of_mem_verticalStrip` (`EisensteinSeries/Summable.lean:155`) with x = ![1, −n], ‖![1,−n]‖ = n by `norm_eq_max_natAbs`, then rpow/zpow bookkeeping.
- **Hypotheses**: s in the strip |Re| ≤ A, Im ≥ B > 0.
- **Uses from project**: []
- **Used by**: `aut_bound_on_comp` (141)
- **Visibility**: public
- **Lines**: 90–103, proof body ≈ 13 lines
- **Notes**: Mathlib private `iteratedDerivWithin_cotTerm_bounded_uniformly` (`Cotangent.lean:302`) proves the same with `abs_norm_eq_max_natAbs_neg` (`Summable.lean:59`).

### `lemma add_bound`
- **Type**: same as `sub_bound` with `(s + n)`.
- **What**: Same bound for 1/(s+n)^{k+2}.
- **How**: identical proof with x = ![1, n].
- **Hypotheses**: as above.
- **Uses from project**: []
- **Used by**: `aut_bound_on_comp` (142)
- **Visibility**: public
- **Lines**: 105–118, proof body ≈ 13 lines
- **Notes**: Line-for-line duplicate of `sub_bound` (only the sign of n differs).

### `theorem aut_bound_on_comp`
- **Type**: `(K : Set ℍ) (hk2 : IsCompact K) (k : ℕ) : ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ (n : ℕ+) (s : K), ‖derivWithin (fun z => iteratedDerivWithin k (fun z => (z - n)⁻¹ + (z + n)⁻¹) {…} z) {…} s‖ ≤ u n`
- **What**: On a compact K ⊂ ℍ the (k+1)-st termwise derivatives of the cotangent series have a summable majorant.
- **How**: `subset_verticalStrip_of_isCompact` (`UpperHalfPlane/Topology.lean:115`) gives A, B; majorant `2·‖(k+1)!/r^{k+2}‖·n^{−(k+2)}` summable by `Real.summable_nat_pow_inv` (`PSeries.lean:324`); `iteratedDerivWithin_succ`, `iter_div_aut_add`, and `sub_bound`+`add_bound` give the termwise bound.
- **Hypotheses**: K compact.
- **Uses from project**: `sub_bound`, `add_bound`, `iter_div_aut_add`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 120–145, proof body ≈ 25 lines
- **Notes**: This is exactly the input shape of tsumderivWithin.lean `hasDerivAt_tsum_fun`, but nothing consumes it any more. Mathlib: `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm` (`Cotangent.lean:320`). Dead project-wide.

### `theorem diff_on_aux`
- **Type**: `(k : ℕ) (n : ℕ+) : DifferentiableOn ℂ ((fun t => (-1)^k * k! * (1/(t - n)^(k+1))) + fun t => (-1)^k * k! * (1/(t + n)^(k+1))) {z | 0 < z.im}`
- **What**: The closed-form k-th derivative of the cotangent term is holomorphic on ℍ.
- **How**: `fun_prop (disch := aesop)` with the denominators nonzero from `upper_ne_int`.
- **Hypotheses**: none.
- **Uses from project**: `upper_ne_int` (iteratedderivs.lean:20)
- **Used by**: `diff_at_aux` (163)
- **Visibility**: public
- **Lines**: 148–156, proof body ≈ 6 lines
- **Notes**: Two `have this` with the same name (152, 154) — shadowing.

### `theorem diff_at_aux`
- **Type**: `(s : {z : ℂ | 0 < z.im}) (k : ℕ) (n : ℕ+) : DifferentiableAt ℂ (fun z => iteratedDerivWithin k (fun z => (z - n)⁻¹ + (z + n)⁻¹) {…} z) ↑s`
- **What**: The k-th derivative of a cotangent term is differentiable at every point of ℍ.
- **How**: `DifferentiableOn.congr (diff_on_aux k n)` with `iter_div_aut_add`, then `.differentiableAt` on the open set.
- **Hypotheses**: s ∈ ℍ.
- **Uses from project**: `diff_on_aux`, `iter_div_aut_add`, `upper_half_plane_isOpen`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 158–166, proof body ≈ 4 lines
- **Notes**: = mathlib `differentiableOn_iteratedDerivWithin_cotTerm` (`Cotangent.lean:330`) `.differentiableAt`. Dead project-wide.

### `theorem aut_series_ite_deriv_uexp2`
- **Type**: `(k : ℕ) (x : ℍ) : iteratedDerivWithin k (fun z => ∑' n : ℕ+, (1/(z - n) + 1/(z + n))) {…} x = ∑' n : ℕ+, iteratedDerivWithin k (fun z => 1/(z - n) + 1/(z + n)) {…} x`
- **What**: Termwise k-fold differentiation of the cotangent series.
- **How**: Rewrite ℕ+ sums as `∑' n, cotTerm z n` via `tsum_pnat_eq_tsum_succ`, then mathlib `iteratedDerivWithin_tsum` (`Mathlib/Topology/Algebra/InfiniteSum/TsumUniformlyOn.lean:93`) with `summable_cotTerm`, `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm`, `differentiableOn_iteratedDerivWithin_cotTerm`.
- **Hypotheses**: x ∈ ℍ.
- **Uses from project**: []
- **Used by**: `auxp_series_ite_deriv_uexp'''` (204)
- **Visibility**: public
- **Lines**: 168–188, proof body ≈ 16 lines
- **Notes**: Already fully mathlib-driven; it is the first `rw` of mathlib's private `aux_iteratedDeriv_tsum_cotTerm` (`Cotangent.lean:355`). Mixes `upperHalfPlaneSet` and `{z : ℂ | 0 < z.im}` spellings (`change` at 181).

### `theorem tsum_ider_der_eq`
- **Type**: `(k : ℕ) (x : {z : ℂ | 0 < z.im}) : ∑' n : ℕ+, iteratedDerivWithin k (…) {…} x = ∑' n : ℕ+, ((-1)^k * k! * (1/(x - n)^(k+1)) + (-1)^k * k! * (1/(x + n)^(k+1)))`
- **What**: Termwise closed form of the k-th derivatives.
- **How**: `tsum_congr` + `iter_div_aut_add`.
- **Hypotheses**: x ∈ ℍ.
- **Uses from project**: `iter_div_aut_add`
- **Used by**: `auxp_series_ite_deriv_uexp'''` (204)
- **Visibility**: public
- **Lines**: 190–195, proof body ≈ 1 line
- **Notes**: —

### `theorem auxp_series_ite_deriv_uexp'''`
- **Type**: `(k : ℕ) : EqOn (iteratedDerivWithin k (fun z => ∑' n : ℕ+, (1/(z - n) + 1/(z + n))) {…}) (fun x => ∑' n : ℕ+, ((-1)^k * k! * (1/(x - n)^(k+1)) + …)) {…}`
- **What**: `EqOn` closed form of the k-th derivative of the cotangent series.
- **How**: compose `aut_series_ite_deriv_uexp2` and `tsum_ider_der_eq`.
- **Hypotheses**: none.
- **Uses from project**: `aut_series_ite_deriv_uexp2`, `tsum_ider_der_eq`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 197–204, proof body ≈ 1 line
- **Notes**: Dead project-wide.

### `theorem tsum_aexp_contDiffOn`
- **Type**: `(k : ℕ) : ContDiffOn ℂ k (fun z : ℂ => ∑' n : ℕ+, (1/(z - n) + 1/(z + n))) {z | 0 < z.im}`
- **What**: The cotangent series is C^k on ℍ.
- **How**: `ContDiffOn.congr` from π cot(πz) − 1/z, whose smoothness is `cot_pi_mul_contDiffWithinAt` (`Cotangent.lean:145`) minus `contDiffWithinAt_const.div contDiffWithinAt_id`, using `cot_series_rep` (`Cotangent.lean:231`).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 206–216, proof body ≈ 9 lines
- **Notes**: Dead project-wide.

### `theorem aux_iter_der_tsum`
- **Type**: `(k : ℕ) (hk : 1 ≤ k) (x : ℍ) : iteratedDerivWithin k ((fun z => 1 / z) + fun z => ∑' n : ℕ+, (1/(z - n) + 1/(z + n))) {…} x = (-1)^k * k! * ∑' n : ℤ, 1 / ((x : ℂ) + n)^(k+1)`
- **What**: k-th derivative of 1/z + cotangent series equals (−1)^k k! ∑_{n∈ℤ} 1/(x+n)^{k+1}.
- **How**: mathlib `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow` (`Cotangent.lean:403`) + `iteratedDerivWithin_congr` with `cot_series_rep`.
- **Hypotheses**: k ≥ 1, x ∈ ℍ.
- **Uses from project**: []
- **Used by**: `aux_iter_der_tsum_eqOn` (235)
- **Visibility**: public
- **Lines**: 218–226, proof body ≈ 4 lines
- **Notes**: Wrapper.

### `theorem aux_iter_der_tsum_eqOn`
- **Type**: `(k : ℕ) (hk : 2 ≤ k) : EqOn (iteratedDerivWithin (k - 1) (…) {…}) (fun z => (-1)^(k-1) * (k-1)! * ∑' n : ℤ, 1/(z + n)^k) {…}`
- **What**: `EqOn` form with k−1 derivatives.
- **How**: previous lemma + `Nat.sub_add_cancel`.
- **Hypotheses**: k ≥ 2.
- **Uses from project**: `aux_iter_der_tsum`
- **Used by**: `q_exp_iden''` (264)
- **Visibility**: public
- **Lines**: 228–235, proof body ≈ 3 lines
- **Notes**: —

### `theorem pos_sum_eq`
- **Type**: `(k : ℕ) (hk : 0 < k) : (fun x => −(2πi) * ∑' n : ℕ, (2πi n)^k * exp (2πi n x)) = fun x => −(2πi) * ∑' n : ℕ+, (2πi n)^k * exp (2πi n x)`
- **What**: For k > 0 the n = 0 term vanishes so ℕ and ℕ+ sums agree.
- **How**: `tsum_pNat` (Basic.lean:54).
- **Hypotheses**: k > 0.
- **Uses from project**: `tsum_pNat`
- **Used by**: `q_exp_iden''` (267)
- **Visibility**: public
- **Lines**: 237–246, proof body ≈ 3 lines
- **Notes**: —

### `theorem cot_series_repr`
- **Type**: `(z : ℍ) : ↑π * cot (↑π * z) - 1 / z = ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n))`
- **What**: Rearranged cotangent partial-fraction expansion.
- **How**: `cot_series_rep` + `ring`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 248–251, proof body ≈ 2 lines
- **Notes**: Mathlib `cot_series_rep'` (`Cotangent.lean:224`) is this form (ℕ-indexed). Dead project-wide.

### `lemma EisensteinSeries_Identity`
- **Type**: `(z : ℍ) : 1 / z + ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / (z + n)) = π * Complex.I - 2 * π * Complex.I * ∑' n : ℕ, Complex.exp (2 * π * Complex.I * z) ^ n`
- **What**: Cotangent partial fractions equal the q-expansion of π cot(πz).
- **How**: `cot_series_rep` (`Cotangent.lean:231`) + `pi_mul_cot_pi_q_exp` (`Cotangent.lean:58`).
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: `q_exp_iden''` (271)
- **Visibility**: public
- **Lines**: 253–256, proof body ≈ 1 line
- **Notes**: Misleading name (it's the cotangent identity, not an Eisenstein one).

### `theorem q_exp_iden''`
- **Type**: `(k : ℕ) (hk : 2 ≤ k) : EqOn (fun z => (-1)^(k-1) * (k-1)! * ∑' d : ℤ, 1/(z + d)^k) (fun z => −(2πi) * ∑' n : ℕ+, (2πi n)^(k-1) * exp (2πi n z)) {z | 0 < z.im}`
- **What**: Lipschitz formula as an `EqOn` of (k−1)-st derivatives of the two representations.
- **How**: `aux_iter_der_tsum_eqOn`, `iter_exp_eqOn`, `pos_sum_eq`, and `iteratedDerivWithin_congr` via `EisensteinSeries_Identity`.
- **Hypotheses**: k ≥ 2.
- **Uses from project**: `aux_iter_der_tsum_eqOn`, `iter_exp_eqOn`, `pos_sum_eq`, `EisensteinSeries_Identity`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 258–271, proof body ≈ 8 lines
- **Notes**: This is the argument of mathlib `EisensteinSeries.qExpansion_identity` (`EisensteinSeries/QExpansion.lean:175`). Dead project-wide (not even used by `q_exp_iden`).

### `theorem q_exp_iden`
- **Type**: `(k : ℕ) (hk : 2 ≤ k) (z : ℍ) : ∑' d : ℤ, 1 / ((z : ℂ) + d) ^ k = (-2 * ↑π * Complex.I) ^ k / (k - 1)! * ∑' n : ℕ+, n ^ ((k - 1)) * Complex.exp (2 * ↑π * Complex.I * z * n)`
- **What**: Lipschitz formula ∑_{d∈ℤ} (z+d)^{−k} = (−2πi)^k/(k−1)! ∑_{n≥1} n^{k−1} qⁿ.
- **How**: mathlib `EisensteinSeries.qExpansion_identity_pnat` (`EisensteinSeries/QExpansion.lean:204`) at k−1, plus `Complex.exp_nat_mul` normalisation.
- **Hypotheses**: k ≥ 2.
- **Uses from project**: []
- **Used by**: unused in file (only mentioned in the module docstring, line 16)
- **Visibility**: public
- **Lines**: 274–280, proof body ≈ 3 lines
- **Notes**: Wrapper; the 10 preceding lemmas that were its original proof are now orphaned. Dead project-wide.

### `lemma t9`
- **Type**: `(z : ℍ) : ∑' m : ℕ, (2 * (-2πi)^2 / (2-1)! * ∑' n : ℕ+, n^(2-1) * exp (2πi (m+1) z n)) = -8 * π^2 * ∑' (n : ℕ+), (sigma 1 n) * cexp (2πi n z)`
- **What**: The k = 2 Lambert rearrangement ∑_m ∑_n n q^{(m+1)n} = ∑ σ₁(n) qⁿ with the constant 2(−2πi)² = −8π².
- **How**: `tsum_prod_pow_eq_tsum_sigma 1` (`TsumDivisorsAntidiagonal.lean:106`) + `tsum_pnat_eq_tsum_succ`, `tsum_mul_left`, `Complex.I_sq`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 282–295, proof body ≈ 12 lines
- **Notes**: Junk name. The downstream fact is mathlib `EisensteinSeries.G2_eq_tsum_cexp` (`E2/Summable.lean:97`). Dead project-wide.

## File Summary
- Total declarations: 25 (0 defs, 25 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): none (max fan-in 2: `exp_series_ite_deriv_uexp''`)
- Unused declarations (not used by anything in this file): `summable_iter_derv'`, `exp_series_ite_deriv_uexp'''`, `tsum_uexp_contDiffOn`, `summable_iter_aut`, `aut_bound_on_comp`, `diff_at_aux`, `auxp_series_ite_deriv_uexp'''`, `tsum_aexp_contDiffOn`, `cot_series_repr`, `q_exp_iden''`, `q_exp_iden`, `t9` — and NO declaration of this file is used anywhere else in the project (grep -rnw over XYin, excluding the batch)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (`aut_bound_on_comp` 25, `aut_series_ite_deriv_uexp2` 16)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `q_exp_iden` (274) = `EisensteinSeries.qExpansion_identity_pnat` (`Mathlib/NumberTheory/ModularForms/EisensteinSeries/QExpansion.lean:204`); `q_exp_iden''` (258) = the proof of `EisensteinSeries.qExpansion_identity` (:175). Everything from line 27 to 271 is the by-hand proof that mathlib now ships.
- `exp_series_ite_deriv_uexp2` (34) = `iteratedDerivWithin_tsum_cexp_eq` (:128); `tsum_uexp_contDiffOn` (55) = `contDiffOn_tsum_cexp` (:138); `summable_iter_derv'` (27) = `summable_pow_mul_cexp` (:192); `iter_der_within_add`/`iter_exp_eqOn` (60/72) = private `iteratedDerivWithin_tsum_exp_aux_eq` (:146).
- `aux_iter_der_tsum` (218) = `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow` (`Mathlib/Analysis/SpecialFunctions/Trigonometric/Cotangent.lean:403`); `tsum_aexp_contDiffOn` (206) = `cot_pi_mul_contDiffWithinAt` (:145); `cot_series_repr` (248) = `cot_series_rep'` (:224); `EisensteinSeries_Identity` (253) = `cot_series_rep` (:231) + `pi_mul_cot_pi_q_exp` (:58).
- `summable_iter_aut` (83), `sub_bound`/`add_bound`/`aut_bound_on_comp` (90–145), `diff_on_aux`/`diff_at_aux` (148–166) = `summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm` (:320), private `iteratedDerivWithin_cotTerm_bounded_uniformly` (:302), `differentiableOn_iteratedDerivWithin_cotTerm` (:330). `aut_series_ite_deriv_uexp2` (168) already IS mathlib's argument (`iteratedDerivWithin_tsum`, TsumUniformlyOn.lean:93).
- `t9` (282) = `tsum_prod_pow_eq_tsum_sigma` (`TsumDivisorsAntidiagonal.lean:106`); its consumer is `G2_eq_tsum_cexp` (`E2/Summable.lean:97`).
- Hand-rolled uniform-bound pattern: `aut_bound_on_comp` (120–145) constructs an explicit `∃ u, Summable u ∧ ∀ n (s : K), ‖…‖ ≤ u n` majorant; mathlib phrases this as `SummableLocallyUniformlyOn` via `SummableLocallyUniformlyOn_of_locally_bounded` (`TsumUniformlyOn.lean:56`).
### Missing API / repeated patterns
- `sub_bound` (90–103) and `add_bound` (105–118): 13 identical lines; one lemma parametrised by `(ε : ℤ) (hε : ε = 1 ∨ ε = -1)` or, better, use mathlib's `abs_norm_eq_max_natAbs`/`_neg` (`Summable.lean:54/59`) and `summand_bound_of_mem_verticalStrip` directly.
- `simpa [← Complex.exp_nat_mul, mul_comm, mul_left_comm, mul_assoc]` normalisation appears at 30, 39, 57, 270, 278–279, 295 — the file fights mathlib's `cexp (2πI z) ^ n` normal form throughout.
- Three spellings of the same set: `ℍ'` (27, 50, 56), `{z : ℂ | 0 < z.im}` (34–246 passim), `upperHalfPlaneSet` (179–184); `change` at 181 exists only to reconcile them.
- `EqOn` doubles: `exp_series_ite_deriv_uexp''`→`'''` (42/49), `iter_der_within_add`→`iter_exp_eqOn` (60/72), `aux_iter_der_tsum`→`_eqOn` (218/228), `aut_series_ite_deriv_uexp2`+`tsum_ider_der_eq`→`auxp_series_ite_deriv_uexp'''` — a pattern that `Set.EqOn` + `fun x hx ↦` handles inline.
### Junk candidates
- Whole file is dead project-wide (its only importer `Eisensteinqexpansions.lean` uses none of it). Candidates for deletion: all 25; at minimum `q_exp_iden''`, `t9`, `cot_series_repr`, `summable_iter_derv'`, `exp_series_ite_deriv_uexp'''`, `tsum_uexp_contDiffOn`, `summable_iter_aut`, `aut_bound_on_comp`, `diff_at_aux`, `auxp_series_ite_deriv_uexp'''`, `tsum_aexp_contDiffOn` (unused even inside the file).
- Names: `t9`, `q_exp_iden''`, `exp_series_ite_deriv_uexp2/''/'''`, `auxp_…`, `aux_iter_der_tsum`, `diff_on_aux`, `diff_at_aux` — none mathlib-style.
- Shadowed `have this` twice at 152/154. Blank-line noise at 146–147, 272–273.
### Moral duplicates within this batch
- `sub_bound` vs `add_bound` (exact).
- `exp_series_ite_deriv_uexp''` (42) vs tsumderivWithin.lean `der_iter_eq_der_aux2`'s closed form (76) vs iteratedderivs.lean `exp_iter_deriv_within` (65): same derivative formula for `exp(2πi n z)` at three levels.
- `diff_on_aux`/`diff_at_aux` (148–166) vs tsumderivWithin.lean `der_iter_eq_der_aux2` (76): same `DifferentiableOn.congr (closed form)` skeleton.
- `aut_bound_on_comp` (120) vs tsumderivWithin.lean `iter_deriv_comp_bound2` (129): same "∃ summable majorant on compact K" shape for the two series.
### Generalization notes
- `iter_der_within_add`, `iter_exp_eqOn`, `pos_sum_eq`: `k : ℕ+` is only used as `0 < k`; mathlib states `1 ≤ k` on `k : ℕ`.
- `summable_iter_derv'` and the exponential lemmas depend only on `‖cexp (2πi y)‖ < 1`, i.e. on `Im y > 0`; the `ℍ'` subtype is incidental.
- `sub_bound`/`add_bound`: hold for any `s` in the strip; `ℍ` is only used to build `⟨⟨A,B⟩,hB⟩ : ℍ` for `r`.
