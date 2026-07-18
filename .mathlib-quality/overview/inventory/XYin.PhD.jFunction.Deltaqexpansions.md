# Source: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/jFunction/Deltaqexpansions.lean — project imports: `XYin.PhD.IntegralPowerSeries.IntegralPowerSeries`, `XYin.PhD.Modularforms.Eisenstein`

### `abbrev E4`
- **Type**: `abbrev E4 := _root_.E₄` (a `ModularForm (CongruenceSubgroup.Gamma 1) 4`)
- **What**: Local abbreviation for the project's normalized weight-4 Eisenstein series E₄ (constant term 1, q-expansion 1 + 240·Σσ₃(n)qⁿ).
- **How**: Direct abbreviation of the root-level `E₄` from the project's Eisenstein file; no proof.
- **Hypotheses**: none.
- **Uses from project**: [`E₄` (XYin.PhD.Modularforms.Eisenstein)]
- **Used by**: `E4_qExpansion_coeff_aux`, `E4_isIntegralPowerSeries`, `E4_pow_three_isIntegralPowerSeries`, `map_integralE4_pow_three_sub_integralE6_pow_two`, `eisenstein_difference_isIntegralPowerSeries_aux`, `Delta_qExpansion_eq_smul_eisenstein_difference`, `Delta_isIntegralPowerSeries` (via rewrite)
- **Visibility**: public
- **Lines**: 36 (1 line)
- **Notes**: none

### `abbrev E6`
- **Type**: `abbrev E6 := _root_.E₆` (a `ModularForm (CongruenceSubgroup.Gamma 1) 6`)
- **What**: Local abbreviation for the project's normalized weight-6 Eisenstein series E₆ (q-expansion 1 − 504·Σσ₅(n)qⁿ).
- **How**: Direct abbreviation of the root-level `E₆` from the project's Eisenstein file; no proof.
- **Hypotheses**: none.
- **Uses from project**: [`E₆` (XYin.PhD.Modularforms.Eisenstein)]
- **Used by**: `E6_qExpansion_coeff_aux`, `E6_isIntegralPowerSeries`, `map_integralE4_pow_three_sub_integralE6_pow_two`, `eisenstein_difference_isIntegralPowerSeries_aux`, `Delta_qExpansion_eq_smul_eisenstein_difference`
- **Visibility**: public
- **Lines**: 39 (1 line)
- **Notes**: none

### `lemma E4_qExpansion_coeff_aux`
- **Type**: `(n : ℕ) : (qExpansion 1 E4).coeff n = if n = 0 then 1 else (240 : ℂ) * sigma 3 n`
- **What**: Closed formula for the n-th q-expansion coefficient of E₄: constant term 1, and 240·σ₃(n) for n ≥ 1.
- **How**: Rewrites via mathlib's `EisensteinSeries.E_qExpansion_coeff` (general normalized-Eisenstein coefficient formula −2k/B_k·σ_{k−1}(n)) and evaluates the Bernoulli number via `bernoulli_eq_bernoulli'_of_ne_one` and `bernoulli'_four` (−8/B₄ = 240).
- **Hypotheses**: none (weight-4 side conditions `3 ≤ 4` and evenness `⟨2, rfl⟩` discharged inline).
- **Uses from project**: [`E4`]
- **Used by**: `E4_isIntegralPowerSeries`, `integralE4_coeff_dvd_aux`, `integralE4_coeff_zero`, `integralE4_coeff_of_pos`
- **Visibility**: private
- **Lines**: 41–48 (7-line proof)
- **Notes**: none

### `lemma E6_qExpansion_coeff_aux`
- **Type**: `(n : ℕ) : (qExpansion 1 E6).coeff n = if n = 0 then 1 else -(504 : ℂ) * sigma 5 n`
- **What**: Closed formula for the n-th q-expansion coefficient of E₆: constant term 1, and −504·σ₅(n) for n ≥ 1.
- **How**: Same route as `E4_qExpansion_coeff_aux`: mathlib's `EisensteinSeries.E_qExpansion_coeff` at weight 6 plus `bernoulli'_six` (−12/B₆ = −504).
- **Hypotheses**: none.
- **Uses from project**: [`E6`]
- **Used by**: `E6_isIntegralPowerSeries`, `integralE6_coeff_dvd_aux`, `integralE6_coeff_zero`, `integralE6_coeff_of_pos`
- **Visibility**: private
- **Lines**: 50–57 (7-line proof)
- **Notes**: none

### `lemma E4_isIntegralPowerSeries`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 E4)`
- **What**: The q-expansion of E₄ has integer coefficients (each complex coefficient is the image of an integer).
- **How**: Via the coefficient-wise criterion `int_iff` and the explicit formula `E4_qExpansion_coeff_aux`; the witnesses are 1 and 240·σ₃(n), which are visibly integers.
- **Hypotheses**: none.
- **Uses from project**: [`IsIntegralPowerSeries`, `int_iff`, `E4_qExpansion_coeff_aux`, `E4`]
- **Used by**: `integralE4`, `E4_pow_three_isIntegralPowerSeries`, `integralE4_coeff_dvd_aux`, `integralE4_coeff_zero`, `integralE4_coeff_of_pos`, `map_integralE4_pow_three_sub_integralE6_pow_two`
- **Visibility**: public
- **Lines**: 60–67 (7-line proof)
- **Notes**: none

### `lemma E6_isIntegralPowerSeries`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 E6)`
- **What**: The q-expansion of E₆ has integer coefficients.
- **How**: Same as for E₄: `int_iff` plus `E6_qExpansion_coeff_aux`, with integer witnesses 1 and −504·σ₅(n).
- **Hypotheses**: none.
- **Uses from project**: [`IsIntegralPowerSeries`, `int_iff`, `E6_qExpansion_coeff_aux`, `E6`]
- **Used by**: `integralE6`, `integralE6_coeff_dvd_aux`, `integralE6_coeff_zero`, `integralE6_coeff_of_pos`, `map_integralE4_pow_three_sub_integralE6_pow_two`
- **Visibility**: public
- **Lines**: 70–77 (7-line proof)
- **Notes**: none

### `def integralE4`
- **Type**: `integralE4 : PowerSeries ℤ`
- **What**: The integral lift of the q-expansion of E₄, i.e. the ℤ-power series 1 + 240·Σσ₃(n)qⁿ.
- **How**: Applies the project's choice function `toIntegralPowerSeries` to the integrality witness `E4_isIntegralPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: [`toIntegralPowerSeries`, `E4_isIntegralPowerSeries`]
- **Used by**: `integralE4_coeff_dvd_aux`, `integralE4_coeff_zero`, `integralE4_constantCoeff_aux`, `integralE4_coeff_of_pos`, `e4Bar`, `eisenstein_difference_modEq_linear_aux`, `linear_coeff_eq_aux`, `eisenstein_difference_modEq_aux`, `eisenstein_difference_coeff_dvd_aux`, `map_integralE4_pow_three_sub_integralE6_pow_two`, `eisenstein_difference_isIntegralPowerSeries_aux`, `toIntegralPowerSeries_eisenstein_difference_aux`, `eisenstein_difference_coeff_modEq_zero`
- **Visibility**: public
- **Lines**: 80 (1 line)
- **Notes**: none

### `def integralE6`
- **Type**: `integralE6 : PowerSeries ℤ`
- **What**: The integral lift of the q-expansion of E₆, i.e. the ℤ-power series 1 − 504·Σσ₅(n)qⁿ.
- **How**: Applies `toIntegralPowerSeries` to `E6_isIntegralPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: [`toIntegralPowerSeries`, `E6_isIntegralPowerSeries`]
- **Used by**: `integralE6_coeff_dvd_aux`, `integralE6_coeff_zero`, `integralE6_constantCoeff_aux`, `integralE6_coeff_of_pos`, `e6Bar`, `eisenstein_difference_modEq_linear_aux`, `linear_coeff_eq_aux`, `eisenstein_difference_modEq_aux`, `eisenstein_difference_coeff_dvd_aux`, `map_integralE4_pow_three_sub_integralE6_pow_two`, `eisenstein_difference_isIntegralPowerSeries_aux`, `toIntegralPowerSeries_eisenstein_difference_aux`, `eisenstein_difference_coeff_modEq_zero`
- **Visibility**: public
- **Lines**: 83 (1 line)
- **Notes**: none

### `lemma E4_pow_three_isIntegralPowerSeries`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 (E4 ^ 3))`
- **What**: The q-expansion of E₄³ has integer coefficients.
- **How**: Converts qExpansion of a power into the power of the qExpansion via mathlib's `ModularForm.qExpansion_pow` (through `DirectSum.ofPow`), then closes under multiplication in the subring of integral power series via `IntegralPowerSeriesSubring.pow_mem` (mathlib's `Subring.pow_mem` on the project subring).
- **Hypotheses**: none.
- **Uses from project**: [`IsIntegralPowerSeries`, `E4`, `E4_isIntegralPowerSeries`, `IntegralPowerSeriesSubring`]
- **Used by**: unused in file (used by `qj_isIntegralPowerSeries_aux` in jfunction.lean)
- **Visibility**: public
- **Lines**: 86–90 (4-line proof)
- **Notes**: none

### `lemma Delta_qExpansion_coeff_zero_aux`
- **Type**: `(qExpansion 1 Delta).coeff 0 = 0`
- **What**: The constant term of the q-expansion of the discriminant cusp form Δ vanishes.
- **How**: Immediate from mathlib's `CuspFormClass.cuspFunction_apply_zero` (cusp forms vanish at the cusp), unfolding `qExpansion_coeff`.
- **Hypotheses**: none.
- **Uses from project**: [`Delta`]
- **Used by**: unused in file
- **Visibility**: private
- **Lines**: 92–94 (2-line proof)
- **Notes**: dead code — the same fact is re-proved inline in jfunction.lean rather than reusing this lemma

### `lemma three_dvd_weighted_powers_aux`
- **Type**: `(d : ℕ) : 3 ∣ (5 * d ^ 3 + 7 * d ^ 5)`
- **What**: 3 divides 5d³ + 7d⁵ for every natural number d.
- **How**: Reduces mod 3 (`ZMod 3`) and checks all three residues by `decide`; transfers back with `ZMod.intCast_zmod_eq_zero_iff_dvd`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `twelve_dvd_weighted_powers_aux`
- **Visibility**: private
- **Lines**: 96–100 (4-line proof)
- **Notes**: none

### `lemma four_dvd_weighted_powers_aux`
- **Type**: `(d : ℕ) : 4 ∣ (5 * d ^ 3 + 7 * d ^ 5)`
- **What**: 4 divides 5d³ + 7d⁵ for every natural number d.
- **How**: Same finite check in `ZMod 4` by `decide`, transferred via `ZMod.intCast_zmod_eq_zero_iff_dvd`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `twelve_dvd_weighted_powers_aux`
- **Visibility**: private
- **Lines**: 102–106 (4-line proof)
- **Notes**: none

### `lemma twelve_dvd_weighted_powers_aux`
- **Type**: `(d : ℕ) : 12 ∣ (5 * d ^ 3 + 7 * d ^ 5)`
- **What**: 12 divides 5d³ + 7d⁵ for every natural number d.
- **How**: Combines the mod-3 and mod-4 divisibilities via coprimality: `Nat.Coprime.mul_dvd_of_dvd_of_dvd` with gcd(3,4)=1.
- **Hypotheses**: none.
- **Uses from project**: [`three_dvd_weighted_powers_aux`, `four_dvd_weighted_powers_aux`]
- **Used by**: `twelve_dvd_weighted_sigma_aux`
- **Visibility**: private
- **Lines**: 108–111 (3-line proof)
- **Notes**: none

### `lemma twelve_dvd_weighted_sigma_aux`
- **Type**: `(n : ℕ) : 12 ∣ 5 * sigma 3 n + 7 * sigma 5 n`
- **What**: 12 divides 5σ₃(n) + 7σ₅(n) — the classical congruence behind the integrality of Δ = (E₄³−E₆²)/1728.
- **How**: Expands both `ArithmeticFunction.sigma_apply` into sums over divisors and applies the term-wise divisibility `twelve_dvd_weighted_powers_aux` through `Finset.dvd_sum`.
- **Hypotheses**: none.
- **Uses from project**: [`twelve_dvd_weighted_powers_aux`]
- **Used by**: `eisenstein_difference_coeff_dvd_aux`
- **Visibility**: private
- **Lines**: 113–121 (8-line proof)
- **Notes**: none

### `lemma integralE4_coeff_dvd_aux`
- **Type**: `(n : ℕ) (hn : 1 ≤ n) : 240 ∣ integralE4.coeff n`
- **What**: Every positive-index coefficient of the integral E₄ series is divisible by 240.
- **How**: Transfers the complex coefficient formula `E4_qExpansion_coeff_aux` to ℤ through the coercion identity `coeTo_of_toIntegralPowerSeries` and injectivity of ℤ → ℂ (`exact_mod_cast`); the coefficient is literally 240·σ₃(n).
- **Hypotheses**: n ≥ 1.
- **Uses from project**: [`coeTo_of_toIntegralPowerSeries`, `E4_isIntegralPowerSeries`, `E4_qExpansion_coeff_aux`, `integralE4`]
- **Used by**: `e4Bar_coeff_dvd_aux`
- **Visibility**: private
- **Lines**: 123–130 (7-line proof)
- **Notes**: none

### `lemma integralE6_coeff_dvd_aux`
- **Type**: `(n : ℕ) (hn : 1 ≤ n) : 504 ∣ integralE6.coeff n`
- **What**: Every positive-index coefficient of the integral E₆ series is divisible by 504.
- **How**: Same cast transfer via `coeTo_of_toIntegralPowerSeries` and `E6_qExpansion_coeff_aux`; the coefficient is −504·σ₅(n), witness −σ₅(n).
- **Hypotheses**: n ≥ 1.
- **Uses from project**: [`coeTo_of_toIntegralPowerSeries`, `E6_isIntegralPowerSeries`, `E6_qExpansion_coeff_aux`, `integralE6`]
- **Used by**: `e6Bar_coeff_dvd_aux`
- **Visibility**: private
- **Lines**: 132–142 (10-line proof)
- **Notes**: none

### `lemma integralE4_coeff_zero`
- **Type**: `integralE4.coeff 0 = 1`
- **What**: The constant term of the integral E₄ series is 1.
- **How**: Casts the complex constant term (which is 1 by `E4_qExpansion_coeff_aux`) back to ℤ using `coeTo_of_toIntegralPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: [`coeTo_of_toIntegralPowerSeries`, `E4_isIntegralPowerSeries`, `E4_qExpansion_coeff_aux`, `integralE4`]
- **Used by**: `integralE4_constantCoeff_aux`
- **Visibility**: public
- **Lines**: 144–149 (5-line proof)
- **Notes**: none

### `lemma integralE6_coeff_zero`
- **Type**: `integralE6.coeff 0 = 1`
- **What**: The constant term of the integral E₆ series is 1.
- **How**: Same cast argument via `coeTo_of_toIntegralPowerSeries` and `E6_qExpansion_coeff_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`coeTo_of_toIntegralPowerSeries`, `E6_isIntegralPowerSeries`, `E6_qExpansion_coeff_aux`, `integralE6`]
- **Used by**: `integralE6_constantCoeff_aux`
- **Visibility**: public
- **Lines**: 151–156 (5-line proof)
- **Notes**: none

### `lemma integralE4_constantCoeff_aux`
- **Type**: `PowerSeries.constantCoeff integralE4 = 1`
- **What**: Restatement of `integralE4_coeff_zero` through `constantCoeff` instead of `coeff 0`.
- **How**: `PowerSeries.coeff_zero_eq_constantCoeff` rewrite of `integralE4_coeff_zero`.
- **Hypotheses**: none.
- **Uses from project**: [`integralE4_coeff_zero`, `integralE4`]
- **Used by**: `e4Bar_coeff_dvd_aux`, `eisenstein_difference_modEq_aux`
- **Visibility**: private
- **Lines**: 158–159 (1-line proof)
- **Notes**: none

### `lemma integralE6_constantCoeff_aux`
- **Type**: `PowerSeries.constantCoeff integralE6 = 1`
- **What**: Restatement of `integralE6_coeff_zero` through `constantCoeff`.
- **How**: `PowerSeries.coeff_zero_eq_constantCoeff` rewrite of `integralE6_coeff_zero`.
- **Hypotheses**: none.
- **Uses from project**: [`integralE6_coeff_zero`, `integralE6`]
- **Used by**: `e6Bar_coeff_dvd_aux`, `eisenstein_difference_modEq_aux`
- **Visibility**: private
- **Lines**: 161–162 (1-line proof)
- **Notes**: none

### `lemma integralE4_coeff_of_pos`
- **Type**: `(n : ℕ) (hn : 1 ≤ n) : integralE4.coeff n = (240 : ℤ) * sigma 3 n`
- **What**: Exact integer formula 240·σ₃(n) for the positive-index coefficients of the integral E₄ series.
- **How**: Cast transfer of `E4_qExpansion_coeff_aux` through `coeTo_of_toIntegralPowerSeries` and ℤ→ℂ injectivity.
- **Hypotheses**: n ≥ 1.
- **Uses from project**: [`coeTo_of_toIntegralPowerSeries`, `E4_isIntegralPowerSeries`, `E4_qExpansion_coeff_aux`, `integralE4`]
- **Used by**: `linear_coeff_eq_aux`
- **Visibility**: public
- **Lines**: 164–170 (6-line proof)
- **Notes**: none

### `lemma integralE6_coeff_of_pos`
- **Type**: `(n : ℕ) (hn : 1 ≤ n) : integralE6.coeff n = -((504 : ℤ) * sigma 5 n)`
- **What**: Exact integer formula −504·σ₅(n) for the positive-index coefficients of the integral E₆ series.
- **How**: Cast transfer of `E6_qExpansion_coeff_aux` through `coeTo_of_toIntegralPowerSeries`.
- **Hypotheses**: n ≥ 1.
- **Uses from project**: [`coeTo_of_toIntegralPowerSeries`, `E6_isIntegralPowerSeries`, `E6_qExpansion_coeff_aux`, `integralE6`]
- **Used by**: `linear_coeff_eq_aux`
- **Visibility**: public
- **Lines**: 172–178 (6-line proof)
- **Notes**: none

### `def e4Bar`
- **Type**: `e4Bar : PowerSeries ℤ` (`:= integralE4 - 1`)
- **What**: The positive-degree part Ē₄ = integralE4 − 1 of the integral E₄ series; every coefficient is divisible by 240.
- **How**: Definition by subtraction of the constant series 1.
- **Hypotheses**: none.
- **Uses from project**: [`integralE4`]
- **Used by**: `e4Bar_coeff_dvd_aux`, `remainder_coeff_dvd_aux`, `eisenstein_difference_modEq_linear_aux`, `linear_coeff_eq_aux`
- **Visibility**: private
- **Lines**: 180 (1 line)
- **Notes**: none

### `def e6Bar`
- **Type**: `e6Bar : PowerSeries ℤ` (`:= integralE6 - 1`)
- **What**: The positive-degree part Ē₆ = integralE6 − 1; every coefficient is divisible by 504.
- **How**: Definition by subtraction of the constant series 1.
- **Hypotheses**: none.
- **Uses from project**: [`integralE6`]
- **Used by**: `e6Bar_coeff_dvd_aux`, `remainder_coeff_dvd_aux`, `eisenstein_difference_modEq_linear_aux`, `linear_coeff_eq_aux`
- **Visibility**: private
- **Lines**: 182 (1 line)
- **Notes**: none

### `lemma e4Bar_coeff_dvd_aux`
- **Type**: `(m : ℕ) : 240 ∣ e4Bar.coeff m`
- **What**: Every coefficient of Ē₄ (including the constant term, which is 0) is divisible by 240.
- **How**: Case split m = 0 (constant term vanishes by `integralE4_constantCoeff_aux`) versus m ≥ 1 (apply `integralE4_coeff_dvd_aux`; subtracting 1 doesn't change positive coefficients).
- **Hypotheses**: none.
- **Uses from project**: [`e4Bar`, `integralE4_constantCoeff_aux`, `integralE4_coeff_dvd_aux`]
- **Used by**: `remainder_coeff_dvd_aux`
- **Visibility**: private
- **Lines**: 184–187 (3-line proof)
- **Notes**: none

### `lemma e6Bar_coeff_dvd_aux`
- **Type**: `(m : ℕ) : 504 ∣ e6Bar.coeff m`
- **What**: Every coefficient of Ē₆ is divisible by 504.
- **How**: Same case split as `e4Bar_coeff_dvd_aux`, using `integralE6_constantCoeff_aux` and `integralE6_coeff_dvd_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`e6Bar`, `integralE6_constantCoeff_aux`, `integralE6_coeff_dvd_aux`]
- **Used by**: `remainder_coeff_dvd_aux`
- **Visibility**: private
- **Lines**: 189–192 (3-line proof)
- **Notes**: none

### `lemma coeff_mul_dvd_aux`
- **Type**: `(a b : ℤ) (f g : PowerSeries ℤ) (hf : ∀ m, a ∣ f.coeff m) (hg : ∀ m, b ∣ g.coeff m) : ∀ m, a * b ∣ (f * g).coeff m`
- **What**: If a divides every coefficient of f and b every coefficient of g, then ab divides every coefficient of fg — a Cauchy-product divisibility principle.
- **How**: Expands `PowerSeries.coeff_mul` into the antidiagonal sum and applies `Finset.dvd_sum` with the factor-wise witnesses.
- **Hypotheses**: coefficient-wise divisibility of f by a and g by b.
- **Uses from project**: []
- **Used by**: `remainder_coeff_dvd_aux`
- **Visibility**: private
- **Lines**: 194–204 (9-line proof)
- **Notes**: general-purpose lemma; a candidate for extraction to the IntegralPowerSeries module

### `lemma remainder_coeff_dvd_aux`
- **Type**: `(n : ℕ) : (1728 : ℤ) ∣ (e4Bar ^ 3 + 3 * e4Bar ^ 2 - e6Bar ^ 2).coeff n`
- **What**: 1728 divides every coefficient of the "quadratic remainder" Ē₄³ + 3Ē₄² − Ē₆² left after subtracting the linear term from E₄³ − E₆².
- **How**: Applies `coeff_mul_dvd_aux` to get 240² ∣ Ē₄², 240³ ∣ Ē₄³ and 504² ∣ Ē₆², then uses 1728 ∣ 240³, 1728 ∣ 3·240², 1728 ∣ 504² (by `norm_num`) and closes with `Int.dvd_add`/`Int.dvd_sub`.
- **Hypotheses**: none.
- **Uses from project**: [`coeff_mul_dvd_aux`, `e4Bar`, `e6Bar`, `e4Bar_coeff_dvd_aux`, `e6Bar_coeff_dvd_aux`]
- **Used by**: `eisenstein_difference_modEq_linear_aux`
- **Visibility**: private
- **Lines**: 206–237 (31-line proof)
- **Notes**: proof >30 lines

### `lemma eisenstein_difference_modEq_linear_aux`
- **Type**: `(n : ℕ) : Int.ModEq 1728 ((integralE4 ^ 3 - integralE6 ^ 2).coeff n) ((3 * e4Bar - 2 * e6Bar).coeff n)`
- **What**: Coefficient-wise, E₄³ − E₆² is congruent mod 1728 to its linearization 3Ē₄ − 2Ē₆ (from the binomial expansion (Ē₄+1)³ − (Ē₆+1)² = Ē₄³ + 3Ē₄² + 3Ē₄ − Ē₆² − 2Ē₆).
- **How**: The polynomial identity (proved by `ring` after substituting integralE4 = Ē₄ + 1, integralE6 = Ē₆ + 1) shows the difference of the two sides equals the remainder Ē₄³ + 3Ē₄² − Ē₆², whose coefficients are divisible by 1728 by `remainder_coeff_dvd_aux`; concludes with `Int.modEq_iff_dvd`.
- **Hypotheses**: none.
- **Uses from project**: [`integralE4`, `integralE6`, `e4Bar`, `e6Bar`, `remainder_coeff_dvd_aux`]
- **Used by**: `eisenstein_difference_modEq_aux`
- **Visibility**: private
- **Lines**: 239–261 (22-line proof)
- **Notes**: none

### `lemma linear_coeff_eq_aux`
- **Type**: `(n : ℕ) (hn0 : n ≠ 0) : ((3 * e4Bar - 2 * e6Bar).coeff n) = 144 * (5 * sigma 3 n + 7 * sigma 5 n)`
- **What**: The positive-index coefficients of the linearization 3Ē₄ − 2Ē₆ equal 144·(5σ₃(n) + 7σ₅(n)) — i.e. 3·240σ₃(n) + 2·504σ₅(n).
- **How**: Computes coefficients via `PowerSeries.coeff_C_mul` and substitutes the explicit formulas `integralE4_coeff_of_pos` and `integralE6_coeff_of_pos`; final arithmetic by `ring`.
- **Hypotheses**: n ≠ 0.
- **Uses from project**: [`e4Bar`, `e6Bar`, `integralE4`, `integralE6`, `integralE4_coeff_of_pos`, `integralE6_coeff_of_pos`]
- **Used by**: `eisenstein_difference_modEq_aux`
- **Visibility**: private
- **Lines**: 263–278 (15-line proof)
- **Notes**: none

### `lemma eisenstein_difference_modEq_aux`
- **Type**: `(n : ℕ) : Int.ModEq 1728 ((integralE4 ^ 3 - integralE6 ^ 2).coeff n) (144 * (5 * sigma 3 n + 7 * sigma 5 n))`
- **What**: Each coefficient of E₄³ − E₆² is congruent to 144(5σ₃(n)+7σ₅(n)) mod 1728, including n = 0 where both sides vanish.
- **How**: For n = 0 both constant terms are 0 (1³ − 1² = 0 via `integralE4_constantCoeff_aux`/`integralE6_constantCoeff_aux`, and σ(0) = 0); for n > 0 chains `eisenstein_difference_modEq_linear_aux` with the identification `linear_coeff_eq_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`integralE4`, `integralE6`, `integralE4_constantCoeff_aux`, `integralE6_constantCoeff_aux`, `linear_coeff_eq_aux`, `eisenstein_difference_modEq_linear_aux`]
- **Used by**: `eisenstein_difference_coeff_dvd_aux`
- **Visibility**: private
- **Lines**: 280–287 (7-line proof)
- **Notes**: none

### `lemma eisenstein_difference_coeff_dvd_aux`
- **Type**: `(n : ℕ) : 1728 ∣ (integralE4 ^ 3 - integralE6 ^ 2).coeff n`
- **What**: The key divisibility: 1728 divides every coefficient of the integral series E₄³ − E₆², so Δ = (E₄³−E₆²)/1728 is integral.
- **How**: 12 ∣ 5σ₃(n)+7σ₅(n) (`twelve_dvd_weighted_sigma_aux`) gives 1728 = 144·12 ∣ 144(5σ₃+7σ₅); combined with the congruence `eisenstein_difference_modEq_aux` and `Int.modEq_zero_iff_dvd`.
- **Hypotheses**: none.
- **Uses from project**: [`eisenstein_difference_modEq_aux`, `twelve_dvd_weighted_sigma_aux`, `integralE4`, `integralE6`]
- **Used by**: `eisenstein_difference_coeff_modEq_zero`
- **Visibility**: private
- **Lines**: 289–304 (15-line proof)
- **Notes**: none

### `lemma map_integralE4_pow_three_sub_integralE6_pow_two`
- **Type**: `(coeToComplexPowerSeries.ringHom ℤ) (integralE4 ^ 3 - integralE6 ^ 2) = qExpansion 1 (E4 ^ 3 - E6 ^ 2)`
- **What**: The complexification of the integral series E₄³ − E₆² is exactly the q-expansion of the modular form E₄³ − E₆² (as a function on ℍ).
- **How**: Pushes the ring hom through powers and subtraction (`map_pow`, `map_sub`), identifies the complexified factors via `coeTo_of_toIntegralPowerSeries`, converts qExpansion of powers/differences of forms via mathlib's `ModularForm.qExpansion_pow` and `ModularForm.qExpansion_sub` (through the `ModularForm.mul` representation of E₄³ and E₆²).
- **Hypotheses**: none.
- **Uses from project**: [`coeToComplexPowerSeries.ringHom`, `integralE4`, `integralE6`, `coeTo_of_toIntegralPowerSeries`, `E4_isIntegralPowerSeries`, `E6_isIntegralPowerSeries`, `E4`, `E6`]
- **Used by**: `eisenstein_difference_isIntegralPowerSeries_aux`, `toIntegralPowerSeries_eisenstein_difference_aux`
- **Visibility**: public
- **Lines**: 306–334 (26-line proof)
- **Notes**: none

### `lemma eisenstein_difference_isIntegralPowerSeries_aux`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 (E4 ^ 3 - E6 ^ 2))`
- **What**: The q-expansion of E₄³ − E₆² has integer coefficients.
- **How**: The witness is the integral series integralE4³ − integralE6², whose complexification matches by `map_integralE4_pow_three_sub_integralE6_pow_two`.
- **Hypotheses**: none.
- **Uses from project**: [`IsIntegralPowerSeries`, `integralE4`, `integralE6`, `map_integralE4_pow_three_sub_integralE6_pow_two`, `E4`, `E6`]
- **Used by**: `toIntegralPowerSeries_eisenstein_difference_aux`, `Delta_isIntegralPowerSeries`
- **Visibility**: private
- **Lines**: 336–339 (3-line proof)
- **Notes**: none

### `lemma toIntegralPowerSeries_eisenstein_difference_aux`
- **Type**: `toIntegralPowerSeries eisenstein_difference_isIntegralPowerSeries_aux = integralE4 ^ 3 - integralE6 ^ 2`
- **What**: The canonical integral lift of the q-expansion of E₄³ − E₆² is exactly integralE4³ − integralE6² (uniqueness of the lift).
- **How**: Injectivity of the coefficient map ℤ⟦q⟧ → ℂ⟦q⟧ (`PowerSeries.map_injective` with `Int.cast_injective`), comparing both complexifications through `coeTo_of_toIntegralPowerSeries` and `map_integralE4_pow_three_sub_integralE6_pow_two`.
- **Hypotheses**: none.
- **Uses from project**: [`toIntegralPowerSeries`, `eisenstein_difference_isIntegralPowerSeries_aux`, `coeToComplexPowerSeries.ringHom`, `coeTo_of_toIntegralPowerSeries`, `map_integralE4_pow_three_sub_integralE6_pow_two`, `integralE4`, `integralE6`]
- **Used by**: `Delta_isIntegralPowerSeries`
- **Visibility**: private
- **Lines**: 341–350 (9-line proof)
- **Notes**: none

### `lemma eisenstein_difference_coeff_modEq_zero`
- **Type**: `(n : ℕ) : Int.ModEq 1728 ((integralE4 ^ 3 - integralE6 ^ 2).coeff n) 0`
- **What**: Restates the 1728-divisibility of the coefficients of E₄³ − E₆² as a congruence to zero mod 1728.
- **How**: `Int.modEq_zero_iff_dvd` applied to `eisenstein_difference_coeff_dvd_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`eisenstein_difference_coeff_dvd_aux`, `integralE4`, `integralE6`]
- **Used by**: `Delta_isIntegralPowerSeries`
- **Visibility**: public
- **Lines**: 352–354 (term-mode, 2 lines)
- **Notes**: none

### `lemma Delta_qExpansion_eq_smul_eisenstein_difference`
- **Type**: `qExpansion 1 Delta = (1 / 1728 : ℂ) • qExpansion 1 (E4 ^ 3 - E6 ^ 2)`
- **What**: The q-expansion identity Δ = (E₄³ − E₆²)/1728 at the level of power series.
- **How**: Builds E₄³ − E₆² as a weight-12 modular form H via `ModularForm.mcast`, derives the pointwise identity from mathlib's `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq` together with the project's `Delta_eq_eta_pow`, then scales the q-expansion via `UpperHalfPlane.qExpansion_smul` (analyticity at the cusp from `ModularFormClass.analyticAt_cuspFunction_zero`).
- **Hypotheses**: none.
- **Uses from project**: [`Delta`, `Delta_apply`, `Delta_eq_eta_pow`, `E4`, `E6`]
- **Used by**: `Delta_isIntegralPowerSeries`
- **Visibility**: public
- **Lines**: 356–382 (25-line proof)
- **Notes**: none

### `lemma Delta_isIntegralPowerSeries`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 Delta)`
- **What**: The q-expansion of the modular discriminant Δ has integer coefficients (Ramanujan tau integrality at the series level).
- **How**: Writes qExpansion Δ = (1/1728) • qExpansion(E₄³−E₆²) via `Delta_qExpansion_eq_smul_eisenstein_difference` and applies the project's divide-by-a-constant integrality criterion `IsIntegralPowerSeriesmod`, feeding it the mod-1728 vanishing `eisenstein_difference_coeff_modEq_zero` transported along `toIntegralPowerSeries_eisenstein_difference_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`IsIntegralPowerSeries`, `Delta_qExpansion_eq_smul_eisenstein_difference`, `IsIntegralPowerSeriesmod`, `toIntegralPowerSeries_eisenstein_difference_aux`, `eisenstein_difference_coeff_modEq_zero`, `Delta`]
- **Used by**: `integralDelta`
- **Visibility**: public
- **Lines**: 385–391 (6-line proof)
- **Notes**: none

### `def integralDelta`
- **Type**: `integralDelta : PowerSeries ℤ`
- **What**: The integral q-expansion of the modular discriminant Δ, whose coefficients are the Ramanujan tau values.
- **How**: `toIntegralPowerSeries` applied to `Delta_isIntegralPowerSeries`.
- **Hypotheses**: none.
- **Uses from project**: [`toIntegralPowerSeries`, `Delta_isIntegralPowerSeries`]
- **Used by**: `ramanujanTau` (also used in jfunction.lean's `deltaOverQ_isIntegralPowerSeries`)
- **Visibility**: public
- **Lines**: 394 (1 line)
- **Notes**: none

### `def ramanujanTau`
- **Type**: `ramanujanTau : ℕ → ℤ` (`:= fun n ↦ integralDelta.coeff n`)
- **What**: The Ramanujan tau function τ(n), defined as the n-th integer coefficient of the discriminant's q-expansion.
- **How**: Coefficient extraction from `integralDelta`; no proof content.
- **Hypotheses**: none.
- **Uses from project**: [`integralDelta`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 397 (1 line)
- **Notes**: none

### File Summary
- Total declarations: 40 (8 defs [2 abbrevs: E4, E6; 6 defs: integralE4, integralE6, e4Bar, e6Bar, integralDelta, ramanujanTau], 32 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): [`E4`, `E6`, `E4_qExpansion_coeff_aux`, `E6_qExpansion_coeff_aux`, `E4_isIntegralPowerSeries`, `E6_isIntegralPowerSeries`, `integralE4`, `integralE6`, `e4Bar`, `e6Bar`]
- Unused declarations (not used by anything in this file): [`Delta_qExpansion_coeff_zero_aux` (dead code — fact re-proved inline in jfunction.lean), `E4_pow_three_isIntegralPowerSeries` (used downstream in jfunction.lean), `ramanujanTau` (public API endpoint)]
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [`remainder_coeff_dvd_aux` (31 lines)]
