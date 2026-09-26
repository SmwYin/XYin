# Inventory: XYin/PhD/jFunction/Deltaqexpansions.lean  (300 lines)

Integral q-expansions of E₄, E₆ and Δ. Builds `integralE4`, `integralE6 : PowerSeries ℤ` from mathlib's `EisensteinSeries.E_qExpansion_coeff`, proves the 1728-divisibility of every coefficient of `integralE4³ − integralE6²` via the congruence `5σ₃(n)+7σ₅(n) ≡ 0 (mod 12)`, and deduces `Delta_isIntegralPowerSeries`, defining `integralDelta` and `ramanujanTau`. Imports mathlib `LevelOne.GradedRing`, project `IntegralPowerSeries` and `Modularforms.Eisenstein`.

## Declarations

### `abbrev E4`
- **Type**: `E4 : ModularForm (CongruenceSubgroup.Gamma 1) 4` (:= `_root_.E₄`)
- **What**: Alias for the project's normalized weight-4 Eisenstein series.
- **How**: Abbreviation of project `E₄` (Modularforms/Eisenstein.lean:55, `(1/2) • eisensteinSeriesMF _ standardcongruencecondition`).
- **Hypotheses**: none
- **Uses from project**: [`E₄` (Eisenstein.lean:55)]
- **Used by**: E4_qExpansion_coeff_aux, E4_isIntegralPowerSeries, E4_pow_three_isIntegralPowerSeries, map_integralE4_pow_three_sub_integralE6_pow_two, eisenstein_difference_isIntegralPowerSeries_aux, Delta_qExpansion_eq_smul_eisenstein_difference, Delta_isIntegralPowerSeries
- **Visibility**: public
- **Lines**: 36, body 1 line
- **Notes**: Third name for one object: `E4` = project `E₄` = mathlib `ModularForm.E₄` (EisensteinSeries/Basic.lean:51); the coercions agree by `rfl` (line 43). External uses: 24 (jfunction.lean, link.lean, LatticeJ.lean, tests).

### `abbrev E6`
- **Type**: `E6 : ModularForm (CongruenceSubgroup.Gamma 1) 6`
- **What**: Alias for the project's normalized weight-6 Eisenstein series.
- **How**: Abbreviation of project `E₆` (Eisenstein.lean:59).
- **Hypotheses**: none
- **Uses from project**: [`E₆` (Eisenstein.lean:59)]
- **Used by**: E6_qExpansion_coeff_aux, E6_isIntegralPowerSeries, map_integralE4_pow_three_sub_integralE6_pow_two, eisenstein_difference_isIntegralPowerSeries_aux, Delta_qExpansion_eq_smul_eisenstein_difference, Delta_isIntegralPowerSeries
- **Visibility**: public
- **Lines**: 39
- **Notes**: same triplication as E4 (mathlib `ModularForm.E₆`, EisensteinSeries/Basic.lean:54).

### `private lemma E4_qExpansion_coeff_aux`
- **Type**: `(n : ℕ) : (qExpansion 1 E4).coeff n = if n = 0 then 1 else (240 : ℂ) * sigma 3 n`
- **What**: The classical q-expansion `E₄ = 1 + 240 Σ σ₃(n) qⁿ`.
- **How**: mathlib `EisensteinSeries.E_qExpansion_coeff` (EisensteinSeries/QExpansion.lean:324) with k=4, then `norm_num [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_four]` evaluates `-(2·4/B₄) = 240`.
- **Hypotheses**: none
- **Uses from project**: [E4]
- **Used by**: E4_isIntegralPowerSeries, integralE4_coeff_zero, integralE4_coeff_of_pos
- **Visibility**: private
- **Lines**: 41–45, body 3 lines
- **Notes**: mathlib proves `E₄_qExpansion_coeff_one` (LevelOne/DimensionFormula.lean:203) with `show bernoulli 4 = -1/30 by decide +kernel` instead.

### `private lemma E6_qExpansion_coeff_aux`
- **Type**: `(n : ℕ) : (qExpansion 1 E6).coeff n = if n = 0 then 1 else -(504 : ℂ) * sigma 5 n`
- **What**: `E₆ = 1 − 504 Σ σ₅(n) qⁿ`.
- **How**: `E_qExpansion_coeff` with k=6 and project `bernoulli'_six` (Eisenstein.lean:288; mathlib has no `bernoulli'_six`, only `bernoulli'_four` at NumberTheory/Bernoulli.lean:135).
- **Hypotheses**: none
- **Uses from project**: [E6, `bernoulli'_six` (Eisenstein.lean:288)]
- **Used by**: E6_isIntegralPowerSeries, integralE6_coeff_zero, integralE6_coeff_of_pos
- **Visibility**: private
- **Lines**: 47–51, body 3 lines
- **Notes**: —

### `lemma E4_isIntegralPowerSeries`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 E4)`
- **What**: All q-expansion coefficients of E₄ are integers.
- **How**: `int_iff` reduces to exhibiting an integer per coefficient; witnesses 1 and `240 * σ₃ n` from E4_qExpansion_coeff_aux.
- **Hypotheses**: none
- **Uses from project**: [IsIntegralPowerSeries, int_iff (IntegralPowerSeries.lean:154,158), E4, E4_qExpansion_coeff_aux]
- **Used by**: integralE4, E4_pow_three_isIntegralPowerSeries, integralE4_coeff_zero, integralE4_coeff_of_pos
- **Visibility**: public
- **Lines**: 54–59, body 5 lines
- **Notes**: —

### `lemma E6_isIntegralPowerSeries`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 E6)`
- **What**: All q-expansion coefficients of E₆ are integers.
- **How**: As for E4 with witnesses 1 and `-504 * σ₅ n`.
- **Hypotheses**: none
- **Uses from project**: [IsIntegralPowerSeries, int_iff, E6, E6_qExpansion_coeff_aux]
- **Used by**: integralE6, integralE6_coeff_zero, integralE6_coeff_of_pos
- **Visibility**: public
- **Lines**: 62–67, body 5 lines
- **Notes**: identical skeleton to E4_isIntegralPowerSeries.

### `def integralE4`
- **Type**: `PowerSeries ℤ`
- **What**: The ℤ-lift of the q-expansion of E₄.
- **How**: `toIntegralPowerSeries E4_isIntegralPowerSeries` (Classical.choose of the witness series).
- **Hypotheses**: none
- **Uses from project**: [toIntegralPowerSeries (IntegralPowerSeries.lean:163), E4_isIntegralPowerSeries]
- **Used by**: integralE4_coeff_zero, integralE4_coeff_of_pos, integralE4_constantCoeff_aux, integralE4_coeff_dvd_aux, e4Bar, eisenstein_difference_modEq_linear_aux, eisenstein_difference_modEq_aux, eisenstein_difference_coeff_dvd_aux, map_integralE4_pow_three_sub_integralE6_pow_two, eisenstein_difference_isIntegralPowerSeries_aux, toIntegralPowerSeries_eisenstein_difference_aux, eisenstein_difference_coeff_modEq_zero
- **Visibility**: public
- **Lines**: 70
- **Notes**: noncomputable (choice); the computable twin is `e4CoeffInt` (qExpansion_tactic), linked by `E4_int_series_eq` (link.lean:148). 8 external uses.

### `def integralE6`
- **Type**: `PowerSeries ℤ`
- **What**: The ℤ-lift of the q-expansion of E₆.
- **How**: `toIntegralPowerSeries E6_isIntegralPowerSeries`.
- **Hypotheses**: none
- **Uses from project**: [toIntegralPowerSeries, E6_isIntegralPowerSeries]
- **Used by**: same set as integralE4 (E6 counterparts)
- **Visibility**: public
- **Lines**: 73
- **Notes**: 8 external uses.

### `lemma E4_pow_three_isIntegralPowerSeries`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 (E4 ^ 3))`
- **What**: The q-expansion of E₄³ has integer coefficients.
- **How**: `qExpansion 1 (E4^3) = (qExpansion 1 E4)^3` by mathlib `ModularForm.qExpansion_pow` (QExpansion.lean:603, via `E4.qExpansion_pow`, unfolding `DirectSum.ofPow`), then closure of the subring `IntegralPowerSeriesSubring` under powers (`Subring.pow_mem`).
- **Hypotheses**: none
- **Uses from project**: [IsIntegralPowerSeries, E4, E4_isIntegralPowerSeries, IntegralPowerSeriesSubring (IntegralPowerSeries.lean:150)]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 76–80, body 4 lines
- **Notes**: used only by jfunction.lean:311. The `hq` block (77–78) recurs verbatim at 231–232, jfunction.lean:417–420 and link.lean:399–401.

### `private lemma three_dvd_weighted_powers_aux`
- **Type**: `(d : ℕ) : 3 ∣ (5 * d ^ 3 + 7 * d ^ 5)`
- **What**: `5d³+7d⁵ ≡ 0 (mod 3)` for every natural d.
- **How**: Finite check `∀ x : ZMod 3, … = 0` by `decide`, transported via `ZMod.intCast_zmod_eq_zero_iff_dvd` (Data/ZMod/Basic.lean:511) after `Int.natCast_dvd_natCast`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: twelve_dvd_weighted_powers_aux
- **Visibility**: private
- **Lines**: 82–86, body 4 lines
- **Notes**: —

### `private lemma four_dvd_weighted_powers_aux`
- **Type**: `(d : ℕ) : 4 ∣ (5 * d ^ 3 + 7 * d ^ 5)`
- **What**: Same congruence mod 4.
- **How**: Same `decide` over `ZMod 4` + cast.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: twelve_dvd_weighted_powers_aux
- **Visibility**: private
- **Lines**: 88–92, body 4 lines
- **Notes**: identical skeleton to the mod-3 lemma (moral duplicate).

### `private lemma twelve_dvd_weighted_powers_aux`
- **Type**: `(d : ℕ) : 12 ∣ (5 * d ^ 3 + 7 * d ^ 5)`
- **What**: Combines the mod 3 and mod 4 statements.
- **How**: `Nat.Coprime.mul_dvd_of_dvd_of_dvd` with `Nat.Coprime 3 4`.
- **Hypotheses**: none
- **Uses from project**: [three_dvd_weighted_powers_aux, four_dvd_weighted_powers_aux]
- **Used by**: twelve_dvd_weighted_sigma_aux
- **Visibility**: private
- **Lines**: 94–97, body 3 lines
- **Notes**: a single `decide` over `ZMod 12` would replace all three lemmas.

### `private lemma twelve_dvd_weighted_sigma_aux`
- **Type**: `(n : ℕ) : 12 ∣ 5 * sigma 3 n + 7 * sigma 5 n`
- **What**: The divisor-sum congruence `5σ₃(n)+7σ₅(n) ≡ 0 (mod 12)` behind the integrality of Δ.
- **How**: Expand `ArithmeticFunction.sigma_apply` and use `Finset.dvd_sum` termwise with twelve_dvd_weighted_powers_aux; `simpa` with `Finset.mul_sum`, `sum_add_distrib`.
- **Hypotheses**: none
- **Uses from project**: [twelve_dvd_weighted_powers_aux]
- **Used by**: eisenstein_difference_coeff_dvd_aux
- **Visibility**: private
- **Lines**: 99–105, body 6 lines
- **Notes**: no mathlib analogue found (searched `sigma` congruences, `Ramanujan`).

### `private lemma toIntegralPowerSeries_coeff_eq`
- **Type**: `{S : PowerSeries ℂ} (hS : IsIntegralPowerSeries S) {n : ℕ} {z : ℤ} (hz : S.coeff n = (z : ℂ)) : (toIntegralPowerSeries hS).coeff n = z`
- **What**: A coefficient of the ℤ-lift is determined by its complex value.
- **How**: Apply `PowerSeries.coeff n` to `coeTo_of_toIntegralPowerSeries hS`, then `Int.cast_injective` (via `exact_mod_cast`).
- **Hypotheses**: S has integer coefficients; the n-th coefficient equals the cast of z.
- **Uses from project**: [IsIntegralPowerSeries, toIntegralPowerSeries, coeTo_of_toIntegralPowerSeries (IntegralPowerSeries.lean:167)]
- **Used by**: integralE4_coeff_zero, integralE6_coeff_zero, integralE4_coeff_of_pos, integralE6_coeff_of_pos
- **Visibility**: private
- **Lines**: 107–111, body 3 lines
- **Notes**: This "cast-coefficient" pattern is re-proved at jfunction.lean:208–211, jfunction.lean:321–323, qexp_coeffs.lean:46–51, link.lean:232–240, IntegralPowerSeries.lean:181. Should be one public lemma in IntegralPowerSeries.lean.

### `lemma integralE4_coeff_zero`
- **Type**: `integralE4.coeff 0 = 1`
- **What**: E₄ has constant term 1.
- **How**: toIntegralPowerSeries_coeff_eq + E4_qExpansion_coeff_aux at n=0.
- **Hypotheses**: none
- **Uses from project**: [integralE4, toIntegralPowerSeries_coeff_eq, E4_isIntegralPowerSeries, E4_qExpansion_coeff_aux]
- **Used by**: integralE4_constantCoeff_aux
- **Visibility**: public
- **Lines**: 114–115
- **Notes**: no `@[simp]`; 1 external use (link.lean).

### `lemma integralE6_coeff_zero`
- **Type**: `integralE6.coeff 0 = 1`
- **What**: E₆ has constant term 1.
- **How**: as above.
- **Hypotheses**: none
- **Uses from project**: [integralE6, toIntegralPowerSeries_coeff_eq, E6_isIntegralPowerSeries, E6_qExpansion_coeff_aux]
- **Used by**: integralE6_constantCoeff_aux
- **Visibility**: public
- **Lines**: 118–119
- **Notes**: —

### `private lemma integralE4_constantCoeff_aux`
- **Type**: `PowerSeries.constantCoeff integralE4 = 1`
- **What**: Restates integralE4_coeff_zero in `constantCoeff` form.
- **How**: `PowerSeries.coeff_zero_eq_constantCoeff`.
- **Hypotheses**: none
- **Uses from project**: [integralE4, integralE4_coeff_zero]
- **Used by**: e4Bar_coeff_dvd_aux, eisenstein_difference_modEq_aux
- **Visibility**: private
- **Lines**: 121–122
- **Notes**: one-line wrapper; mergeable into integralE4_coeff_zero as a simp lemma.

### `private lemma integralE6_constantCoeff_aux`
- **Type**: `PowerSeries.constantCoeff integralE6 = 1`
- **What**: As above for E₆.
- **How**: same.
- **Hypotheses**: none
- **Uses from project**: [integralE6, integralE6_coeff_zero]
- **Used by**: e6Bar_coeff_dvd_aux, eisenstein_difference_modEq_aux
- **Visibility**: private
- **Lines**: 124–125
- **Notes**: —

### `lemma integralE4_coeff_of_pos`
- **Type**: `(n : ℕ) (hn : 1 ≤ n) : integralE4.coeff n = (240 : ℤ) * sigma 3 n`
- **What**: Positive coefficients of the integral E₄ are `240 σ₃(n)`.
- **How**: toIntegralPowerSeries_coeff_eq with E4_qExpansion_coeff_aux and `if_neg`; `push_cast; ring`.
- **Hypotheses**: n ≥ 1.
- **Uses from project**: [integralE4, toIntegralPowerSeries_coeff_eq, E4_isIntegralPowerSeries, E4_qExpansion_coeff_aux]
- **Used by**: integralE4_coeff_dvd_aux, linear_coeff_eq_aux
- **Visibility**: public
- **Lines**: 128–131, body 2 lines
- **Notes**: callers convert from `n ≠ 0` (`Nat.one_le_iff_ne_zero`, lines 152, 157, 205); an `n ≠ 0` hypothesis or an `if` formulation would be more convenient. 1 external use (link.lean:131).

### `lemma integralE6_coeff_of_pos`
- **Type**: `(n : ℕ) (hn : 1 ≤ n) : integralE6.coeff n = -((504 : ℤ) * sigma 5 n)`
- **What**: Positive coefficients of the integral E₆ are `−504 σ₅(n)`.
- **How**: as above.
- **Hypotheses**: n ≥ 1.
- **Uses from project**: [integralE6, toIntegralPowerSeries_coeff_eq, E6_isIntegralPowerSeries, E6_qExpansion_coeff_aux]
- **Used by**: integralE6_coeff_dvd_aux, linear_coeff_eq_aux
- **Visibility**: public
- **Lines**: 134–137
- **Notes**: —

### `private lemma integralE4_coeff_dvd_aux`
- **Type**: `(n : ℕ) (hn : 1 ≤ n) : 240 ∣ integralE4.coeff n`
- **What**: 240 divides every positive coefficient of E₄.
- **How**: witness `σ₃ n` from integralE4_coeff_of_pos.
- **Hypotheses**: n ≥ 1.
- **Uses from project**: [integralE4, integralE4_coeff_of_pos]
- **Used by**: e4Bar_coeff_dvd_aux
- **Visibility**: private
- **Lines**: 139–140
- **Notes**: —

### `private lemma integralE6_coeff_dvd_aux`
- **Type**: `(n : ℕ) (hn : 1 ≤ n) : 504 ∣ integralE6.coeff n`
- **What**: 504 divides every positive coefficient of E₆.
- **How**: witness `−σ₅ n`.
- **Hypotheses**: n ≥ 1.
- **Uses from project**: [integralE6, integralE6_coeff_of_pos]
- **Used by**: e6Bar_coeff_dvd_aux
- **Visibility**: private
- **Lines**: 142–143
- **Notes**: —

### `private def e4Bar`
- **Type**: `PowerSeries ℤ` (:= `integralE4 - 1`)
- **What**: E₄ minus its constant term, so all coefficients are divisible by 240.
- **How**: definition.
- **Hypotheses**: none
- **Uses from project**: [integralE4]
- **Used by**: e4Bar_coeff_dvd_aux, remainder_coeff_dvd_aux, eisenstein_difference_modEq_linear_aux, linear_coeff_eq_aux
- **Visibility**: private
- **Lines**: 145
- **Notes**: —

### `private def e6Bar`
- **Type**: `PowerSeries ℤ` (:= `integralE6 - 1`)
- **What**: E₆ minus its constant term (all coefficients divisible by 504).
- **How**: definition.
- **Hypotheses**: none
- **Uses from project**: [integralE6]
- **Used by**: e6Bar_coeff_dvd_aux, remainder_coeff_dvd_aux, eisenstein_difference_modEq_linear_aux, linear_coeff_eq_aux
- **Visibility**: private
- **Lines**: 147
- **Notes**: —

### `private lemma e4Bar_coeff_dvd_aux`
- **Type**: `(m : ℕ) : 240 ∣ e4Bar.coeff m`
- **What**: Every coefficient of `E₄ − 1` is divisible by 240.
- **How**: m = 0 via integralE4_constantCoeff_aux (gives 0), m ≠ 0 via integralE4_coeff_dvd_aux.
- **Hypotheses**: none
- **Uses from project**: [e4Bar, integralE4_constantCoeff_aux, integralE4_coeff_dvd_aux]
- **Used by**: remainder_coeff_dvd_aux
- **Visibility**: private
- **Lines**: 149–152, body 3 lines
- **Notes**: —

### `private lemma e6Bar_coeff_dvd_aux`
- **Type**: `(m : ℕ) : 504 ∣ e6Bar.coeff m`
- **What**: Every coefficient of `E₆ − 1` is divisible by 504.
- **How**: same case split.
- **Hypotheses**: none
- **Uses from project**: [e6Bar, integralE6_constantCoeff_aux, integralE6_coeff_dvd_aux]
- **Used by**: remainder_coeff_dvd_aux
- **Visibility**: private
- **Lines**: 154–157
- **Notes**: —

### `private lemma coeff_mul_dvd_aux`
- **Type**: `(a b : ℤ) (f g : PowerSeries ℤ) (hf : ∀ m, a ∣ f.coeff m) (hg : ∀ m, b ∣ g.coeff m) : ∀ m, a * b ∣ (f * g).coeff m`
- **What**: Coefficientwise divisibility is multiplicative for power-series products.
- **How**: `PowerSeries.coeff_mul` (antidiagonal sum) + `Finset.dvd_sum` + `mul_dvd_mul`.
- **Hypotheses**: all coefficients of f divisible by a, of g by b.
- **Uses from project**: []
- **Used by**: coeff_pow_dvd_aux
- **Visibility**: private
- **Lines**: 159–164, body 3 lines
- **Notes**: holds in any `CommSemiring`; is the power-series analogue of mathlib `Polynomial.C_dvd_iff_dvd_coeff` (Algebra/Polynomial/Coeff.lean:313) — no PowerSeries version found (searched `C_dvd_iff`, `dvd_coeff` in RingTheory/PowerSeries).

### `private lemma coeff_pow_dvd_aux`
- **Type**: `(a : ℤ) (f : PowerSeries ℤ) (hf : ∀ m, a ∣ f.coeff m) (k : ℕ) : ∀ m, a ^ k ∣ (f ^ k).coeff m`
- **What**: Coefficientwise divisibility passes to powers.
- **How**: induction on k with coeff_mul_dvd_aux and `pow_succ`.
- **Hypotheses**: all coefficients of f divisible by a.
- **Uses from project**: [coeff_mul_dvd_aux]
- **Used by**: remainder_coeff_dvd_aux
- **Visibility**: private
- **Lines**: 166–172, body 5 lines
- **Notes**: generalizes to any CommSemiring.

### `private lemma remainder_coeff_dvd_aux`
- **Type**: `(n : ℕ) : (1728 : ℤ) ∣ (e4Bar ^ 3 + 3 * e4Bar ^ 2 - e6Bar ^ 2).coeff n`
- **What**: The non-linear remainder of `(1+ē₄)³ − (1+ē₆)²` is divisible by 1728 = 12³.
- **How**: 240³, 3·240², 504² are all multiples of 1728 (`norm_num`), combined with coeff_pow_dvd_aux and `PowerSeries.coeff_C_mul`.
- **Hypotheses**: none
- **Uses from project**: [e4Bar, e6Bar, coeff_pow_dvd_aux, e4Bar_coeff_dvd_aux, e6Bar_coeff_dvd_aux]
- **Used by**: eisenstein_difference_modEq_linear_aux
- **Visibility**: private
- **Lines**: 174–186, body 12 lines
- **Notes**: —

### `private lemma eisenstein_difference_modEq_linear_aux`
- **Type**: `(n : ℕ) : Int.ModEq 1728 ((integralE4 ^ 3 - integralE6 ^ 2).coeff n) ((3 * e4Bar - 2 * e6Bar).coeff n)`
- **What**: Modulo 1728, `E₄³ − E₆²` agrees with its linearization `3ē₄ − 2ē₆`.
- **How**: Algebraic identity `3ē₄ − 2ē₆ − (E₄³ − E₆²) = −(ē₄³ + 3ē₄² − ē₆²)` by `ring` after substituting `E = ē + 1`, then remainder_coeff_dvd_aux and `Int.modEq_iff_dvd`.
- **Hypotheses**: none
- **Uses from project**: [integralE4, integralE6, e4Bar, e6Bar, remainder_coeff_dvd_aux]
- **Used by**: eisenstein_difference_modEq_aux
- **Visibility**: private
- **Lines**: 188–198, body 10 lines
- **Notes**: —

### `private lemma linear_coeff_eq_aux`
- **Type**: `(n : ℕ) (hn0 : n ≠ 0) : ((3 * e4Bar - 2 * e6Bar).coeff n) = 144 * (5 * sigma 3 n + 7 * sigma 5 n)`
- **What**: The linear part's positive coefficients are `144(5σ₃+7σ₅)` (= 3·240σ₃ + 2·504σ₅).
- **How**: `PowerSeries.coeff_C_mul`, `coeff_one`, then integralE4/E6_coeff_of_pos and `ring`.
- **Hypotheses**: n ≠ 0.
- **Uses from project**: [e4Bar, e6Bar, integralE4_coeff_of_pos, integralE6_coeff_of_pos]
- **Used by**: eisenstein_difference_modEq_aux
- **Visibility**: private
- **Lines**: 200–206, body 5 lines
- **Notes**: `change (PowerSeries.C 3 * e4Bar - …)` is needed because `3 * e4Bar` elaborates with numeral `3 : PowerSeries ℤ`.

### `private lemma eisenstein_difference_modEq_aux`
- **Type**: `(n : ℕ) : Int.ModEq 1728 ((integralE4 ^ 3 - integralE6 ^ 2).coeff n) (144 * (5 * sigma 3 n + 7 * sigma 5 n))`
- **What**: Every coefficient of `E₄³ − E₆²` is `≡ 144(5σ₃(n)+7σ₅(n)) (mod 1728)`; at n=0 both sides are 0.
- **How**: n = 0 by the constant-coefficient lemmas (1−1 = 0, and σ(0)=0); n ≠ 0 by the two previous lemmas.
- **Hypotheses**: none
- **Uses from project**: [integralE4, integralE6, integralE4_constantCoeff_aux, integralE6_constantCoeff_aux, linear_coeff_eq_aux, eisenstein_difference_modEq_linear_aux]
- **Used by**: eisenstein_difference_coeff_dvd_aux
- **Visibility**: private
- **Lines**: 208–215, body 6 lines
- **Notes**: —

### `private lemma eisenstein_difference_coeff_dvd_aux`
- **Type**: `(n : ℕ) : 1728 ∣ (integralE4 ^ 3 - integralE6 ^ 2).coeff n`
- **What**: 1728 divides every coefficient of `E₄³ − E₆²` — the integrality of Δ.
- **How**: 12 ∣ 5σ₃+7σ₅ (twelve_dvd_weighted_sigma_aux) so 1728 = 144·12 ∣ 144(…); chain the ModEq.
- **Hypotheses**: none
- **Uses from project**: [integralE4, integralE6, twelve_dvd_weighted_sigma_aux, eisenstein_difference_modEq_aux]
- **Used by**: eisenstein_difference_coeff_modEq_zero
- **Visibility**: private
- **Lines**: 217–224, body 7 lines
- **Notes**: —

### `lemma map_integralE4_pow_three_sub_integralE6_pow_two`
- **Type**: `(coeToComplexPowerSeries.ringHom ℤ) (integralE4 ^ 3 - integralE6 ^ 2) = qExpansion 1 (E4 ^ 3 - E6 ^ 2)`
- **What**: Complexifying the integral series recovers the q-expansion of the modular form E₄³ − E₆².
- **How**: `map_sub/map_pow` + `coeTo_of_toIntegralPowerSeries`; the modular-form side uses mathlib `ModularForm.qExpansion_sub` (QExpansion.lean:570) and `ModularForm.qExpansion_pow` (QExpansion.lean:603) written out with `E4.mul (E4.mul E4)`.
- **Hypotheses**: none
- **Uses from project**: [coeToComplexPowerSeries.ringHom (IntegralPowerSeries.lean:107), integralE4, integralE6, E4, E6, coeTo_of_toIntegralPowerSeries]
- **Used by**: eisenstein_difference_isIntegralPowerSeries_aux, toIntegralPowerSeries_eisenstein_difference_aux
- **Visibility**: public
- **Lines**: 228–240, body 12 lines
- **Notes**: `hpow4`/`hpow6` re-prove the E4_pow_three block (77–78). 1 external use (link.lean).

### `private lemma eisenstein_difference_isIntegralPowerSeries_aux`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 (E4 ^ 3 - E6 ^ 2))`
- **What**: E₄³ − E₆² has integral q-expansion.
- **How**: witness `integralE4^3 − integralE6^2` via the previous lemma.
- **Hypotheses**: none
- **Uses from project**: [IsIntegralPowerSeries, E4, E6, integralE4, integralE6, map_integralE4_pow_three_sub_integralE6_pow_two]
- **Used by**: toIntegralPowerSeries_eisenstein_difference_aux
- **Visibility**: private
- **Lines**: 242–244
- **Notes**: —

### `private lemma toIntegralPowerSeries_eisenstein_difference_aux`
- **Type**: `toIntegralPowerSeries eisenstein_difference_isIntegralPowerSeries_aux = integralE4 ^ 3 - integralE6 ^ 2`
- **What**: The chosen ℤ-lift of the q-expansion of E₄³ − E₆² is the explicit one.
- **How**: `PowerSeries.map_injective (algebraMap ℤ ℂ) Int.cast_injective` (RingTheory/PowerSeries/Basic.lean:476) and `coeTo_of_toIntegralPowerSeries`.
- **Hypotheses**: none
- **Uses from project**: [toIntegralPowerSeries, eisenstein_difference_isIntegralPowerSeries_aux, coeToComplexPowerSeries.ringHom, coeTo_of_toIntegralPowerSeries, map_integralE4_pow_three_sub_integralE6_pow_two, integralE4, integralE6]
- **Used by**: Delta_isIntegralPowerSeries
- **Visibility**: private
- **Lines**: 246–255, body 7 lines
- **Notes**: uniqueness of the lift (`toIntegralPowerSeries hf = g` whenever `map g = f`) deserves a general lemma in IntegralPowerSeries.lean.

### `lemma eisenstein_difference_coeff_modEq_zero`
- **Type**: `(n : ℕ) : Int.ModEq 1728 ((integralE4 ^ 3 - integralE6 ^ 2).coeff n) 0`
- **What**: Public form of the 1728-divisibility.
- **How**: `Int.modEq_zero_iff_dvd`.
- **Hypotheses**: none
- **Uses from project**: [integralE4, integralE6, eisenstein_difference_coeff_dvd_aux]
- **Used by**: Delta_isIntegralPowerSeries
- **Visibility**: public
- **Lines**: 258–260
- **Notes**: stated as ModEq only to feed `IsIntegralPowerSeriesmod`; 1 external use (link.lean:216).

### `lemma Delta_qExpansion_eq_smul_eisenstein_difference`
- **Type**: `qExpansion 1 Delta = (1 / 1728 : ℂ) • qExpansion 1 (E4 ^ 3 - E6 ^ 2)`
- **What**: `Δ = (E₄³ − E₆²)/1728` at the level of q-expansions.
- **How**: Builds `H := mcast (E4.pow 3) - mcast (E6.pow 2) : ModularForm (Gamma 1) 12`, shows `Delta = (1/1728) • H` pointwise from mathlib `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq` (LevelOne/GradedRing.lean:59) via `Delta_apply`, `Delta_eq_eta_pow`; analyticity of `cuspFunction 1 H` from `ModularFormClass.analyticAt_cuspFunction_zero`, then `UpperHalfPlane.qExpansion_smul` (QExpansion.lean:477).
- **Hypotheses**: none
- **Uses from project**: [Delta (Modularforms/Delta.lean:170), Delta_apply (Delta.lean:191), Delta_eq_eta_pow (Delta.lean:36), E4, E6]
- **Used by**: Delta_isIntegralPowerSeries
- **Visibility**: public
- **Lines**: 263–283, body 20 lines
- **Notes**: Reconstructs mathlib's *private* `E₄CubeSubE₆SqForm` (GradedRing.lean:31–44). Mathlib's public `discriminant_eq_E₄_cube_sub_E₆_sq_graded` (GradedRing.lean:78) + `ModularForm.qExpansionRingHom` (QExpansion.lean:621) yield this identity by `map_smul/map_sub/map_pow`. 1 external use (link.lean:213).

### `lemma Delta_isIntegralPowerSeries`
- **Type**: `IsIntegralPowerSeries (qExpansion 1 Delta)`
- **What**: The discriminant has an integral q-expansion (Ramanujan τ(n) ∈ ℤ).
- **How**: Rewrite with the previous lemma, apply the divisibility-descent lemma `IsIntegralPowerSeriesmod` (IntegralPowerSeries.lean:173) with c = 1728 and the ModEq lemma transported through toIntegralPowerSeries_eisenstein_difference_aux.
- **Hypotheses**: none
- **Uses from project**: [IsIntegralPowerSeries, Delta, Delta_qExpansion_eq_smul_eisenstein_difference, IsIntegralPowerSeriesmod, toIntegralPowerSeries_eisenstein_difference_aux, eisenstein_difference_coeff_modEq_zero, E4, E6]
- **Used by**: integralDelta
- **Visibility**: public
- **Lines**: 286–292, body 6 lines
- **Notes**: `decide` for `(1728 : ℤ) ≠ 0`. External uses: jfunction.lean:211, link.lean.

### `def integralDelta`
- **Type**: `PowerSeries ℤ`
- **What**: The ℤ-lift of the q-expansion of Δ.
- **How**: `toIntegralPowerSeries Delta_isIntegralPowerSeries`.
- **Hypotheses**: none
- **Uses from project**: [toIntegralPowerSeries, Delta_isIntegralPowerSeries]
- **Used by**: ramanujanTau
- **Visibility**: public
- **Lines**: 295
- **Notes**: computable twin `Delta_qexpansion := PowerSeries.mk deltaCoeffInt` (qExpansion_tactic/Qj.lean:158), linked by `Delta_qexpansion_link` (link.lean:208). External: jfunction.lean:208, link.lean.

### `def ramanujanTau`
- **Type**: `ℕ → ℤ` (:= `fun n ↦ integralDelta.coeff n`)
- **What**: Ramanujan's τ function as the coefficients of the integral Δ-expansion.
- **How**: definition.
- **Hypotheses**: none
- **Uses from project**: [integralDelta]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 298
- **Notes**: No mathlib Ramanujan τ (only a TODO comment, NumberTheory/ModularForms/Derivative.lean:18). Companion lemmas live in qexp_coeffs.lean (τ(1..3)) and link.lean:232 (`ramanujanTau_link`); `ramanujanTau 0 = 0` is nowhere stated (jfunction.lean:108 has the ℂ version privately). External: link.lean, qexp_coeffs.lean.

## File Summary
- Total declarations: 41 (7 defs/abbrevs: E4, E6, integralE4, integralE6, e4Bar, e6Bar, integralDelta, ramanujanTau → 8 counting abbrevs as defs; 33 lemmas; 0 instances)
- Key API (used by 3+ others in the file): E4, E6, integralE4, integralE6, E4_isIntegralPowerSeries, E6_isIntegralPowerSeries, E4/E6_qExpansion_coeff_aux, toIntegralPowerSeries_coeff_eq, e4Bar, e6Bar, map_integralE4_pow_three_sub_integralE6_pow_two
- Unused declarations (not used by anything in this file): E4_pow_three_isIntegralPowerSeries (used by jfunction.lean:311), ramanujanTau (used by link.lean:232, qexp_coeffs.lean)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: Delta_qExpansion_eq_smul_eisenstein_difference, 20 lines)

## Observations
### Mathlib API candidates
- `E4`/`E6` (36, 39) and project `E₄`/`E₆` (Eisenstein.lean:55/59) duplicate mathlib `ModularForm.E₄`/`E₆` (`.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean:51,54`, `abbrev E₄ : ModularForm 𝒮ℒ 4 := E _`); line 43/49 show `(E4 : ℍ → ℂ) = ModularForm.E₄` by `rfl`. Unlock: delete the project copies, use mathlib's `E₄_qExpansion_coeff_one`, `E_qExpansion_coeff_zero`, `E_ne_zero`.
- `Delta` (Delta.lean:170) duplicates mathlib `CuspForm.discriminant : CuspForm 𝒮ℒ 12` (`Mathlib/NumberTheory/ModularForms/Discriminant.lean:235`); `Δ` (Delta.lean:26) duplicates `ModularForm.discriminant` (Discriminant.lean:49) — the private `delta_eq_discriminant` (Delta.lean:40) is exactly this. Lines 272–275 convert back and forth.
- `Delta_qExpansion_eq_smul_eisenstein_difference` (263–283): mathlib has `discriminant_eq_E₄_cube_sub_E₆_sq_graded` (`LevelOne/GradedRing.lean:78`) and `qExpansionRingHom` (`QExpansion.lean:621`); applying the ring hom to the graded identity gives the q-expansion identity without rebuilding `H`.
- `E4_qExpansion_coeff_aux`/`E6_…` (41–51): mathlib `EisensteinSeries.E_qExpansion_coeff` (`EisensteinSeries/QExpansion.lean:324`) is used; mathlib's own evaluations use `decide +kernel` on `bernoulli 4/6` (DimensionFormula.lean:203–207) making project `bernoulli'_six` unnecessary.
- `coeff_mul_dvd_aux`/`coeff_pow_dvd_aux` (159–172): hand-rolled coefficientwise divisibility; equivalently membership in `RingHom.ker (PowerSeries.map (Int.castRingHom (ZMod 1728)))`, which is closed under `*`/`^` for free. Polynomial analogue exists: `Polynomial.C_dvd_iff_dvd_coeff` (`Mathlib/Algebra/Polynomial/Coeff.lean:313`); no PowerSeries version found (searched `C_dvd_iff`, `dvd_coeff` in `Mathlib/RingTheory/PowerSeries/`).
- `three/four_dvd_weighted_powers_aux` (82–92): one `decide` over `ZMod 12` suffices.
- No mathlib analogue for: integrality of E₄/E₆/Δ q-expansions, Ramanujan τ (searched `ramanujan`, `tau` in Mathlib/NumberTheory).
### Missing API / repeated patterns
- Cast-coefficient lemma `((toIntegralPowerSeries hf).coeff n : ℂ) = f.coeff n` re-proved at 107–111, jfunction.lean:208–211, 321–323, qexp_coeffs.lean:46–51, link.lean:232–240, IntegralPowerSeries.lean:181. Add `IntegralPowerSeries.coeff_toIntegralPowerSeries_cast` in IntegralPowerSeries.lean.
- Lift-uniqueness `toIntegralPowerSeries hf = g` from `map g = f` (246–255) deserves a general lemma.
- `qExpansion 1 (E4^3) = (qExpansion 1 E4)^3` block: 77–78, 231–232, jfunction.lean:417–420, link.lean:399–401 (4 copies).
- `integralE4_coeff_zero`/`integralE6_coeff_zero` lack `@[simp]`; no `ramanujanTau_zero`; `ramanujanTau` has no `_apply`/`simp` unfolding lemma.
### Junk candidates
- `integralE4_constantCoeff_aux`/`integralE6_constantCoeff_aux` (121–125): one-line restatements.
- `twelve_dvd_weighted_powers_aux` chain (82–97): collapsible to one lemma.
### Moral duplicates within this batch
- E4-vs-E6 pairs with identical proofs: E4/E6_isIntegralPowerSeries, integralE4/E6_coeff_zero, _constantCoeff_aux, _coeff_of_pos, _coeff_dvd_aux, e4Bar/e6Bar(_coeff_dvd_aux). A single `integralE (k) ` for `E hk` would halve the file.
- `Delta_q_one_term` (Eisenstein.lean:374) = mathlib `discriminant_qExpansion_coeff_one` (Discriminant.lean:210) = `ramanujanTau_one` (qexp_coeffs.lean:30) at ℤ level.
### Generalization notes
- `coeff_mul_dvd_aux`, `coeff_pow_dvd_aux`: any `CommSemiring` (only `PowerSeries.coeff_mul`, `Finset.dvd_sum`, `mul_dvd_mul`).
- `toIntegralPowerSeries_coeff_eq`: any `R` with injective `algebraMap R ℂ` (the file's `IsRIntegralCPowerSeries R` layer already exists, IntegralPowerSeries.lean:130).
