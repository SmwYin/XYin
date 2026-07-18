# XYin/PhD/qExpansion_tactic/link.lean

**Source path**: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/qExpansion_tactic/link.lean
**Project-internal imports**: [`XYin.PhD.jFunction.jfunction`, `XYin.PhD.qExpansion_tactic.Qj`]
**Namespace**: root (opens `XYin.PhD.qExpansion_tactic`, `IntegralPowerSeries`, `UpperHalfPlane`, `PowerSeries`, `ModularForm`, `ModularFormClass`, `ArithmeticFunction`)

This is the soundness file for the q-expansion tactic: it proves that the fast
array-based integer coefficient functions of Qj.lean compute exactly the analytic
q-expansion coefficients of Δ and q·j (as modular objects), culminating in
`Delta_qexpansion_link` / `qj_qexpansion_link` (equality of formal ℤ-series with the
analytic q-expansions after base change ℤ → ℂ) and the coefficientwise corollaries.
File-level `set_option linter.style.header false`.

### `lemma foldl_range_add_eq_sum`
- **Type**: `foldl_range_add_eq_sum (f : Nat → Int) (n : Nat) : List.foldl (fun acc i => acc + f i) 0 (List.range n) = ∑ i ∈ Finset.range n, f i`
- **What**: A left fold accumulating `f` over `range n` equals the finite sum Σ_{i<n} f(i) — the basic bridge from imperative accumulation to `Finset.sum`.
- **How**: Induction on n, peeling the last element with `List.range_succ`/`List.foldl_concat` and matching it with `Finset.sum_range_succ`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `convArrayCoeff_eq_coeff_mul`, `inverseOnePlusCoeffsUpTo_toList`
- **Visibility**: public
- **Lines**: 17–22 (6 lines)
- **Notes**: none

### `lemma foldl_push_toList`
- **Type**: `foldl_push_toList (g : Nat → Int) (m : Nat) : ((List.range m).foldl (fun acc j => acc.push (g j)) #[]).toList = (List.range m).map g`
- **What**: Tabulating g by repeated `Array.push` over `range m` yields the array whose underlying list is `(range m).map g`.
- **How**: Induction on m with `List.range_succ`, `List.foldl_concat`, `Array.toList_push`, `List.map_append`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `foldl_push_getD`
- **Visibility**: public
- **Lines**: 26–33 (8 lines)
- **Notes**: none

### `lemma foldl_push_getD`
- **Type**: `foldl_push_getD (g : Nat → Int) (m i : Nat) (hi : i < m) : ((List.range m).foldl (fun acc j => acc.push (g j)) #[]).getD i 0 = g i`
- **What**: Reading entry i (with default 0) from the tabulated array gives g(i), for in-range i — the fundamental "array lookup = function value" lemma.
- **How**: Rewrites the fold as `((range m).map g).toArray` via `foldl_push_toList`, then evaluates the lookup with `Array.getD_eq_getD_getElem?`, `List.getElem?_map`, `List.getElem?_range`.
- **Hypotheses**: i < m
- **Uses from project**: [`foldl_push_toList`]
- **Used by**: `coeffArray_getD`, `convArrayUpTo_getD`, `deltaCoeffInt_eq`, `delta_array_getD`, `qoverDeltaCoeffInt_eq`, `qjCoeffInt_eq`
- **Visibility**: public
- **Lines**: 36–43 (8 lines)
- **Notes**: none

### `lemma coeffArray_getD`
- **Type**: `coeffArray_getD (f : Nat → Int) (n i : Nat) (hi : i ≤ n) : (coeffArray f n).getD i 0 = f i`
- **What**: An entry of the tabulated coefficient array `coeffArray f n` equals the coefficient function value, for i ≤ n.
- **How**: Unfolds `coeffArray` and applies `foldl_push_getD` (i < n+1 by `omega`).
- **Hypotheses**: i ≤ n
- **Uses from project**: [`coeffArray` (Qj), `foldl_push_getD`]
- **Used by**: `convArrayUpTo_self_coeff`, `convArrayUpTo_cube_coeff`
- **Visibility**: public
- **Lines**: 45–48 (4 lines)
- **Notes**: none

### `lemma convArrayUpTo_getD`
- **Type**: `convArrayUpTo_getD (A B : Array Int) (n i : Nat) (hi : i ≤ n) : (convArrayUpTo A B n).getD i 0 = convArrayCoeff A B i`
- **What**: An entry of the convolution table equals the single-index convolution coefficient, for i ≤ n.
- **How**: Unfolds `convArrayUpTo` and applies `foldl_push_getD`.
- **Hypotheses**: i ≤ n
- **Uses from project**: [`convArrayUpTo` (Qj), `convArrayCoeff` (Qj), `foldl_push_getD`]
- **Used by**: `convArrayUpTo_self_coeff`, `convArrayUpTo_cube_coeff`, `qjCoeffInt_eq`
- **Visibility**: public
- **Lines**: 50–53 (4 lines)
- **Notes**: none

### `lemma convArrayCoeff_eq_coeff_mul`
- **Type**: `convArrayCoeff_eq_coeff_mul (A B : Array Int) (α β : Nat → Int) (m i : Nat) (hA : ∀ j ≤ m, A.getD j 0 = α j) (hB : ∀ j ≤ m, B.getD j 0 = β j) (hi : i ≤ m) : convArrayCoeff A B i = ((PowerSeries.mk α) * (PowerSeries.mk β)).coeff i`
- **What**: The array convolution coefficient computes the Cauchy-product coefficient of the corresponding formal power series, provided the arrays agree with α, β up to index m ≥ i. Core soundness of the multiplication routine.
- **How**: Converts the fold to a sum (`foldl_range_add_eq_sum`), rewrites the power-series side with `PowerSeries.coeff_mul` and `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`, then matches summands termwise using hA, hB and `PowerSeries.coeff_mk`.
- **Hypotheses**: A, B agree with α, β on all indices ≤ m; i ≤ m.
- **Uses from project**: [`convArrayCoeff` (Qj), `foldl_range_add_eq_sum`]
- **Used by**: `convArrayUpTo_self_coeff`, `convArrayUpTo_cube_coeff`, `qjCoeffInt_eq`
- **Visibility**: public
- **Lines**: 57–66 (10 lines)
- **Notes**: none

### `lemma mk_coeff_self`
- **Type**: `mk_coeff_self (F : PowerSeries ℤ) : (PowerSeries.mk fun j => F.coeff j) = F`
- **What**: Rebuilding a power series from its own coefficient function gives back the series (mk/coeff round-trip).
- **How**: Coefficientwise `ext` plus `PowerSeries.coeff_mk`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `convArrayUpTo_cube_coeff`, `qjCoeffInt_eq`
- **Visibility**: public
- **Lines**: 69–72 (4 lines)
- **Notes**: Candidate for replacement by mathlib's `PowerSeries.mk_coeff` / `eta`-style lemma if present.

### `lemma convArrayUpTo_self_coeff`
- **Type**: `convArrayUpTo_self_coeff (f : Nat → Int) (N i : Nat) (hi : i ≤ N) : (convArrayUpTo (coeffArray f N) (coeffArray f N) N).getD i 0 = ((PowerSeries.mk f) ^ 2).coeff i`
- **What**: The "square table" (self-convolution of the tabulation of f) reads off the coefficients of (mk f)², up to index N. Used for the E₆² table.
- **How**: `convArrayUpTo_getD` then `convArrayCoeff_eq_coeff_mul` with α = β = f (agreement via `coeffArray_getD`), finishing with `pow_two`.
- **Hypotheses**: i ≤ N
- **Uses from project**: [`convArrayUpTo` (Qj), `coeffArray` (Qj), `convArrayUpTo_getD`, `convArrayCoeff_eq_coeff_mul`, `coeffArray_getD`]
- **Used by**: `convArrayUpTo_cube_coeff`, `deltaCoeffInt_eq`, `delta_array_getD`
- **Visibility**: public
- **Lines**: 76–82 (7 lines)
- **Notes**: none

### `lemma convArrayUpTo_cube_coeff`
- **Type**: `convArrayUpTo_cube_coeff (f : Nat → Int) (N i : Nat) (hi : i ≤ N) : (convArrayUpTo (convArrayUpTo (coeffArray f N) (coeffArray f N) N) (coeffArray f N) N).getD i 0 = ((PowerSeries.mk f) ^ 3).coeff i`
- **What**: The "cube table" (square table convolved once more with the tabulation of f) reads off the coefficients of (mk f)³. Used for the E₄³ table.
- **How**: `convArrayUpTo_getD` + `convArrayCoeff_eq_coeff_mul` with α = coefficients of (mk f)² (agreement via `convArrayUpTo_self_coeff`) and β = f, then `mk_coeff_self` and `pow_succ` to collapse (mk f)²·(mk f) = (mk f)³.
- **Hypotheses**: i ≤ N
- **Uses from project**: [`convArrayUpTo` (Qj), `coeffArray` (Qj), `convArrayUpTo_getD`, `convArrayCoeff_eq_coeff_mul`, `convArrayUpTo_self_coeff`, `coeffArray_getD`, `mk_coeff_self`]
- **Used by**: `deltaCoeffInt_eq`, `delta_array_getD`, `qjCoeffInt_eq`
- **Visibility**: public
- **Lines**: 85–93 (9 lines)
- **Notes**: none

### `lemma foldl_sigma_search_eq_sum`
- **Type**: `foldl_sigma_search_eq_sum (k m n : Nat) : List.foldl (fun acc i => let d := i + 1; if m % d = 0 then acc + (d : Int) ^ k else acc) 0 (List.range n) = ∑ i ∈ Finset.range n, if m % (i + 1) = 0 then ((i + 1 : Nat) : Int) ^ k else 0`
- **What**: The conditional fold inside `sigmaPow` equals the corresponding conditional finite sum over `range n`.
- **How**: Induction on n peeling the last element (`List.range_succ`, `List.foldl_concat`, `Finset.sum_range_succ`), with a case split on the divisibility test.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `sigmaPow_eq_sigma`
- **Visibility**: public
- **Lines**: 97–108 (12 lines)
- **Notes**: none

### `lemma sigmaPow_eq_sigma`
- **Type**: `sigmaPow_eq_sigma (k n : Nat) : sigmaPow k n = (ArithmeticFunction.sigma k n : Int)`
- **What**: The brute-force divisor search `sigmaPow` computes the arithmetic function σ_k(n) (mathlib's `ArithmeticFunction.sigma`), including the n = 0 convention σ_k(0) = 0.
- **How**: Rewrites the fold as a conditional sum (`foldl_sigma_search_eq_sum`) and `ArithmeticFunction.sigma_apply`; then, for n ≠ 0, converts the conditional sum over `range n` first to a sum over the filtered set (`Finset.sum_filter`) and then to a sum over `n.divisors` via an explicit `Finset.sum_bij` with the bijection i ↦ i+1, whose inverse d ↦ d−1 is justified by `Nat.mem_divisors`, `Nat.pos_of_dvd_of_pos`, `Nat.le_of_dvd`; final cast by `norm_cast`.
- **Hypotheses**: none
- **Uses from project**: [`sigmaPow` (Qj), `foldl_sigma_search_eq_sum`]
- **Used by**: `e4CoeffInt_eq_integralE4_coeff`, `e6CoeffInt_eq_integralE6_coeff`
- **Visibility**: public
- **Lines**: 110–153 (44 lines)
- **Notes**: Proof >30 lines (44); the `sum_bij` block is the bulk and could be golfed via `Nat.sum_divisors_eq_sum_properDivisors...`-style or `Finset.sum_nbij'` helpers.

### `lemma e4CoeffInt_eq_integralE4_coeff`
- **Type**: `e4CoeffInt_eq_integralE4_coeff (n : Nat) : e4CoeffInt n = integralE4.coeff n`
- **What**: The computational E₄-coefficient function agrees with the integral power series `integralE4` (the ℤ-descent of the analytic q-expansion of E₄) at every index.
- **How**: Case split n = 0 vs n ≥ 1, using `integralE4_coeff_zero` and `integralE4_coeff_of_pos` (from Deltaqexpansions) together with `sigmaPow_eq_sigma`.
- **Hypotheses**: none
- **Uses from project**: [`e4CoeffInt` (Qj), `integralE4`, `integralE4_coeff_zero`, `integralE4_coeff_of_pos`, `sigmaPow_eq_sigma`]
- **Used by**: `E4_int_series_eq`
- **Visibility**: public
- **Lines**: 155–161 (7 lines)
- **Notes**: none

### `lemma e6CoeffInt_eq_integralE6_coeff`
- **Type**: `e6CoeffInt_eq_integralE6_coeff (n : Nat) : e6CoeffInt n = integralE6.coeff n`
- **What**: The computational E₆-coefficient function agrees with `integralE6` at every index.
- **How**: Same shape as the E₄ case, via `integralE6_coeff_zero`, `integralE6_coeff_of_pos`, `sigmaPow_eq_sigma`, plus a final `ring` to reconcile the sign/constant arrangement.
- **Hypotheses**: none
- **Uses from project**: [`e6CoeffInt` (Qj), `integralE6`, `integralE6_coeff_zero`, `integralE6_coeff_of_pos`, `sigmaPow_eq_sigma`]
- **Used by**: `E6_int_series_eq`
- **Visibility**: public
- **Lines**: 163–170 (8 lines)
- **Notes**: none

### `lemma E4_int_series_eq`
- **Type**: `E4_int_series_eq : PowerSeries.mk e4CoeffInt = integralE4`
- **What**: The formal ℤ-series built from `e4CoeffInt` is exactly `integralE4`.
- **How**: Coefficientwise `ext` + `PowerSeries.coeff_mk` + `e4CoeffInt_eq_integralE4_coeff`.
- **Hypotheses**: none
- **Uses from project**: [`e4CoeffInt` (Qj), `integralE4`, `e4CoeffInt_eq_integralE4_coeff`]
- **Used by**: `E4_int_link`, `Delta_qexpansion_link`
- **Visibility**: public
- **Lines**: 172–174 (3 lines)
- **Notes**: none

### `lemma E6_int_series_eq`
- **Type**: `E6_int_series_eq : PowerSeries.mk e6CoeffInt = integralE6`
- **What**: The formal ℤ-series built from `e6CoeffInt` is exactly `integralE6`.
- **How**: Coefficientwise `ext` + `PowerSeries.coeff_mk` + `e6CoeffInt_eq_integralE6_coeff`.
- **Hypotheses**: none
- **Uses from project**: [`e6CoeffInt` (Qj), `integralE6`, `e6CoeffInt_eq_integralE6_coeff`]
- **Used by**: `E6_int_link`, `Delta_qexpansion_link`
- **Visibility**: public
- **Lines**: 176–178 (3 lines)
- **Notes**: none

### `lemma E4_int_link`
- **Type**: `E4_int_link : mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk e4CoeffInt) = qExpansion 1 E4`
- **What**: Base-changing the computational E₄-series along ℤ → ℂ recovers the analytic q-expansion of the modular form E₄.
- **How**: Rewrites via `E4_int_series_eq`, then identifies the ℤ→ℂ map with the project's coercion using `coeTo_of_toIntegralPowerSeries E4_isIntegralPowerSeries` (unfolding `integralE4`, `coeToComplexPowerSeries.ringHom`, `powerSeriesMapAlgHom` by `simpa`).
- **Hypotheses**: none
- **Uses from project**: [`e4CoeffInt` (Qj), `E4_int_series_eq`, `integralE4`, `coeToComplexPowerSeries.ringHom`, `powerSeriesMapAlgHom`, `coeTo_of_toIntegralPowerSeries`, `E4_isIntegralPowerSeries`, `E4`]
- **Used by**: `qj_qexpansion_link`
- **Visibility**: public
- **Lines**: 180–184 (5 lines)
- **Notes**: none

### `lemma E6_int_link`
- **Type**: `E6_int_link : mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk e6CoeffInt) = qExpansion 1 E6`
- **What**: Base-changing the computational E₆-series along ℤ → ℂ recovers the analytic q-expansion of E₆.
- **How**: Identical to `E4_int_link` with `E6_int_series_eq` and `coeTo_of_toIntegralPowerSeries E6_isIntegralPowerSeries`.
- **Hypotheses**: none
- **Uses from project**: [`e6CoeffInt` (Qj), `E6_int_series_eq`, `integralE6`, `coeToComplexPowerSeries.ringHom`, `powerSeriesMapAlgHom`, `coeTo_of_toIntegralPowerSeries`, `E6_isIntegralPowerSeries`, `E6`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 186–190 (5 lines)
- **Notes**: Kept for API symmetry with `E4_int_link`; `Delta_qexpansion_link` goes through `E6_int_series_eq` directly instead.

### `lemma int_cast_div_eq_inv_mul_complex`
- **Type**: `int_cast_div_eq_inv_mul_complex {z : Int} (hz : Int.ModEq 1728 z 0) : ((z / 1728 : Int) : ℂ) = (1 / 1728 : ℂ) * (z : ℂ)`
- **What**: For an integer z divisible by 1728, the complex cast of the integer quotient z/1728 equals (1/1728)·z in ℂ — justifying the integer division in the Δ-coefficient routine.
- **How**: Extracts 1728 ∣ z from the congruence (`Int.modEq_zero_iff_dvd`), writes z = 1728·t, evaluates the exact integer division with `Int.ediv_eq_of_eq_mul_right`, and finishes by `norm_num`/`ring` in ℂ.
- **Hypotheses**: z ≡ 0 (mod 1728)
- **Uses from project**: []
- **Used by**: `Delta_qexpansion_link`
- **Visibility**: public
- **Lines**: 192–201 (10 lines)
- **Notes**: none

### `lemma deltaCoeffInt_eq`
- **Type**: `deltaCoeffInt_eq (n : Nat) : deltaCoeffInt n = (((PowerSeries.mk e4CoeffInt) ^ 3 - (PowerSeries.mk e6CoeffInt) ^ 2).coeff n) / 1728`
- **What**: The array-based Δ-coefficient equals the n-th coefficient of the formal series E₄³ − E₆² divided (as integers) by 1728 — soundness of `deltaCoeffsArrayUpTo` against the abstract convolution definition.
- **How**: Unfolds the array construction and applies `foldl_push_getD`, `convArrayUpTo_cube_coeff` (for E₄³), `convArrayUpTo_self_coeff` (for E₆²), and `map_sub` for the coefficient of the difference.
- **Hypotheses**: none
- **Uses from project**: [`deltaCoeffInt` (Qj), `deltaCoeffsArrayUpTo` (Qj), `e4CoeffInt` (Qj), `e6CoeffInt` (Qj), `foldl_push_getD`, `convArrayUpTo_cube_coeff`, `convArrayUpTo_self_coeff`]
- **Used by**: `Delta_qexpansion_link`, `delta_array_getD`
- **Visibility**: public
- **Lines**: 205–211 (7 lines)
- **Notes**: none

### `theorem Delta_qexpansion_link`
- **Type**: `Delta_qexpansion_link : mapAlgHom (Algebra.ofId ℤ ℂ) Delta_qexpansion = qExpansion 1 Delta`
- **What**: Main Δ-soundness theorem: the computational integer q-expansion `Delta_qexpansion` (array-computed Ramanujan τ) maps under ℤ → ℂ to the analytic q-expansion of the cusp form Δ.
- **How**: Coefficientwise. Reduces the left side to (E₄³ − E₆²)ₙ/1728 via `Delta_qexpansion_coeff_eq` and `deltaCoeffInt_eq`, identifies the series with `integralE4³ − integralE6²` (`E4_int_series_eq`, `E6_int_series_eq`), rewrites the right side with `Delta_qExpansion_eq_smul_eisenstein_difference`, gets exactness of the /1728 from `eisenstein_difference_coeff_modEq_zero` fed into `int_cast_div_eq_inv_mul_complex`, and matches the complex coefficient via `map_integralE4_pow_three_sub_integralE6_pow_two` and `PowerSeries.coeff_map`.
- **Hypotheses**: none
- **Uses from project**: [`Delta_qexpansion` (Qj), `Delta_qexpansion_coeff_eq` (Qj), `deltaCoeffInt_eq`, `Delta_qExpansion_eq_smul_eisenstein_difference`, `e4CoeffInt` (Qj), `e6CoeffInt` (Qj), `E4_int_series_eq`, `E6_int_series_eq`, `integralE4`, `integralE6`, `eisenstein_difference_coeff_modEq_zero`, `map_integralE4_pow_three_sub_integralE6_pow_two`, `coeToComplexPowerSeries.ringHom`, `int_cast_div_eq_inv_mul_complex`, `Delta`, `E4`, `E6`]
- **Used by**: `Delta_qxp_coeff_link`, `ramanujanTau_link`, `deltaOverQ_qexpansion_link`, `deltaOverQCoeffInt_zero`
- **Visibility**: public
- **Lines**: 213–242 (30 lines)
- **Notes**: Proof at the 30-line boundary; central theorem of the Δ side.

### `theorem Delta_qxp_coeff_link`
- **Type**: `Delta_qxp_coeff_link (n : ℕ) : (qExpansion 1 Delta).coeff n = Delta_qexpansion.coeff n`
- **What**: Coefficientwise corollary: the n-th analytic q-expansion coefficient of Δ is (the complex cast of) the array-computed integer coefficient. This is the statement that lets `qexp_coeff Delta` facts transfer to the analytic Δ.
- **How**: `congrArg (PowerSeries.coeff n)` applied to `Delta_qexpansion_link`, symmetrized. (Both sides live in ℂ via the coefficient of the mapped series.)
- **Hypotheses**: none
- **Uses from project**: [`Delta_qexpansion` (Qj), `Delta_qexpansion_link`, `Delta`]
- **Used by**: unused in file (user-facing API)
- **Visibility**: public
- **Lines**: 244–246 (3 lines)
- **Notes**: none

### `theorem ramanujanTau_link`
- **Type**: `ramanujanTau_link (n : ℕ) : ramanujanTau n = Delta_qexpansion.coeff n`
- **What**: The project's Ramanujan tau function (defined abstractly as coefficients of `integralDelta`, the ℤ-descent of the analytic Δ-expansion) coincides with the fast array-computed coefficients — so `qexp_coeff Delta` proves τ-values.
- **How**: Both sides cast to ℂ equal the analytic coefficient: the left via `coeTo_of_toIntegralPowerSeries Delta_isIntegralPowerSeries` and `PowerSeries.coeff_map`, the right via `Delta_qexpansion_link`; conclude by injectivity of ℤ → ℂ (`exact_mod_cast`).
- **Hypotheses**: none
- **Uses from project**: [`ramanujanTau`, `integralDelta`, `coeTo_of_toIntegralPowerSeries`, `Delta_isIntegralPowerSeries`, `Delta_qexpansion` (Qj), `Delta_qexpansion_link`, `Delta`]
- **Used by**: unused in file (user-facing API)
- **Visibility**: public
- **Lines**: 248–260 (13 lines)
- **Notes**: none

### `lemma deltaOverQ_qexpansion_link`
- **Type**: `deltaOverQ_qexpansion_link : mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk deltaOverQCoeffInt) = qExpansion 1 deltaOverQ`
- **What**: The shifted computational series (Δ/q with coefficients τ(n+1)) maps under ℤ → ℂ to the analytic q-expansion of the function Δ/q on the upper half-plane.
- **How**: Coefficientwise: the n-th coefficient is τ(n+1) cast to ℂ, which equals the (n+1)-st analytic Δ-coefficient by `Delta_qexpansion_link`; the analytic side is rewritten from `deltaOverQ` to the shifted series `deltaShiftedQSeries` using `qExpansion_ext` with `deltaShiftedQSeries_eq_deltaOverQ`, whose coefficients are computed by `deltaShiftedQSeries_qExpansion_coeff`.
- **Hypotheses**: none
- **Uses from project**: [`deltaOverQCoeffInt` (Qj), `deltaCoeffInt` (Qj), `Delta_qexpansion_link`, `Delta_qexpansion_coeff_eq` (Qj), `qExpansion_ext`, `deltaOverQ`, `deltaShiftedQSeries`, `deltaShiftedQSeries_eq_deltaOverQ`, `deltaShiftedQSeries_qExpansion_coeff`]
- **Used by**: `qOverDelta_qexpansion_link`
- **Visibility**: public
- **Lines**: 264–285 (22 lines)
- **Notes**: none

### `lemma deltaOverQCoeffInt_zero`
- **Type**: `deltaOverQCoeffInt_zero : deltaOverQCoeffInt 0 = 1`
- **What**: The constant term of Δ/q is 1, i.e. τ(1) = 1 — the unit condition needed to invert the series.
- **How**: Derives ((τ(1) : ℤ) : ℂ) = coefficient 1 of the analytic Δ-expansion from `Delta_qexpansion_link`, evaluates that coefficient with `Delta_q_one_term` ((qExpansion 1 Δ).coeff 1 = 1), and descends to ℤ by cast injectivity.
- **Hypotheses**: none
- **Uses from project**: [`deltaOverQCoeffInt` (Qj), `deltaCoeffInt` (Qj), `Delta_qexpansion_link`, `Delta_qexpansion_coeff_eq` (Qj), `Delta_q_one_term`]
- **Used by**: `qoverDelta_mul_eq_one`, `qOverDelta_qexpansion_link`
- **Visibility**: public
- **Lines**: 287–299 (13 lines)
- **Notes**: Proves τ(1) = 1 analytically rather than by computation (`decide`/`native_decide` on `deltaCoeffInt 1` would also work but would add the `ofReduceBool` axiom).

### `def invFn`
- **Type**: `invFn (α : Nat → Int) : Nat → Int`
- **What**: The abstract inverse-coefficient recursion for a series 1 + Σ_{k≥1} α(k)q^k: invFn(0) = 1 and invFn(m+1) = −Σ_{i=0}^{m} α(i+1)·invFn(m−i). This is the mathematical specification that the array routine `inverseOnePlusCoeffsUpTo` implements.
- **How**: Well-founded recursion on n (`termination_by n`, `decreasing_by omega`), with the recursive calls at strictly smaller indices m−i.
- **Hypotheses**: none (interpretation as inverse requires constant term 1, proved separately in `qoverDelta_mul_eq_one`)
- **Uses from project**: []
- **Used by**: `invFn_succ`, `inverseOnePlusCoeffsUpTo_toList`, `inverseOnePlusCoeffsUpTo_getD`, `qoverDeltaCoeffInt_eq`, `qoverDeltaCoeffInt_zero`, `qoverDelta_coeff_succ`
- **Visibility**: public
- **Lines**: 302–306 (5 lines)
- **Notes**: `termination_by`/`decreasing_by` present.

### `lemma invFn_succ`
- **Type**: `invFn_succ (α : Nat → Int) (m : Nat) : invFn α (m + 1) = -∑ i ∈ Finset.range (m + 1), α (i + 1) * invFn α (m - i)`
- **What**: The unfolding (recurrence) equation for `invFn` at successor indices.
- **How**: Single `rw [invFn]` exposing the equation lemma of the well-founded definition.
- **Hypotheses**: none
- **Uses from project**: [`invFn`]
- **Used by**: `inverseOnePlusCoeffsUpTo_toList`, `qoverDelta_coeff_succ`
- **Visibility**: public
- **Lines**: 308–310 (3 lines)
- **Notes**: none

### `lemma array_getD_eq_toList_getD`
- **Type**: `array_getD_eq_toList_getD (arr : Array Int) (i : Nat) : arr.getD i 0 = arr.toList.getD i 0`
- **What**: Array lookup-with-default agrees with list lookup-with-default on the underlying list.
- **How**: `Array.getD_eq_getD_getElem?`, `List.getD_eq_getElem?_getD`, `List.getElem?_toArray`, `Array.toArray_toList`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `inverseOnePlusCoeffsUpTo_toList`, `inverseOnePlusCoeffsUpTo_getD`
- **Visibility**: public
- **Lines**: 312–315 (4 lines)
- **Notes**: Pure Array/List glue; candidate for mathlib or for replacement by an existing mathlib lemma.

### `lemma getD_map_range`
- **Type**: `getD_map_range (g : Nat → Int) (L j : Nat) (hj : j < L) : ((List.range L).map g).getD j 0 = g j`
- **What**: Looking up index j in the list `(range L).map g` returns g(j), for j < L.
- **How**: `List.getD_eq_getElem?_getD`, `List.getElem?_map`, `List.getElem?_range`.
- **Hypotheses**: j < L
- **Uses from project**: []
- **Used by**: `inverseOnePlusCoeffsUpTo_toList`, `inverseOnePlusCoeffsUpTo_getD`
- **Visibility**: public
- **Lines**: 317–320 (4 lines)
- **Notes**: none

### `lemma inverseOnePlusCoeffsUpTo_toList`
- **Type**: `inverseOnePlusCoeffsUpTo_toList (a : Array Int) (α : Nat → Int) (N : Nat) (hα : ∀ j ≤ N, a.getD j 0 = α j) : ∀ K, K ≤ N + 1 → ((List.range K).foldl … #[]).toList = (List.range K).map (invFn α)` (fold body is the literal inversion step of `inverseOnePlusCoeffsUpTo`)
- **What**: Strong invariant for the inversion loop: after K steps, the accumulator array is exactly the tabulation of the abstract inverse coefficients invFn α on 0..K−1. This is the loop-invariant heart of the inversion soundness proof.
- **How**: Induction on K. The successor step peels the last push (`List.range_succ`, `List.foldl_concat`, `Array.toList_push`), invokes the induction hypothesis for the accumulator, converts the inner fold to a sum via `foldl_range_add_eq_sum`, and matches it against `invFn_succ`, using hα and the IH (through `array_getD_eq_toList_getD` and `getD_map_range`) to identify each accessed entry.
- **Hypotheses**: The input array agrees with α up to index N; K ≤ N + 1.
- **Uses from project**: [`invFn`, `invFn_succ`, `foldl_range_add_eq_sum`, `array_getD_eq_toList_getD`, `getD_map_range`]
- **Used by**: `inverseOnePlusCoeffsUpTo_getD`
- **Visibility**: public
- **Lines**: 324–354 (31 lines)
- **Notes**: Proof >30 lines (31). The statement restates the fold body of `inverseOnePlusCoeffsUpTo` literally rather than naming it — fragile against changes in Qj.lean.

### `lemma inverseOnePlusCoeffsUpTo_getD`
- **Type**: `inverseOnePlusCoeffsUpTo_getD (a : Array Int) (α : Nat → Int) (N : Nat) (hα : ∀ j ≤ N, a.getD j 0 = α j) (i : Nat) (hi : i ≤ N) : (inverseOnePlusCoeffsUpTo a N).getD i 0 = invFn α i`
- **What**: Entrywise soundness of the array inversion routine: entry i of `inverseOnePlusCoeffsUpTo a N` is the abstract inverse coefficient invFn α i.
- **How**: Specializes the loop invariant `inverseOnePlusCoeffsUpTo_toList` at K = N+1 and reads off the entry with `array_getD_eq_toList_getD` and `getD_map_range`.
- **Hypotheses**: a agrees with α up to N; i ≤ N.
- **Uses from project**: [`inverseOnePlusCoeffsUpTo` (Qj), `inverseOnePlusCoeffsUpTo_toList`, `invFn`, `array_getD_eq_toList_getD`, `getD_map_range`]
- **Used by**: `qoverDeltaCoeffInt_eq`, `qjCoeffInt_eq`
- **Visibility**: public
- **Lines**: 356–362 (7 lines)
- **Notes**: none

### `lemma delta_array_getD`
- **Type**: `delta_array_getD (top k : Nat) (hk : k ≤ top) : ((List.range (top + 1)).foldl (fun acc i => acc.push ((E₄³-table i − E₆²-table i)/1728)) #[]).getD k 0 = deltaCoeffInt k` (fold body written out literally)
- **What**: The Δ-coefficient table as built *inline* inside `qoverDeltaCoeffsArrayUpTo` and `qjCoeffsArrayUpTo` (with headroom parameter `top`) agrees entrywise with `deltaCoeffInt` — needed because those routines duplicate the table construction instead of calling `deltaCoeffsArrayUpTo`.
- **How**: `foldl_push_getD` to read the entry, `convArrayUpTo_cube_coeff` and `convArrayUpTo_self_coeff` to identify the E₄³ and E₆² entries, then `deltaCoeffInt_eq` backwards (via `map_sub`).
- **Hypotheses**: k ≤ top
- **Uses from project**: [`coeffArray` (Qj), `convArrayUpTo` (Qj), `e4CoeffInt` (Qj), `e6CoeffInt` (Qj), `deltaCoeffInt` (Qj), `foldl_push_getD`, `convArrayUpTo_cube_coeff`, `convArrayUpTo_self_coeff`, `deltaCoeffInt_eq`]
- **Used by**: `qoverDeltaCoeffInt_eq`, `qjCoeffInt_eq`
- **Visibility**: public
- **Lines**: 366–377 (12 lines)
- **Notes**: The statement duplicates 10 lines of the Qj.lean fold body verbatim; refactoring Qj.lean to reuse `deltaCoeffsArrayUpTo` would remove this lemma.

### `lemma qoverDeltaCoeffInt_eq`
- **Type**: `qoverDeltaCoeffInt_eq (n : Nat) : qoverDeltaCoeffInt n = invFn deltaOverQCoeffInt n`
- **What**: The array-computed q/Δ coefficient equals the abstract inversion recursion applied to the Δ/q coefficients — full soundness of the q/Δ routine.
- **How**: Unfolds `qoverDeltaCoeffsArrayUpTo` and applies `inverseOnePlusCoeffsUpTo_getD` with α = `deltaOverQCoeffInt`; the agreement hypothesis is discharged by `foldl_push_getD` + `delta_array_getD` (identifying the inline shifted Δ-table entries with τ(j+1)).
- **Hypotheses**: none
- **Uses from project**: [`qoverDeltaCoeffInt` (Qj), `qoverDeltaCoeffsArrayUpTo` (Qj), `deltaOverQCoeffInt` (Qj), `invFn`, `inverseOnePlusCoeffsUpTo_getD`, `foldl_push_getD`, `delta_array_getD`]
- **Used by**: `qoverDeltaCoeffInt_zero`, `qoverDelta_coeff_succ`, `qjCoeffInt_eq`
- **Visibility**: public
- **Lines**: 380–387 (8 lines)
- **Notes**: none

### `lemma qoverDeltaCoeffInt_zero`
- **Type**: `qoverDeltaCoeffInt_zero : qoverDeltaCoeffInt 0 = 1`
- **What**: The constant term of q/Δ is 1.
- **How**: `qoverDeltaCoeffInt_eq` then the base case of `invFn`.
- **Hypotheses**: none
- **Uses from project**: [`qoverDeltaCoeffInt` (Qj), `qoverDeltaCoeffInt_eq`, `invFn`]
- **Used by**: `qoverDelta_mul_eq_one`
- **Visibility**: public
- **Lines**: 389–390 (2 lines)
- **Notes**: none

### `lemma qoverDelta_coeff_succ`
- **Type**: `qoverDelta_coeff_succ (n : Nat) : qoverDeltaCoeffInt (n + 1) = -∑ i ∈ Finset.range (n + 1), deltaOverQCoeffInt (i + 1) * qoverDeltaCoeffInt (n - i)`
- **What**: The inversion recurrence stated directly for the array-computed q/Δ coefficients.
- **How**: Transfers `invFn_succ` along `qoverDeltaCoeffInt_eq` (applied on both sides and inside the sum via `Finset.sum_congr`).
- **Hypotheses**: none
- **Uses from project**: [`qoverDeltaCoeffInt` (Qj), `deltaOverQCoeffInt` (Qj), `qoverDeltaCoeffInt_eq`, `invFn_succ`]
- **Used by**: `qoverDelta_mul_eq_one`
- **Visibility**: public
- **Lines**: 392–400 (9 lines)
- **Notes**: none

### `lemma qoverDelta_mul_eq_one`
- **Type**: `qoverDelta_mul_eq_one : (PowerSeries.mk deltaOverQCoeffInt) * (PowerSeries.mk qoverDeltaCoeffInt) = 1`
- **What**: The formal ℤ-series Δ/q and its computed inverse multiply to 1 — the key algebraic identity certifying the inversion over ℤ.
- **How**: Coefficientwise. Constant term: 1·1 = 1 from `deltaOverQCoeffInt_zero`/`qoverDeltaCoeffInt_zero`. Coefficient n+1: `PowerSeries.coeff_mul` + `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` turn the antidiagonal sum into a range sum; splitting off the i = 0 term (`Finset.sum_range_succ'`) and substituting the recurrence `qoverDelta_coeff_succ` makes the sum telescope to 0 by `ring`.
- **Hypotheses**: none
- **Uses from project**: [`deltaOverQCoeffInt` (Qj), `qoverDeltaCoeffInt` (Qj), `deltaOverQCoeffInt_zero`, `qoverDeltaCoeffInt_zero`, `qoverDelta_coeff_succ`]
- **Used by**: `qOverDelta_qexpansion_link`
- **Visibility**: public
- **Lines**: 402–424 (23 lines)
- **Notes**: none

### `lemma qOverDelta_qexpansion_link`
- **Type**: `qOverDelta_qexpansion_link : mapAlgHom (Algebra.ofId ℤ ℂ) (PowerSeries.mk qoverDeltaCoeffInt) = qExpansion 1 qOverDelta`
- **What**: The computed q/Δ series maps under ℤ → ℂ to the analytic q-expansion of the function q/Δ on ℍ.
- **How**: Cancellation against the unit A = image of Δ/q: A is a unit since its constant term is 1 (`PowerSeries.isUnit_iff_constantCoeff`, `deltaOverQCoeffInt_zero`); then A·(computed inverse) = 1 by `qoverDelta_mul_eq_one` + `map_mul`, while A·(analytic expansion) = 1 by `deltaOverQ_qexpansion_link` combined with `coeTo_integralDeltaOverQ` and `integralDeltaOverQ_mul_qExpansion_qOverDelta`; conclude by `IsUnit.mul_left_cancel`.
- **Hypotheses**: none
- **Uses from project**: [`qoverDeltaCoeffInt` (Qj), `deltaOverQCoeffInt` (Qj), `deltaOverQCoeffInt_zero`, `qoverDelta_mul_eq_one`, `deltaOverQ_qexpansion_link`, `deltaOverQ`, `qOverDelta`, `coeTo_integralDeltaOverQ`, `integralDeltaOverQ_mul_qExpansion_qOverDelta`, `coeToComplexPowerSeries.ringHom`, `powerSeriesMapAlgHom`]
- **Used by**: `qj_qexpansion_link`
- **Visibility**: public
- **Lines**: 426–453 (28 lines)
- **Notes**: none

### `lemma qjCoeffInt_eq`
- **Type**: `qjCoeffInt_eq (n : Nat) : qjCoeffInt n = ((PowerSeries.mk e4CoeffInt) ^ 3 * PowerSeries.mk qoverDeltaCoeffInt).coeff n`
- **What**: The array-computed q·j coefficient equals the n-th coefficient of the formal product E₄³·(q/Δ) — soundness of the final convolution in `qjCoeffsArrayUpTo`.
- **How**: `convArrayUpTo_getD` + `convArrayCoeff_eq_coeff_mul` with α = coefficients of (mk e4CoeffInt)³ (via `convArrayUpTo_cube_coeff`) and β = `qoverDeltaCoeffInt` (via `inverseOnePlusCoeffsUpTo_getD`, `qoverDeltaCoeffInt_eq` backwards, and `delta_array_getD` for the inline table); closes with `mk_coeff_self`.
- **Hypotheses**: none
- **Uses from project**: [`qjCoeffInt` (Qj), `qjCoeffsArrayUpTo` (Qj), `e4CoeffInt` (Qj), `qoverDeltaCoeffInt` (Qj), `deltaOverQCoeffInt` (Qj), `convArrayUpTo_getD`, `convArrayCoeff_eq_coeff_mul`, `convArrayUpTo_cube_coeff`, `inverseOnePlusCoeffsUpTo_getD`, `qoverDeltaCoeffInt_eq`, `foldl_push_getD`, `delta_array_getD`, `mk_coeff_self`]
- **Used by**: `qj_series_eq`
- **Visibility**: public
- **Lines**: 455–472 (18 lines)
- **Notes**: none

### `lemma qj_series_eq`
- **Type**: `qj_series_eq : PowerSeries.mk qjCoeffInt = (PowerSeries.mk e4CoeffInt) ^ 3 * PowerSeries.mk qoverDeltaCoeffInt`
- **What**: The formal ℤ-series of q·j factors as E₄³ times the computed q/Δ series.
- **How**: Coefficientwise `ext` + `PowerSeries.coeff_mk` + `qjCoeffInt_eq`.
- **Hypotheses**: none
- **Uses from project**: [`qjCoeffInt` (Qj), `e4CoeffInt` (Qj), `qoverDeltaCoeffInt` (Qj), `qjCoeffInt_eq`]
- **Used by**: `qj_qexpansion_link`
- **Visibility**: public
- **Lines**: 474–478 (5 lines)
- **Notes**: none

### `theorem qj_qexpansion_link`
- **Type**: `qj_qexpansion_link : mapAlgHom (Algebra.ofId ℤ ℂ) qj_qexpansion = qExpansion 1 qj`
- **What**: Main q·j soundness theorem: the computational integer series `qj_qexpansion` maps under ℤ → ℂ to the analytic q-expansion of q·j (equivalently, the tactic's coefficients are the true j-invariant Fourier coefficients shifted by one).
- **How**: Factors through `qj_series_eq`: the image is (image of E₄-series)³ · (image of q/Δ-series) by `map_mul`/`map_pow`, identified with (qExpansion 1 E4)³ · qExpansion 1 qOverDelta by `E4_int_link` and `qOverDelta_qexpansion_link`; then mathlib's `qExpansion_of_pow` gives qExpansion 1 (E4^3) = (qExpansion 1 E4)^3, mathlib's `qExpansion_mul` (with the analyticity inputs `E4_pow_three_cuspFunction_analyticAt`, `qOverDelta_cuspFunction_analyticAt`) multiplies the expansions, and `E4_pow_three_mul_qOverDelta_eq_qj` rewrites E₄³·(q/Δ) = q·j.
- **Hypotheses**: none
- **Uses from project**: [`qj_qexpansion` (Qj), `qj_series_eq`, `E4_int_link`, `qOverDelta_qexpansion_link`, `E4_pow_three_cuspFunction_analyticAt`, `qOverDelta_cuspFunction_analyticAt`, `E4_pow_three_mul_qOverDelta_eq_qj`, `qj`, `qOverDelta`, `E4`]
- **Used by**: `qj_qxp_coeff_link`
- **Visibility**: public
- **Lines**: 480–501 (22 lines)
- **Notes**: Uses mathlib's `qExpansion_of_pow` and `qExpansion_mul` (Mathlib.NumberTheory.ModularForms.QExpansion). Capstone theorem of the file.

### `theorem qj_qxp_coeff_link`
- **Type**: `qj_qxp_coeff_link (n : ℕ) : (qExpansion 1 qj).coeff n = qj_qexpansion.coeff n`
- **What**: Coefficientwise corollary: the analytic q-expansion coefficient of q·j equals (the complex cast of) the tactic's integer coefficient — the transfer statement making `qexp_coeff qj` facts about the analytic j-function.
- **How**: `congrArg (PowerSeries.coeff n)` on `qj_qexpansion_link`, symmetrized.
- **Hypotheses**: none
- **Uses from project**: [`qj_qexpansion` (Qj), `qj_qexpansion_link`, `qj`]
- **Used by**: unused in file (user-facing API)
- **Visibility**: public
- **Lines**: 503–505 (3 lines)
- **Notes**: none

### File Summary
- Total declarations: 34 (1 def, 33 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): [`foldl_push_getD` (6 uses), `Delta_qexpansion_link` (4), `convArrayUpTo_cube_coeff` (3), `convArrayUpTo_self_coeff` (3), `convArrayCoeff_eq_coeff_mul` (3), `convArrayUpTo_getD` (3), `invFn` (6), `qoverDeltaCoeffInt_eq` (3), `deltaCoeffInt_eq` (2 but central)]
- Unused declarations (not used by anything in this file): [`E6_int_link`, `Delta_qxp_coeff_link`, `ramanujanTau_link`, `qj_qxp_coeff_link`] (the latter three are the intended user-facing transfer API; `E6_int_link` is API symmetry only)
- Declarations with sorry: []
- Declarations with set_option: [] (file-level `set_option linter.style.header false` at line 4)
- Proofs >30 lines: [`sigmaPow_eq_sigma` (44 lines, 110–153), `inverseOnePlusCoeffsUpTo_toList` (31 lines, 324–354)]; borderline: `Delta_qexpansion_link` (30 lines, 213–242)
