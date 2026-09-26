# Inventory: XYin/PhD/LaurentQExpansion/Algebra.lean  (439 lines)

Ring-hom behaviour of the analytic Laurent q-expansion `laurentqExpansion` (defined in `LaurentQExpansion.lean`): additivity, multiplicativity, constants, zero, one, negation, finite sums/products; plus the period-enlargement rule `h ↦ m*h` = substitution `q ↦ q^m` (`to_qExpansion_nat_mul`, `laurentqExpansion_nat_mul_coeff`, `_of_not_dvd`). Consumed by `Cox/DiagonalLaurent.lean`, `Cox/Kronecker.lean`, `Cox/ModularPolynomial/IntegralDescent.lean`. Root namespace (no `namespace` command); 15 of 28 declarations are `private`.

## Declarations

### `private lemma norm_lt_one_mem_nhdsNE_zero`
- **Type**: `{q : ℂ | ‖q‖ < 1} ∈ nhdsWithin (0 : ℂ) ({0}ᶜ)`
- **What**: The open unit disc is a punctured neighbourhood of `0`.
- **How**: `nhdsWithin_le_nhds` of `Metric.ball_mem_nhds 0 zero_lt_one`, unfolding `Metric.ball`/`dist_eq_norm`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: cuspFunction_qpow_mul_eventuallyEq, cuspFunction_poleRemoved_nat_mul_eventuallyEq
- **Visibility**: private
- **Lines**: 34–37, proof ≈ 3 lines
- **Notes**: same fact is re-derived inline in LaurentQExpansion.lean at L363–364, L380–381, L523–524 (`filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds …), self_mem_nhdsWithin]`); should be one shared public lemma.

### `private lemma cuspFunction_const`
- **Type**: `(h : ℝ) (a : ℂ) : cuspFunction h (fun _ : ℍ ↦ a) = fun _ : ℂ ↦ a`
- **What**: The cusp function of a constant is that constant (globally, including the `limUnder` value at `0`).
- **How**: at `q = 0` unfold `Periodic.cuspFunction`/`Function.update` and use `tendsto_const_nhds.limUnder_eq`; else `Periodic.cuspFunction_eq_of_nonzero` (mathlib Analysis/Complex/Periodic.lean:119).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: analyticAt_cuspFunction_const, qExpansion_qParam_pow
- **Visibility**: private
- **Lines**: 40–46, proof ≈ 5 lines
- **Notes**: mathlib proves the identical `cuspFunction h 1 = 1` inline inside `qExpansion_one` (NumberTheory/ModularForms/QExpansion.lean:517–520) without exporting it; upstream candidate `UpperHalfPlane.cuspFunction_const`. Moral duplicate of LaurentQExpansion.lean `cuspFunction_const_eventuallyEq` (L90–96, `𝓝[≠]` version).

### `private lemma analyticAt_cuspFunction_const`
- **Type**: `(h : ℝ) (a : ℂ) : AnalyticAt ℂ (cuspFunction h (fun _ : ℍ ↦ a)) 0`
- **What**: Constants have analytic cusp functions.
- **How**: rewrite with `cuspFunction_const`, `analyticAt_const`.
- **Hypotheses**: none.
- **Uses from project**: cuspFunction_const
- **Used by**: qExpansion_qParam_pow, qExpansion_qpow_mul, laurentqExpansion_const (×2)
- **Visibility**: private
- **Lines**: 48–51, proof ≈ 2 lines
- **Notes**: none.

### `private lemma cuspFunction_qpow_mul_eventuallyEq`
- **Type**: `{h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) : cuspFunction h (fun τ ↦ 𝕢 h τ ^ n * f τ) =ᶠ[nhds 0] fun q ↦ q ^ n * cuspFunction h f q`
- **What**: Near `0` (including at `0`), the cusp function of `q^n · f` is `q^n` times the cusp function of `f`.
- **How**: On `𝓝[≠] 0` use `cuspFunction_qpow_mul_eq` (LaurentQExpansion.lean) on the unit disc (`norm_lt_one_mem_nhdsNE_zero`); extend to `𝓝 0` by `eventuallyEq_nhds_of_eventuallyEq_nhdsNE` (mathlib Topology/NhdsWithin.lean:432) with the value at `0` supplied by `cuspFunction_apply_zero_eq` and continuity of `q^n · cuspFunction h f q` (`analyticAt_id.pow`, `.mul`).
- **Hypotheses**: `0 < h`; `cuspFunction h f` analytic at `0`.
- **Uses from project**: norm_lt_one_mem_nhdsNE_zero, cuspFunction_qpow_mul_eq, cuspFunction_apply_zero_eq
- **Used by**: analyticAt_cuspFunction_qpow_mul, qExpansion_qParam_pow
- **Visibility**: private
- **Lines**: 55–67, proof ≈ 10 lines
- **Notes**: none.

### `private lemma analyticAt_cuspFunction_qpow_mul`
- **Type**: `{h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) : AnalyticAt ℂ (cuspFunction h (fun τ ↦ 𝕢 h τ ^ n * f τ)) 0`
- **What**: Multiplying by `q^n` preserves analyticity of the cusp function.
- **How**: `((analyticAt_id.pow n).mul hf).congr` with `cuspFunction_qpow_mul_eventuallyEq`.
- **Hypotheses**: `0 < h`; `cuspFunction h f` analytic at `0`.
- **Uses from project**: cuspFunction_qpow_mul_eventuallyEq
- **Used by**: qExpansion_qpow_mul, analyticAt_cuspFunction_qpow_of_poleOrder_le
- **Visibility**: private
- **Lines**: 69–74, proof ≈ 2 lines
- **Notes**: none.

### `private lemma qExpansion_qParam_pow`
- **Type**: `(h : ℝ) (hh : 0 < h) (n : ℕ) : qExpansion h (fun τ : ℍ ↦ 𝕢 h τ ^ n) = (PowerSeries.X : PowerSeries ℂ) ^ n`
- **What**: The q-expansion of `q^n` is the monomial `X^n`.
- **How**: `cuspFunction_qpow_mul_eventuallyEq` with `f = 1` (plus `cuspFunction_const`) gives `cuspFunction =ᶠ[𝓝 0] (·^n)`; then `qExpansion_coeff`, `Filter.EventuallyEq.iteratedDeriv_eq`, `iteratedDeriv_fun_pow_zero` (mathlib IteratedDeriv/Lemmas.lean:429), `PowerSeries.coeff_X_pow`, and `inv_mul_cancel₀` on `n!`.
- **Hypotheses**: `0 < h`.
- **Uses from project**: cuspFunction_const, cuspFunction_qpow_mul_eventuallyEq, analyticAt_cuspFunction_const
- **Used by**: qExpansion_qpow_mul
- **Visibility**: private
- **Lines**: 77–91, proof ≈ 12 lines
- **Notes**: public-worthy (`qExpansion h (𝕢 h ·) = X` is the most basic q-expansion fact) but private; no mathlib analogue (grepped `qExpansion_qParam`, `qExpansion_X` in QExpansion.lean).

### `private lemma qExpansion_qpow_mul`
- **Type**: `{h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) : qExpansion h (fun τ ↦ 𝕢 h τ ^ n * f τ) = PowerSeries.X ^ n * qExpansion h f`
- **What**: Multiplying by `q^n` on functions is multiplying by `X^n` on q-expansions.
- **How**: mathlib `UpperHalfPlane.qExpansion_mul` (QExpansion.lean:466) with `qExpansion_qParam_pow` and `analyticAt_cuspFunction_qpow_mul`.
- **Hypotheses**: `0 < h`; `cuspFunction h f` analytic at `0`.
- **Uses from project**: analyticAt_cuspFunction_qpow_mul, analyticAt_cuspFunction_const, qExpansion_qParam_pow
- **Used by**: laurentqExpansion_eq_shiftedLaurent
- **Visibility**: private
- **Lines**: 94–102, proof ≈ 5 lines
- **Notes**: none.

### `private def shiftedLaurent`
- **Type**: `(h : ℝ) (N : ℕ) (f : ℍ → ℂ) : LaurentSeries ℂ := HahnSeries.single (-(N : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℂ (qExpansion h (fun τ ↦ 𝕢 h τ ^ N * f τ))`
- **What**: The "shift by `N`" presentation of a Laurent expansion: `q^{−N}` times the power series of `q^N · f`. For any `N ≥ poleOrder h f` it equals `laurentqExpansion h f`.
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: laurentqExpansion_eq_shiftedLaurent, shiftedLaurent_add, laurentqExpansion_add, shiftedLaurent_mul, laurentqExpansion_mul
- **Visibility**: private
- **Lines**: 108–111
- **Notes**: this is `UpperHalfPlane.laurentqExpansion` with `poleOrder` replaced by a free `N`; `laurentqExpansion` is the `N := poleOrder h f` instance. Suggests re-architecting: define the `N`-parametrised version publicly, prove independence of `N` once (`laurentqExpansion_eq_shiftedLaurent`), and derive all ring lemmas without the ad-hoc common-shift arithmetic.

### `private lemma qpow_mul_eq_qpow_sub_mul_poleRemoved`
- **Type**: `{h : ℝ} {f : ℍ → ℂ} {N : ℕ} (hN : poleOrder h f ≤ N) : (fun τ ↦ 𝕢 h τ ^ N * f τ) = fun τ ↦ 𝕢 h τ ^ (N - poleOrder h f) * poleRemoved h f τ`
- **What**: For `N ≥ poleOrder`, `q^N · f` factors as `q^{N − poleOrder} · poleRemoved f`.
- **How**: `funext`, unfold `poleRemoved`, `pow_add`, `Nat.sub_add_cancel`.
- **Hypotheses**: `poleOrder h f ≤ N`.
- **Uses from project**: poleOrder, poleRemoved
- **Used by**: laurentqExpansion_eq_shiftedLaurent, analyticAt_cuspFunction_qpow_of_poleOrder_le
- **Visibility**: private
- **Lines**: 115–121, proof ≈ 3 lines
- **Notes**: none.

### `private lemma laurentqExpansion_eq_shiftedLaurent`
- **Type**: `{h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) {N : ℕ} (hN : poleOrder h f ≤ N) : laurentqExpansion h f = shiftedLaurent h N f`
- **What**: Well-definedness of the shifted presentation: any denominator exponent `N ≥ poleOrder` gives the same Laurent series.
- **How**: `qExpansion h (q^N f) = X^{N−poleOrder} · to_qExpansion h f` by `qpow_mul_eq_qpow_sub_mul_poleRemoved` + `qExpansion_qpow_mul` (analyticity from `analyticAt_cuspFunction_poleRemoved`), then `map_mul`, `HahnSeries.ofPowerSeries_X_pow` (mathlib HahnSeries/PowerSeries.lean:140), `HahnSeries.single_mul_single` (HahnSeries/Multiplication.lean:776), and `omega` on the exponents.
- **Hypotheses**: `0 < h`; `f` cusp-meromorphic; `poleOrder h f ≤ N`.
- **Uses from project**: qpow_mul_eq_qpow_sub_mul_poleRemoved, qExpansion_qpow_mul, analyticAt_cuspFunction_poleRemoved, laurentqExpansion, shiftedLaurent, to_qExpansion, poleOrder
- **Used by**: laurentqExpansion_add (×3), laurentqExpansion_mul (×3)
- **Visibility**: private
- **Lines**: 125–138, proof ≈ 9 lines
- **Notes**: `rfl` at L135 closes `qExpansion h (poleRemoved h f) = to_qExpansion h f` by definitional unfolding.

### `private lemma analyticAt_cuspFunction_qpow_of_poleOrder_le`
- **Type**: `{h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) {N : ℕ} (hN : poleOrder h f ≤ N) : AnalyticAt ℂ (cuspFunction h (fun τ ↦ 𝕢 h τ ^ N * f τ)) 0`
- **What**: Any shift `N ≥ poleOrder` clears the pole.
- **How**: `qpow_mul_eq_qpow_sub_mul_poleRemoved`, then `analyticAt_cuspFunction_qpow_mul` on `poleRemoved` (analytic by `analyticAt_cuspFunction_poleRemoved`).
- **Hypotheses**: `0 < h`; cusp-meromorphic; `poleOrder h f ≤ N`.
- **Uses from project**: qpow_mul_eq_qpow_sub_mul_poleRemoved, analyticAt_cuspFunction_qpow_mul, analyticAt_cuspFunction_poleRemoved
- **Used by**: laurentqExpansion_add (×2), laurentqExpansion_mul (×2)
- **Visibility**: private
- **Lines**: 140–147, proof ≈ 3 lines
- **Notes**: none.

### `private lemma shiftedLaurent_add`
- **Type**: `{h : ℝ} {f g : ℍ → ℂ} {N : ℕ} (hfN : AnalyticAt ℂ (cuspFunction h (fun τ ↦ 𝕢 h τ ^ N * f τ)) 0) (hgN : …g…) : shiftedLaurent h N (fun τ ↦ f τ + g τ) = shiftedLaurent h N f + shiftedLaurent h N g`
- **What**: The shifted presentation is additive at a common shift.
- **How**: `mul_add` under the binder, mathlib `qExpansion_add` (QExpansion.lean:487), `map_add`, `mul_add`.
- **Hypotheses**: both shifted cusp functions analytic at `0`.
- **Uses from project**: shiftedLaurent
- **Used by**: laurentqExpansion_add
- **Visibility**: private
- **Lines**: 150–160, proof ≈ 6 lines
- **Notes**: no `0 < h` needed — purely formal.

### `lemma laurentqExpansion_add`
- **Type**: `{h : ℝ} (hh : 0 < h) {f g : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) (hg : MeromorphicAt (cuspFunction h g) 0) : laurentqExpansion h (fun τ ↦ f τ + g τ) = laurentqExpansion h f + laurentqExpansion h g`
- **What**: The Laurent q-expansion is additive on cusp-meromorphic functions.
- **How**: Choose the common shift `N := poleOrder f + poleOrder g + poleOrder (f+g)`; rewrite all three expansions via `laurentqExpansion_eq_shiftedLaurent` (`meromorphicAt_cuspFunction_add` for the sum) and apply `shiftedLaurent_add` with `analyticAt_cuspFunction_qpow_of_poleOrder_le`.
- **Hypotheses**: `0 < h`; `f`, `g` cusp-meromorphic.
- **Uses from project**: poleOrder, meromorphicAt_cuspFunction_add, laurentqExpansion_eq_shiftedLaurent, shiftedLaurent_add, analyticAt_cuspFunction_qpow_of_poleOrder_le
- **Used by**: laurentqExpansion_finset_sum; externally DiagonalLaurent.lean:172, IntegralDescent.lean:42
- **Visibility**: public
- **Lines**: 163–177, proof ≈ 9 lines
- **Notes**: stated with `fun τ ↦ f τ + g τ` rather than `f + g` (mathlib `qExpansion_add` uses `f + g`); the common-shift trick exists because `poleOrder_add_le` is missing from LaurentQExpansion.lean.

### `private lemma shiftedLaurent_mul`
- **Type**: `{h : ℝ} {f g : ℍ → ℂ} {A B : ℕ} (hfA : AnalyticAt ℂ (cuspFunction h (fun τ ↦ 𝕢 h τ ^ A * f τ)) 0) (hgB : …B…g…) : shiftedLaurent h (A + B) (fun τ ↦ f τ * g τ) = shiftedLaurent h A f * shiftedLaurent h B g`
- **What**: The shifted presentation is multiplicative with shifts adding.
- **How**: `pow_add` + `mul_mul_mul_comm` under the binder, mathlib `qExpansion_mul` (QExpansion.lean:466), `map_mul`, `HahnSeries.single_mul_single`, `omega`.
- **Hypotheses**: both shifted cusp functions analytic at `0`.
- **Uses from project**: shiftedLaurent
- **Used by**: laurentqExpansion_mul
- **Visibility**: private
- **Lines**: 180–193, proof ≈ 9 lines
- **Notes**: no `0 < h` needed.

### `lemma laurentqExpansion_mul`
- **Type**: `{h : ℝ} (hh : 0 < h) {f g : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) (hg : MeromorphicAt (cuspFunction h g) 0) : laurentqExpansion h (fun τ ↦ f τ * g τ) = laurentqExpansion h f * laurentqExpansion h g`
- **What**: The Laurent q-expansion is multiplicative on cusp-meromorphic functions.
- **How**: Shifts `A := poleOrder f + poleOrder (f·g)`, `B := poleOrder g` so that `A + B` dominates the product's pole order; `laurentqExpansion_eq_shiftedLaurent` ×3 (`meromorphicAt_cuspFunction_mul`) and `shiftedLaurent_mul`.
- **Hypotheses**: `0 < h`; `f`, `g` cusp-meromorphic.
- **Uses from project**: poleOrder, meromorphicAt_cuspFunction_mul, laurentqExpansion_eq_shiftedLaurent, shiftedLaurent_mul, analyticAt_cuspFunction_qpow_of_poleOrder_le
- **Used by**: laurentqExpansion_neg, laurentqExpansion_finset_prod; externally DiagonalLaurent.lean:184, IntegralDescent.lean:51
- **Visibility**: public
- **Lines**: 196–211, proof ≈ 9 lines
- **Notes**: the ad-hoc `A` is needed because `poleOrder_mul` (from mathlib `meromorphicOrderAt_mul`, Meromorphic/Order.lean:429) is missing.

### `@[simp] lemma laurentqExpansion_const`
- **Type**: `(h : ℝ) (a : ℂ) : laurentqExpansion h (fun _ : ℍ ↦ a) = HahnSeries.C a`
- **What**: The Laurent q-expansion of a constant is the constant series.
- **How**: `meromorphicAt_cuspFunction_const` + `analyticAt_cuspFunction_iff_poleOrder_eq_zero` give `poleOrder = 0`; `qExpansion h (const a) = C a` from mathlib `qExpansion_smul` on `1` (QExpansion.lean:477) + `qExpansion_one` (:515) + `PowerSeries.smul_eq_C_mul`; finish with `laurentqExpansion.eq_qExpansion_iff` and `HahnSeries.ofPowerSeries_C` (HahnSeries/PowerSeries.lean:114).
- **Hypotheses**: none (no `0 < h`).
- **Uses from project**: meromorphicAt_cuspFunction_const, poleOrder, analyticAt_cuspFunction_iff_poleOrder_eq_zero, analyticAt_cuspFunction_const, laurentqExpansion.eq_qExpansion_iff
- **Used by**: laurentqExpansion_zero, laurentqExpansion_one, laurentqExpansion_neg; externally DiagonalLaurent.lean:183, IntegralDescent.lean:50
- **Visibility**: public
- **Lines**: 214–224, proof ≈ 9 lines
- **Notes**: `@[simp]`; the intermediate `qExpansion h (fun _ ↦ a) = C a` (L219–223) is a missing mathlib `qExpansion_const`.

### `@[simp] lemma laurentqExpansion_zero`
- **Type**: `(h : ℝ) : laurentqExpansion h (0 : ℍ → ℂ) = 0`
- **What**: Expansion of the zero function is zero.
- **How**: `Pi.zero_def`, `laurentqExpansion_const`, `map_zero`.
- **Hypotheses**: none.
- **Uses from project**: laurentqExpansion_const
- **Used by**: unused in file; externally IntegralDescent.lean:230
- **Visibility**: public
- **Lines**: 227–229, proof ≈ 1 line
- **Notes**: `@[simp]`.

### `@[simp] lemma laurentqExpansion_one`
- **Type**: `(h : ℝ) : laurentqExpansion h (1 : ℍ → ℂ) = 1`
- **What**: Expansion of the constant-one function is one.
- **How**: `Pi.one_def`, `laurentqExpansion_const`, `map_one`.
- **Hypotheses**: none.
- **Uses from project**: laurentqExpansion_const
- **Used by**: unused in file; 0 external references
- **Visibility**: public
- **Lines**: 232–234, proof ≈ 1 line
- **Notes**: `@[simp]`; unused but legitimate API.

### `lemma laurentqExpansion_neg`
- **Type**: `{h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) : laurentqExpansion h (fun τ ↦ -f τ) = -laurentqExpansion h f`
- **What**: Expansion commutes with negation.
- **How**: `-f = (−1)·f`; `laurentqExpansion_mul` with `meromorphicAt_cuspFunction_const h (-1)` and `laurentqExpansion_const`; `HahnSeries.C (-1) = -1` by `simp`; `ring`.
- **Hypotheses**: `0 < h`; cusp-meromorphic.
- **Uses from project**: laurentqExpansion_mul, meromorphicAt_cuspFunction_const, laurentqExpansion_const
- **Used by**: unused in file; externally IntegralDescent.lean:190
- **Visibility**: public
- **Lines**: 237–247, proof ≈ 8 lines
- **Notes**: the `hh`/`hf` hypotheses are artefacts of routing through `mul`; a direct proof via mathlib `qExpansion_neg` (QExpansion.lean:483) on `poleRemoved` would need `poleOrder h (-f) = poleOrder h f` (missing, follows from `meromorphicOrderAt_neg`, Order.lean:388) and `meromorphicAt_cuspFunction_neg` (missing).

### `lemma laurentqExpansion_finset_sum`
- **Type**: `{h : ℝ} (hh : 0 < h) {I : Type*} (s : Finset I) {f : I → ℍ → ℂ} (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) : laurentqExpansion h (∑ i ∈ s, f i) = ∑ i ∈ s, laurentqExpansion h (f i)`
- **What**: Expansion commutes with finite pointwise sums.
- **How**: `Finset.induction_on`; `Finset.sum_insert`; `laurentqExpansion_add` with `meromorphicAt_cuspFunction_finset_sum` for the tail.
- **Hypotheses**: `0 < h`; each summand cusp-meromorphic.
- **Uses from project**: laurentqExpansion_add, meromorphicAt_cuspFunction_finset_sum
- **Used by**: unused in file; externally IntegralDescent.lean:215
- **Visibility**: public
- **Lines**: 250–264, proof ≈ 11 lines
- **Notes**: identical skeleton to `laurentqExpansion_finset_prod` (L267–281) and to `meromorphicAt_cuspFunction_finset_sum/prod` (LaurentQExpansion.lean L118–143) — four copies of one induction; all four are `map_sum`/`map_prod` of an unbundled ring hom.

### `lemma laurentqExpansion_finset_prod`
- **Type**: `{h : ℝ} (hh : 0 < h) {I : Type*} (s : Finset I) {f : I → ℍ → ℂ} (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) : laurentqExpansion h (∏ i ∈ s, f i) = ∏ i ∈ s, laurentqExpansion h (f i)`
- **What**: Expansion commutes with finite pointwise products.
- **How**: as for sums, with `laurentqExpansion_mul` and `meromorphicAt_cuspFunction_finset_prod`.
- **Hypotheses**: `0 < h`; each factor cusp-meromorphic.
- **Uses from project**: laurentqExpansion_mul, meromorphicAt_cuspFunction_finset_prod
- **Used by**: unused in file; externally DiagonalLaurent.lean:155, IntegralDescent.lean:27, 218
- **Visibility**: public
- **Lines**: 267–281, proof ≈ 11 lines
- **Notes**: see `laurentqExpansion_finset_sum`.

### `private def analyticTaylor`
- **Type**: `(F : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk fun n ↦ (n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0`
- **What**: The formal Taylor series of `F` at `0`.
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: hasFPowerSeriesAt_expand_analyticTaylor, analyticTaylor_comp_pow, to_qExpansion_nat_mul
- **Visibility**: private
- **Lines**: 285–286
- **Notes**: literally the body of mathlib `UpperHalfPlane.qExpansion` (QExpansion.lean:166–167) with `cuspFunction h f` replaced by an arbitrary `F`; `qExpansion h f = analyticTaylor (cuspFunction h f)` definitionally (exploited by `simpa [analyticTaylor, UpperHalfPlane.to_qExpansion, UpperHalfPlane.qExpansion]` at L380). Mathlib has the `FormalMultilinearSeries` form (`FormalMultilinearSeries.ofScalars`, Analytic/OfScalars.lean:38; `AnalyticAt.hasFPowerSeriesAt`, IteratedDeriv/Defs.lean:339) but no `PowerSeries`-valued Taylor series def.

### `private lemma hasFPowerSeriesAt_expand_analyticTaylor`
- **Type**: `{G : ℂ → ℂ} {m : ℕ} (hm : m ≠ 0) (hG : AnalyticAt ℂ G 0) {F : ℂ → ℂ} (hEq : F =ᶠ[nhds 0] G ∘ fun q ↦ q ^ m) : HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ fun n ↦ ((analyticTaylor G).expand m hm).coeff n) 0`
- **What**: If `F = G ∘ (·^m)` near `0`, then `F` is represented at `0` by the `m`-fold expansion (`X ↦ X^m`) of the Taylor series of `G`.
- **How**: `AnalyticAt.exists_ball_analyticOnNhd` (Analytic/ChangeOrigin.lean:386) for `G`; `Complex.hasSum_taylorSeries_on_ball` (Analysis/Complex/TaylorSeries.lean:45) gives `HasSum (coeff n G • (q^m)^n) (G (q^m))`; reindex along the injection `n ↦ m n` with `Function.Injective.hasSum_iff` (to_additive of `Function.Injective.hasProd_iff`, Topology/Algebra/InfiniteSum/Defs.lean:231), using `PowerSeries.coeff_expand_mul` (RingTheory/PowerSeries/Expand.lean:87) for the multiples and `PowerSeries.coeff_expand` (:110) / non-divisibility for the vanishing of the rest; conclude via `hasFPowerSeriesAt_iff` and `FormalMultilinearSeries.coeff_ofScalars`.
- **Hypotheses**: `m ≠ 0`; `G` analytic at `0`; `F =ᶠ[𝓝 0] G ∘ (·^m)`.
- **Uses from project**: analyticTaylor
- **Used by**: analyticTaylor_comp_pow
- **Visibility**: private
- **Lines**: 290–326, proof ≈ 36 lines (>30)
- **Notes**: nothing cusp-specific; a general analytic-composition-with-monomial fact. No file in `Mathlib/Analysis` references `PowerSeries.expand` (grep) — mathlib gap: "Taylor series of `G ∘ (·^m)` is `expand m` of the Taylor series of `G`" (`HasFPowerSeriesAt.comp_pow` / `FormalMultilinearSeries.expand`).

### `private lemma analyticTaylor_comp_pow`
- **Type**: `{F G : ℂ → ℂ} {m : ℕ} (hm : m ≠ 0) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) (hEq : F =ᶠ[nhds 0] G ∘ fun q ↦ q ^ m) : analyticTaylor F = (analyticTaylor G).expand m hm`
- **What**: Taylor-series version of the previous lemma.
- **How**: `HasFPowerSeriesAt.eq_formalMultilinearSeries` (Analytic/Uniqueness.lean:88) between `hasFPowerSeriesAt_expand_analyticTaylor` and `hF.hasFPowerSeriesAt`; compare coefficients (`FormalMultilinearSeries.coeff_ofScalars`).
- **Hypotheses**: as above plus `F` analytic at `0` (redundant: it follows from `hEq` and `hG`).
- **Uses from project**: hasFPowerSeriesAt_expand_analyticTaylor, analyticTaylor
- **Used by**: to_qExpansion_nat_mul
- **Visibility**: private
- **Lines**: 330–339, proof ≈ 6 lines
- **Notes**: `hF` is derivable (`hG.comp (analyticAt_id.pow m)` + `congr`), so the hypothesis is redundant.

### `private lemma cuspFunction_poleRemoved_nat_mul_eventuallyEq`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (hfper : Periodic (f ∘ ofComplex) h) : cuspFunction (m * h) (poleRemoved (m * h) f) =ᶠ[𝓝[≠] 0] cuspFunction h (poleRemoved h f) ∘ fun q ↦ q ^ m`
- **What**: On a punctured neighbourhood of `0`, the pole-removed cusp function for period `m h` is the one for period `h` composed with `q ↦ q^m`.
- **How**: On the punctured unit disc, `cuspFunction_poleRemoved_eq` for both periods (meromorphy at `m h` via `meromorphicAt_cuspFunction_nat_mul`), `poleOrder_nat_mul`, `cuspFunction_nat_mul_eq_cuspFunction_pow`, `pow_mul`.
- **Hypotheses**: `m ≠ 0`; cusp-meromorphic; `h`-periodic.
- **Uses from project**: meromorphicAt_cuspFunction_nat_mul, norm_lt_one_mem_nhdsNE_zero, cuspFunction_poleRemoved_eq, poleOrder_nat_mul, cuspFunction_nat_mul_eq_cuspFunction_pow, poleOrder, poleRemoved
- **Used by**: to_qExpansion_nat_mul
- **Visibility**: private
- **Lines**: 343–362, proof ≈ 16 lines
- **Notes**: none.

### `lemma to_qExpansion_nat_mul`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (hfper : Periodic (f ∘ ofComplex) h) : to_qExpansion (m * h) f = (to_qExpansion h f).expand m hm`
- **What**: Enlarging the period by `m` expands the pole-removed q-expansion by `X ↦ X^m`.
- **How**: Upgrade `cuspFunction_poleRemoved_nat_mul_eventuallyEq` from `𝓝[≠]` to `𝓝` using `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE` (Topology/Separation/Hausdorff.lean:654) with both sides analytic (`analyticAt_cuspFunction_poleRemoved`, `AnalyticAt.comp`), then `analyticTaylor_comp_pow` and unfold `to_qExpansion`/`qExpansion`/`analyticTaylor`.
- **Hypotheses**: `m ≠ 0`; cusp-meromorphic; `h`-periodic.
- **Uses from project**: analyticAt_cuspFunction_poleRemoved, meromorphicAt_cuspFunction_nat_mul, cuspFunction_poleRemoved_nat_mul_eventuallyEq, analyticTaylor_comp_pow, analyticTaylor, to_qExpansion, poleRemoved
- **Used by**: laurentqExpansion_nat_mul_coeff, laurentqExpansion_nat_mul_coeff_of_not_dvd
- **Visibility**: public
- **Lines**: 365–381, proof ≈ 14 lines
- **Notes**: 0 external references (consumers use the coefficient forms below).

### `lemma laurentqExpansion_nat_mul_coeff`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero : …) (hfper : …) (k : ℤ) : (laurentqExpansion (m * h) f).coeff (m * k) = (laurentqExpansion h f).coeff k`
- **What**: The coefficient at `m k` for period `m h` is the coefficient at `k` for period `h`.
- **How**: `poleOrder_nat_mul`; case `k < −poleOrder`: both sides vanish by `laurentqExpansion.coeff_eq_zero_of_lt`; else `laurentqExpansion.coeff_of_geq` twice, `to_qExpansion_nat_mul`, `Int.toNat_mul` (core `Init/Data/Int/Order.lean`), `PowerSeries.coeff_expand_mul`.
- **Hypotheses**: `m ≠ 0`; cusp-meromorphic; `h`-periodic.
- **Uses from project**: poleOrder_nat_mul, poleOrder, laurentqExpansion.coeff_eq_zero_of_lt, laurentqExpansion.coeff_of_geq, to_qExpansion_nat_mul, laurentqExpansion
- **Used by**: unused in file; externally Kronecker.lean:213, DiagonalLaurent.lean:47, IntegralDescent.lean:240
- **Visibility**: public
- **Lines**: 384–413, proof ≈ 29 lines
- **Notes**: the `Int.toNat`/`push_cast` arithmetic (L398–412) is 14 lines of index bookkeeping.

### `lemma laurentqExpansion_nat_mul_coeff_of_not_dvd`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero : …) (hfper : …) {k : ℤ} (hk : ¬ (m : ℤ) ∣ k) : (laurentqExpansion (m * h) f).coeff k = 0`
- **What**: At period `m h`, coefficients with exponent not divisible by `m` vanish.
- **How**: below `−poleOrder` by `coeff_eq_zero_of_lt`; else `coeff_of_geq`, `to_qExpansion_nat_mul`, `PowerSeries.coeff_expand_of_not_dvd` (Expand.lean:97), translating `m ∣ toNat (k + m·poleOrder)` back to `m ∣ k` with `Int.toNat_of_nonneg` and `linear_combination`.
- **Hypotheses**: `m ≠ 0`; cusp-meromorphic; `h`-periodic; `m ∤ k`.
- **Uses from project**: poleOrder_nat_mul, poleOrder, laurentqExpansion.coeff_eq_zero_of_lt, laurentqExpansion.coeff_of_geq, to_qExpansion_nat_mul, laurentqExpansion
- **Used by**: unused in file; externally Kronecker.lean:239
- **Visibility**: public
- **Lines**: 417–439, proof ≈ 21 lines
- **Notes**: together with the previous lemma this says `laurentqExpansion (m h) f = HahnSeries.embDomain (·*m) (laurentqExpansion h f)` — the packaged Laurent statement is missing (mathlib has no `LaurentSeries.expand`, but `HahnSeries.embDomain` exists in HahnSeries/Basic.lean).

## File Summary
- Total declarations: 28 (2 defs — both private, 26 lemmas — 15 private / 11 public, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `shiftedLaurent` (5), `analyticAt_cuspFunction_const` (3 users, 4 sites), `laurentqExpansion_const` (3), `analyticTaylor` (3), `laurentqExpansion_eq_shiftedLaurent` (2 users, 6 sites), `analyticAt_cuspFunction_qpow_of_poleOrder_le` (2 users, 4 sites)
- Unused declarations (not used by anything in this file): `laurentqExpansion_zero` (ext 1), `laurentqExpansion_one` (ext 0), `laurentqExpansion_neg` (ext 1), `laurentqExpansion_finset_sum` (ext 1), `laurentqExpansion_finset_prod` (ext 3), `laurentqExpansion_nat_mul_coeff` (ext 3), `laurentqExpansion_nat_mul_coeff_of_not_dvd` (ext 1)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `hasFPowerSeriesAt_expand_analyticTaylor` (≈36)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- The analytic building blocks are mathlib's `UpperHalfPlane.qExpansion_add/mul/smul/neg/zero/one` (QExpansion.lean:466–515) and `HahnSeries.single_mul_single` (Multiplication.lean:776), `ofPowerSeries_X_pow` (PowerSeries.lean:140), `ofPowerSeries_C` (:114), `PowerSeries.expand` (Expand.lean:33, an `→ₐ[R]`), `coeff_expand_mul` (:87), `coeff_expand_of_not_dvd` (:97), `coeff_expand` (:110) — all grep-verified. The Laurent-level lifts are new; mathlib has no Laurent expansion of a meromorphic germ at all (no file under `Mathlib/Analysis` imports `LaurentSeries`/`HahnSeries`).
- `cuspFunction_const` (L40–46): mathlib proves `cuspFunction h 1 = 1` inline in `qExpansion_one` (QExpansion.lean:517–520) — upstream `UpperHalfPlane.cuspFunction_const` + `qExpansion_const : qExpansion h (fun _ ↦ a) = C a` (the latter is re-derived at L219–223 via `qExpansion_smul` on `1`).
- `qExpansion_qParam_pow` (L77–91): upstream `qExpansion_qParam_pow`/`qExpansion_qParam : qExpansion h (𝕢 h ·) = X` (no analogue; grepped QExpansion.lean).
- `analyticTaylor` + `hasFPowerSeriesAt_expand_analyticTaylor` + `analyticTaylor_comp_pow` (L285–339): general "Taylor series of `G ∘ (·^m)` is `expand m` of Taylor series of `G`"; mathlib gap (no `Mathlib/Analysis` file mentions `PowerSeries.expand`); belongs in `Analysis/Analytic` or `Analysis/Complex/TaylorSeries.lean`; only `ℂ`-specific input is `Complex.hasSum_taylorSeries_on_ball` (TaylorSeries.lean:45).
- Ring-hom packaging: mathlib bundles `qExpansionRingHom` for modular forms (QExpansion.lean:621); the analogue here would be a `RingHom` from the subring `{f : ℍ → ℂ | MeromorphicAt (cuspFunction h f) 0}` (whose closure properties are exactly LaurentQExpansion.lean `meromorphicAt_cuspFunction_add/mul/const`) to `LaurentSeries ℂ`; `laurentqExpansion_add/mul/zero/one/neg/finset_sum/finset_prod` (L163–281, ≈120 lines) would then be `map_add/map_mul/map_zero/map_one/map_neg/map_sum/map_prod`.
### Missing API / repeated patterns
- Common-shift block (L170–177 and L203–211): `set N := … ; rw [laurentqExpansion_eq_shiftedLaurent hh _ (N := N) (by omega)] ×3; exact shiftedLaurent_* (analyticAt_cuspFunction_qpow_of_poleOrder_le hh _ (by omega)) …` — duplicated because `poleOrder_add_le : poleOrder h (f+g) ≤ max …` and `poleOrder_mul_le : poleOrder h (f*g) ≤ poleOrder h f + poleOrder h g` are missing in LaurentQExpansion.lean.
- `Finset.induction_on` skeleton ×2 here (L255–264, L272–281) and ×2 in LaurentQExpansion.lean (L122–143).
- Statement forms use `fun τ ↦ f τ + g τ`, `fun τ ↦ f τ * g τ`, `fun τ ↦ -f τ` (L167, 200, 240) instead of `f + g`, `f * g`, `-f`; mathlib's convention (`qExpansion_add` at QExpansion.lean:487 uses `f + g`) — callers with `Pi` operations need `show`/`change` (LaurentQExpansion.lean L127, L141 already do this dance).
- Missing companions: `laurentqExpansion_sub`, `laurentqExpansion_smul`/`_const_mul`, `laurentqExpansion_pow`, `laurentqExpansion_qParam_pow` (public form of L77–91 lifted to Laurent: `= single n 1`), `laurentqExpansion_inv` (needs `meromorphicAt_cuspFunction_inv`), `laurentqExpansion_congr` (agreement of `f`, `g` on ℍ or near the cusp), the Laurent-level `laurentqExpansion_nat_mul : laurentqExpansion (m*h) f = embDomain … ` packaging L384–439; `hh : 0 < h` is asymmetrically required (add/mul/neg need it; const/zero/one do not) although `shiftedLaurent_add/mul` themselves are `h`-free.
- `norm_lt_one_mem_nhdsNE_zero` (L34) vs three inline copies in LaurentQExpansion.lean (L363, 380, 523).
### Junk candidates
- `laurentqExpansion_one` (L232–234): 0 external users (keep as API, but note).
- `to_qExpansion_nat_mul` (L365–381): public but 0 external users; only feeds the two coefficient lemmas.
- `hF` hypothesis of `analyticTaylor_comp_pow` (L331) is redundant.
- `hC : HahnSeries.C (-1 : ℂ) = (-1 : LaurentSeries ℂ) := by simp` (L241) — inline fact that should be `map_neg`/`HahnSeries.C_neg`+`C_one`.
### Moral duplicates within this batch
- `cuspFunction_const` (Algebra L40–46, global) vs `cuspFunction_const_eventuallyEq` (LaurentQExpansion L90–96, `𝓝[≠]`) vs mathlib `qExpansion_one` inline.
- `laurentqExpansion_finset_sum/prod` vs `meromorphicAt_cuspFunction_finset_sum/prod` (same induction).
- `shiftedLaurent` (L108) vs `UpperHalfPlane.laurentqExpansion` (LaurentQExpansion L326): same expression with `N` vs `poleOrder h f`.
- `cuspFunction_qpow_mul_eventuallyEq` (L55–67) vs `analyticAt_cuspFunction_poleRemoved`'s `hEq_shift` (LaurentQExpansion L378–384) — both are "`cuspFunction (q^n f) = q^n cuspFunction f` near 0" derived from `cuspFunction_qpow_mul_eq`.
### Generalization notes
- `shiftedLaurent_add`, `shiftedLaurent_mul` (L150–193) are purely formal (no `0 < h`, no meromorphy); they hold for any `h` given analyticity of the shifted cusp functions.
- `analyticTaylor`, `hasFPowerSeriesAt_expand_analyticTaylor`, `analyticTaylor_comp_pow` (L285–339) are statements about arbitrary `F G : ℂ → ℂ`; the `ℂ` dependence is only through `Complex.hasSum_taylorSeries_on_ball` and could be replaced by `HasFPowerSeriesAt.hasSum` for any `RCLike`/complete `𝕜` with `CharZero`.
- `laurentqExpansion_const/zero/one` (L214–234) need neither `0 < h` nor periodicity — correct as stated.
- `laurentqExpansion_nat_mul_coeff(_of_not_dvd)` (L384–439): the index arithmetic is generic HahnSeries/`expand` bookkeeping valid for `single (-N) 1 * ofPowerSeries F` over any semiring; the only analytic input is `to_qExpansion_nat_mul` + `poleOrder_nat_mul`.
