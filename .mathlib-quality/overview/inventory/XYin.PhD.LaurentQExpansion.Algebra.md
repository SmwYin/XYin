# Source: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/LaurentQExpansion/Algebra.lean
Project-internal imports: `XYin.PhD.LaurentQExpansion.LaurentQExpansion`

File-level: mathlib-style copyright header + module docstring present; `noncomputable section`; declarations in root namespace (relying on `open UpperHalfPlane` for `laurentqExpansion`, `poleOrder`, etc.).

### `[notation] 𝔢` (local)
- **Type**: `local notation "𝔢" => Periodic.qParam`
- **What**: Local notation for the q-parameter map exp(2πiτ/h).
- **How**: Notation only.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: all `qpow`/`shiftedLaurent` lemmas in this file
- **Visibility**: local
- **Lines**: 22
- **Notes**: inconsistent with `𝕢` used in LaurentQExpansion.lean for the same map.

### `[lemma] cuspFunction_qpow_mul_eventuallyEq` (private)
- **Type**: `{h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) : cuspFunction h (fun τ ↦ (𝔢 h τ)^n * f τ) =ᶠ[nhds 0] fun q ↦ q^n * cuspFunction h f q`
- **What**: Upgrades the punctured-disc identity "cusp function of q(τ)^n·f = q^n·(cusp function of f)" to a full neighbourhood of 0, given analyticity of the cusp function of f.
- **How**: On the punctured disc the identity is `cuspFunction_qpow_mul_eq`; the value at 0 is pinned down by `Periodic.cuspFunction_zero_eq_limUnder_nhds_ne` and continuity of the analytic right-hand side, then glued by `eventuallyEq_nhds_of_eventuallyEq_nhdsNE`.
- **Hypotheses**: h > 0; cuspFunction h f analytic at 0.
- **Uses from project**: [`cuspFunction_qpow_mul_eq`]
- **Used by**: `analyticAt_cuspFunction_qpow_mul`, `qExpansion_qParam_pow`
- **Visibility**: private
- **Lines**: 24–53, proof 28 lines
- **Notes**: none

### `[lemma] analyticAt_cuspFunction_qpow_mul` (private)
- **Type**: `{h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) : AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝔢 h τ)^n * f τ)) 0`
- **What**: Multiplying an analytic-at-the-cusp function by q(τ)^n preserves analyticity of the cusp function.
- **How**: q^n·cuspFunction h f is analytic (product of analytic functions) and agrees near 0 with the target by `cuspFunction_qpow_mul_eventuallyEq`; transfer by `AnalyticAt.congr`.
- **Hypotheses**: h > 0; analyticity at 0.
- **Uses from project**: [`cuspFunction_qpow_mul_eventuallyEq`]
- **Used by**: `qExpansion_qpow_mul`, `analyticAt_cuspFunction_qpow_of_poleOrder_le`
- **Visibility**: private
- **Lines**: 55–61, proof 2 lines
- **Notes**: none

### `[lemma] qExpansion_qParam_pow` (private)
- **Type**: `(h : ℝ) (hh : 0 < h) (n : ℕ) : qExpansion h (fun τ : ℍ ↦ (𝔢 h τ)^n) = (PowerSeries.X : PowerSeries ℂ)^n`
- **What**: The q-expansion of the function τ ↦ q(τ)^n is exactly the monomial X^n.
- **How**: The cusp function of the constant 1 is the constant function 1, so by `cuspFunction_qpow_mul_eventuallyEq` the cusp function of q(τ)^n is q ↦ q^n near 0; coefficients are computed from `qExpansion_coeff` via `EventuallyEq.iteratedDeriv_eq` and `iteratedDeriv_fun_pow_zero`, matching `PowerSeries.coeff_X_pow` (with the n!·(n!)⁻¹ cancellation `inv_mul_cancel₀`).
- **Hypotheses**: h > 0.
- **Uses from project**: [`cuspFunction_qpow_mul_eventuallyEq`]
- **Used by**: `qExpansion_qpow_mul`
- **Visibility**: private
- **Lines**: 63–86, proof 22 lines
- **Notes**: none

### `[lemma] qExpansion_qpow_mul` (private)
- **Type**: `{h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) : qExpansion h (fun τ ↦ (𝔢 h τ)^n * f τ) = X^n * qExpansion h f`
- **What**: Multiplying by q(τ)^n on functions corresponds to multiplying by X^n on q-expansions.
- **How**: mathlib's multiplicativity `qExpansion_mul` (valid for analytic cusp functions) combined with `qExpansion_qParam_pow`; analyticity of the q^n factor from `analyticAt_cuspFunction_qpow_mul` applied to the constant 1.
- **Hypotheses**: h > 0; cuspFunction h f analytic at 0.
- **Uses from project**: [`qExpansion_qParam_pow`, `analyticAt_cuspFunction_qpow_mul`]
- **Used by**: `laurentqExpansion_eq_shiftedLaurent`
- **Visibility**: private
- **Lines**: 88–105, proof 16 lines
- **Notes**: re-proves `cuspFunction h 1 = 1` inline, duplicating the identical block in `qExpansion_qParam_pow` and `analyticAt_cuspFunction_const`.

### `[def] shiftedLaurent` (private)
- **Type**: `(h : ℝ) (N : ℕ) (f : ℍ → ℂ) : LaurentSeries ℂ`
- **What**: The "shift by N" presentation of a Laurent expansion: q^{−N}·(power series of q(τ)^N·f(τ)). For any N ≥ poleOrder this recovers the Laurent q-expansion, giving a presentation with a common denominator for algebraic manipulations.
- **How**: Direct definition `single(−N) 1 * ofPowerSeries(qExpansion h (q^N·f))`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `laurentqExpansion_eq_shiftedLaurent`, `laurentqExpansion_add`, `laurentqExpansion_mul`
- **Visibility**: private
- **Lines**: 107–110
- **Notes**: none

### `[lemma] laurentqExpansion_eq_shiftedLaurent` (private)
- **Type**: `{h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) {N : ℕ} (hN : poleOrder h f ≤ N) : laurentqExpansion h f = shiftedLaurent h N f`
- **What**: The Laurent q-expansion is independent of the chosen denominator exponent: any N ≥ M gives the same Laurent series via the shifted presentation. This is the workhorse allowing sums/products to be computed with one common N.
- **How**: Writes q^N·f = q^{N−M}·(poleRemoved f); by `qExpansion_qpow_mul` (applicable because `analyticAt_cuspFunction_poleRemoved` gives analyticity) its q-expansion is X^{N−M}·to_qExpansion, and `HahnSeries.ofPowerSeries_X_pow` plus `HahnSeries.single_mul_single` collapse single(−N)·X^{N−M} to single(−M).
- **Hypotheses**: h > 0; cusp-meromorphy; N ≥ poleOrder.
- **Uses from project**: [`UpperHalfPlane.laurentqExpansion`, `UpperHalfPlane.poleOrder`, `UpperHalfPlane.poleRemoved`, `UpperHalfPlane.to_qExpansion`, `shiftedLaurent`, `qExpansion_qpow_mul`, `analyticAt_cuspFunction_poleRemoved`]
- **Used by**: `laurentqExpansion_add`, `laurentqExpansion_mul`
- **Visibility**: private
- **Lines**: 112–144, proof 30 lines
- **Notes**: none

### `[lemma] analyticAt_cuspFunction_qpow_of_poleOrder_le` (private)
- **Type**: `{h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) {N : ℕ} (hN : poleOrder h f ≤ N) : AnalyticAt ℂ (cuspFunction h (fun τ ↦ (𝔢 h τ)^N * f τ)) 0`
- **What**: For N at least the pole order, q(τ)^N·f(τ) has analytic cusp function — the analytic counterpart of the shifted presentation.
- **How**: Same factorization q^N·f = q^{N−M}·poleRemoved f as in `laurentqExpansion_eq_shiftedLaurent`, then `analyticAt_cuspFunction_qpow_mul` on top of `analyticAt_cuspFunction_poleRemoved`.
- **Hypotheses**: h > 0; cusp-meromorphy; N ≥ poleOrder.
- **Uses from project**: [`UpperHalfPlane.poleOrder`, `UpperHalfPlane.poleRemoved`, `analyticAt_cuspFunction_qpow_mul`, `analyticAt_cuspFunction_poleRemoved`]
- **Used by**: `laurentqExpansion_add`, `laurentqExpansion_mul`
- **Visibility**: private
- **Lines**: 146–164, proof 17 lines
- **Notes**: duplicates the `hfun` factorization block of `laurentqExpansion_eq_shiftedLaurent` verbatim.

### `[lemma] laurentqExpansion_add`
- **Type**: `{h : ℝ} (hh : 0 < h) {f g : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) (hg : MeromorphicAt (cuspFunction h g) 0) : laurentqExpansion h (fun τ ↦ f τ + g τ) = laurentqExpansion h f + laurentqExpansion h g`
- **What**: Additivity of the Laurent q-expansion on cusp-meromorphic functions.
- **How**: Chooses the common shift N = M_f + M_g + M_{f+g} dominating all three pole orders, rewrites all three Laurent expansions via `laurentqExpansion_eq_shiftedLaurent`, and reduces to additivity of the ordinary q-expansion (mathlib's `qExpansion_add`, applicable by `analyticAt_cuspFunction_qpow_of_poleOrder_le`); distributivity `mul_add` finishes on the Hahn-series side.
- **Hypotheses**: h > 0; both summands cusp-meromorphic (sum is cusp-meromorphic via `meromorphicAt_cuspFunction_add`).
- **Uses from project**: [`laurentqExpansion_eq_shiftedLaurent`, `analyticAt_cuspFunction_qpow_of_poleOrder_le`, `meromorphicAt_cuspFunction_add`, `shiftedLaurent`, `UpperHalfPlane.poleOrder`, `UpperHalfPlane.laurentqExpansion`]
- **Used by**: `laurentqExpansion_finset_sum`
- **Visibility**: public
- **Lines**: 167–199, proof 30 lines
- **Notes**: none

### `[lemma] laurentqExpansion_mul`
- **Type**: `{h : ℝ} (hh : 0 < h) {f g : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) (hg : MeromorphicAt (cuspFunction h g) 0) : laurentqExpansion h (fun τ ↦ f τ * g τ) = laurentqExpansion h f * laurentqExpansion h g`
- **What**: Multiplicativity of the Laurent q-expansion: the map f ↦ laurentqExpansion h f is a ring homomorphism on cusp-meromorphic functions (together with `laurentqExpansion_add`).
- **How**: Splits the total shift N = A + B with A = M_f + M_{fg}, B = M_g so that q^N·(fg) = (q^A·f)·(q^B·g); rewrites all three expansions with `laurentqExpansion_eq_shiftedLaurent`, applies mathlib's `qExpansion_mul` (justified by `analyticAt_cuspFunction_qpow_of_poleOrder_le`), and matches single-terms with `HahnSeries.single_mul_single` and `mul_mul_mul_comm`.
- **Hypotheses**: h > 0; both factors cusp-meromorphic (product cusp-meromorphic via `meromorphicAt_cuspFunction_mul`).
- **Uses from project**: [`laurentqExpansion_eq_shiftedLaurent`, `analyticAt_cuspFunction_qpow_of_poleOrder_le`, `meromorphicAt_cuspFunction_mul`, `shiftedLaurent`, `UpperHalfPlane.poleOrder`, `UpperHalfPlane.laurentqExpansion`]
- **Used by**: `laurentqExpansion_neg`, `laurentqExpansion_finset_prod`
- **Visibility**: public
- **Lines**: 202–243, proof 38 lines
- **Notes**: proof >30 lines. Subtle point: the choice A = M_f + M_{fg} (not just M_f) is what makes the final exponent bookkeeping −N = −A + −B work while also dominating M_{fg} ≤ N.

### `[lemma] analyticAt_cuspFunction_const` (private)
- **Type**: `(h : ℝ) (a : ℂ) : AnalyticAt ℂ (cuspFunction h (fun _ : ℍ ↦ a)) 0`
- **What**: The cusp function of a constant function is analytic at 0 (indeed constant).
- **How**: Shows `cuspFunction h (const a) = const a` pointwise — at q ≠ 0 by `Periodic.cuspFunction_eq_of_nonzero`, at 0 because the limit of a constant is that constant (`Filter.Tendsto.limUnder_eq`) — then `analyticAt_const`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `laurentqExpansion_zero`, `laurentqExpansion_one`, `laurentqExpansion_const`
- **Visibility**: private
- **Lines**: 245–254, proof 9 lines
- **Notes**: the sub-proof `cuspFunction h 1 = 1` appearing in `qExpansion_qParam_pow`/`qExpansion_qpow_mul` is a special case of this — could be shared.

### `[lemma] laurentqExpansion_zero`
- **Type**: `@[simp] (h : ℝ) : laurentqExpansion h (0 : ℍ → ℂ) = 0`
- **What**: The Laurent q-expansion of the zero function is the zero Laurent series.
- **How**: The zero function has analytic cusp function (`analyticAt_cuspFunction_const`), so its pole order vanishes by `analyticAt_iff`, `laurentqExpansion.eq_qExpansion_iff` reduces to the ordinary q-expansion, and mathlib's `qExpansion_zero` finishes.
- **Hypotheses**: none.
- **Uses from project**: [`meromorphicAt_cuspFunction_const`, `analyticAt_cuspFunction_const`, `analyticAt_iff`, `laurentqExpansion.eq_qExpansion_iff`, `UpperHalfPlane.poleOrder`, `UpperHalfPlane.laurentqExpansion`]
- **Used by**: `laurentqExpansion_finset_sum` (via `simp` in the empty case)
- **Visibility**: public
- **Lines**: 257–268, proof 11 lines
- **Notes**: @[simp]

### `[lemma] laurentqExpansion_one`
- **Type**: `@[simp] (h : ℝ) : laurentqExpansion h (1 : ℍ → ℂ) = 1`
- **What**: The Laurent q-expansion of the constant-one function is the unit Laurent series.
- **How**: Same route as `laurentqExpansion_zero`: pole order 0 via `analyticAt_cuspFunction_const` and `analyticAt_iff`, then `laurentqExpansion.eq_qExpansion_iff` and mathlib's `qExpansion_one`.
- **Hypotheses**: none.
- **Uses from project**: [`meromorphicAt_cuspFunction_const`, `analyticAt_cuspFunction_const`, `analyticAt_iff`, `laurentqExpansion.eq_qExpansion_iff`, `UpperHalfPlane.poleOrder`, `UpperHalfPlane.laurentqExpansion`]
- **Used by**: `laurentqExpansion_finset_prod` (via `simp` in the empty case)
- **Visibility**: public
- **Lines**: 271–282, proof 11 lines
- **Notes**: @[simp]

### `[lemma] laurentqExpansion_const`
- **Type**: `@[simp] (h : ℝ) (a : ℂ) : laurentqExpansion h (fun _ : ℍ ↦ a) = HahnSeries.C a`
- **What**: The Laurent q-expansion of a constant function a is the constant Laurent series C a.
- **How**: Pole order 0 as above reduces to the ordinary q-expansion; writing const a = a • 1 and using mathlib's `qExpansion_smul` plus `PowerSeries.smul_eq_C_mul` gives qExpansion = C a, transported by `HahnSeries.ofPowerSeries_C`.
- **Hypotheses**: none.
- **Uses from project**: [`meromorphicAt_cuspFunction_const`, `analyticAt_cuspFunction_const`, `analyticAt_iff`, `laurentqExpansion.eq_qExpansion_iff`, `UpperHalfPlane.poleOrder`, `UpperHalfPlane.laurentqExpansion`]
- **Used by**: `laurentqExpansion_neg`
- **Visibility**: public
- **Lines**: 285–302, proof 17 lines
- **Notes**: @[simp]; subsumes `laurentqExpansion_zero`/`_one` up to simp normal forms.

### `[lemma] laurentqExpansion_neg`
- **Type**: `{h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) : laurentqExpansion h (fun τ ↦ -f τ) = -laurentqExpansion h f`
- **What**: The Laurent q-expansion commutes with negation.
- **How**: Writes −f = (−1)·f and applies multiplicativity `laurentqExpansion_mul` with the constant −1, evaluated by `laurentqExpansion_const` and `HahnSeries.C(−1) = −1`.
- **Hypotheses**: h > 0; f cusp-meromorphic.
- **Uses from project**: [`meromorphicAt_cuspFunction_const`, `laurentqExpansion_mul`, `laurentqExpansion_const`, `UpperHalfPlane.laurentqExpansion`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 305–317, proof 12 lines
- **Notes**: none

### `[lemma] laurentqExpansion_finset_sum`
- **Type**: `{h : ℝ} (hh : 0 < h) {I : Type*} (s : Finset I) {f : I → ℍ → ℂ} (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) : laurentqExpansion h (∑ i ∈ s, f i) = ∑ i ∈ s, laurentqExpansion h (f i)`
- **What**: The Laurent q-expansion commutes with finite pointwise sums.
- **How**: `Finset.induction_on`; the step is `laurentqExpansion_add` with the tail's cusp-meromorphy supplied by `meromorphicAt_cuspFunction_finset_sum`; the empty case is `laurentqExpansion_zero` via simp.
- **Hypotheses**: h > 0; every summand cusp-meromorphic.
- **Uses from project**: [`laurentqExpansion_add`, `meromorphicAt_cuspFunction_finset_sum`, `laurentqExpansion_zero`, `UpperHalfPlane.laurentqExpansion`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 320–334, proof 13 lines
- **Notes**: none

### `[lemma] laurentqExpansion_finset_prod`
- **Type**: `{h : ℝ} (hh : 0 < h) {I : Type*} (s : Finset I) {f : I → ℍ → ℂ} (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) : laurentqExpansion h (∏ i ∈ s, f i) = ∏ i ∈ s, laurentqExpansion h (f i)`
- **What**: The Laurent q-expansion commutes with finite pointwise products.
- **How**: `Finset.induction_on`; step is `laurentqExpansion_mul` with tail cusp-meromorphy from `meromorphicAt_cuspFunction_finset_prod`; empty case is `laurentqExpansion_one` via simp.
- **Hypotheses**: h > 0; every factor cusp-meromorphic.
- **Uses from project**: [`laurentqExpansion_mul`, `meromorphicAt_cuspFunction_finset_prod`, `laurentqExpansion_one`, `UpperHalfPlane.laurentqExpansion`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 337–351, proof 13 lines
- **Notes**: none

### `[lemma] analyticAt_hasFPowerSeriesAt_taylor` (private)
- **Type**: `{F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) : HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ (n.factorial)⁻¹ * iteratedDeriv n F 0)) 0`
- **What**: An analytic function at 0 is represented near 0 by its classical Taylor series with coefficients F⁽ⁿ⁾(0)/n!.
- **How**: `AnalyticAt.exists_ball_analyticOnNhd` provides a ball of analyticity; mathlib's `Complex.hasSum_taylorSeries_on_ball` gives the pointwise Taylor-sum representation, massaged into `hasFPowerSeriesAt_iff` form via `FormalMultilinearSeries.coeff_ofScalars`.
- **Hypotheses**: F analytic at 0.
- **Uses from project**: []
- **Used by**: `analyticTaylor_comp_pow`
- **Visibility**: private
- **Lines**: 353–364, proof 10 lines
- **Notes**: general complex-analysis fact; likely subsumed by mathlib's `AnalyticAt`/`taylorSeries` API.

### `[def] analyticTaylor` (private)
- **Type**: `(F : ℂ → ℂ) : PowerSeries ℂ`
- **What**: The formal Taylor series ∑ (F⁽ⁿ⁾(0)/n!)·Xⁿ of a function at 0; for cusp functions this coincides definitionally with `qExpansion`.
- **How**: `PowerSeries.mk fun n ↦ (n.factorial)⁻¹ * iteratedDeriv n F 0`.
- **Hypotheses**: none (meaningful for F analytic at 0).
- **Uses from project**: []
- **Used by**: `analyticTaylor_comp_pow`, `to_qExpansion_nat_mul`
- **Visibility**: private
- **Lines**: 366–367
- **Notes**: none

### `[lemma] analyticTaylor_comp_pow` (private)
- **Type**: `{F G : ℂ → ℂ} {m : ℕ} (hm : m ≠ 0) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) (hEq : F =ᶠ[nhds 0] G ∘ (·^m)) : analyticTaylor F = (analyticTaylor G).expand m hm`
- **What**: If F(q) = G(q^m) near 0, the Taylor series of F is the m-fold expansion (X ↦ X^m substitution) of the Taylor series of G — uniqueness of power-series representations under substitution by a monomial.
- **How**: Builds `HasFPowerSeriesAt F` with the expanded coefficient series: the Taylor sum of G at q^m (`Complex.hasSum_taylorSeries_on_ball`) is reindexed along the injection n ↦ m·n (`Function.Injective.hasSum_iff`, with off-image coefficients killed by `PowerSeries.coeff_expand` for non-multiples of m and identified by `PowerSeries.coeff_expand_mul` on multiples); then uniqueness of power series `HasFPowerSeriesAt.eq_formalMultilinearSeries` against `analyticAt_hasFPowerSeriesAt_taylor` identifies coefficients.
- **Hypotheses**: m ≠ 0; F, G analytic at 0; F = G∘(·^m) near 0.
- **Uses from project**: [`analyticTaylor`, `analyticAt_hasFPowerSeriesAt_taylor`]
- **Used by**: `to_qExpansion_nat_mul`
- **Visibility**: private
- **Lines**: 369–413, proof 44 lines
- **Notes**: proof >30 lines; general fact about `PowerSeries.expand`, independent of modular forms — mathlib candidate.

### `[lemma] to_qExpansion_nat_mul`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (hfper : Periodic (f ∘ ofComplex) h) : to_qExpansion ((m : ℝ) * h) f = (to_qExpansion h f).expand m hm`
- **What**: Enlarging the period from h to m·h transforms the pole-removed q-expansion by the substitution X ↦ X^m — the coefficient a_k for period h becomes the coefficient at index m·k for period m·h.
- **How**: Let F, G be the pole-removed cusp functions for periods m·h and h. On the punctured disc, F(q) = q^{M_{mh}}·cusp_{mh}f(q) = q^{m·M_h}·cusp_h f(q^m) = G(q^m), using `cuspFunction_poleRemoved_eq` (twice), the period-change identity `cuspFunction_nat_mul_eq_cuspFunction_pow`, and the pole-order scaling `poleOrder_nat_mul`; both sides are analytic (`analyticAt_cuspFunction_poleRemoved`, `meromorphicAt_cuspFunction_nat_mul`), so `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE` upgrades to a full neighbourhood, and `analyticTaylor_comp_pow` transfers to the Taylor/q-expansion level.
- **Hypotheses**: m ≠ 0; cusp-meromorphy for h; h-periodicity of f∘ofComplex.
- **Uses from project**: [`meromorphicAt_cuspFunction_nat_mul`, `poleOrder_nat_mul`, `analyticAt_cuspFunction_poleRemoved`, `cuspFunction_poleRemoved_eq`, `cuspFunction_nat_mul_eq_cuspFunction_pow`, `analyticTaylor_comp_pow`, `analyticTaylor`, `UpperHalfPlane.to_qExpansion`, `UpperHalfPlane.poleRemoved`, `UpperHalfPlane.poleOrder`]
- **Used by**: `laurentqExpansion_nat_mul_coeff`, `laurentqExpansion_nat_mul_coeff_of_not_dvd`
- **Visibility**: public
- **Lines**: 416–463, proof 46 lines
- **Notes**: proof >30 lines.

### `[lemma] laurentqExpansion_nat_mul_coeff`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (hfper : Periodic (f ∘ ofComplex) h) (k : ℤ) : (laurentqExpansion ((m : ℝ) * h) f).coeff ((m : ℤ) * k) = (laurentqExpansion h f).coeff k`
- **What**: Under period enlargement h ↦ m·h, the Laurent coefficient at exponent m·k equals the original coefficient at k (the Laurent series is the substitution q ↦ q^m of the original).
- **How**: Case split on k < −M_h vs k ≥ −M_h. Below the cutoff both coefficients vanish by `laurentqExpansion.coeff_eq_zero_of_lt`, with the m·h cutoff scaled by `poleOrder_nat_mul`. Above it, both reduce via `laurentqExpansion.coeff_of_geq` to power-series coefficients, related by `to_qExpansion_nat_mul` and `PowerSeries.coeff_expand_mul` after the toNat index computation `Int.toNat_mul`.
- **Hypotheses**: m ≠ 0; cusp-meromorphy; h-periodicity.
- **Uses from project**: [`poleOrder_nat_mul`, `laurentqExpansion.coeff_eq_zero_of_lt`, `laurentqExpansion.coeff_of_geq`, `to_qExpansion_nat_mul`, `UpperHalfPlane.laurentqExpansion`, `UpperHalfPlane.poleOrder`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 466–500, proof 33 lines
- **Notes**: proof >30 lines.

### `[lemma] laurentqExpansion_nat_mul_coeff_of_not_dvd`
- **Type**: `{h : ℝ} {m : ℕ} (hm : m ≠ 0) {f : ℍ → ℂ} (hmero : MeromorphicAt (cuspFunction h f) 0) (hfper : Periodic (f ∘ ofComplex) h) {k : ℤ} (hk : ¬(m : ℤ) ∣ k) : (laurentqExpansion ((m : ℝ) * h) f).coeff k = 0`
- **What**: After enlarging the period by m, all Laurent coefficients at exponents not divisible by m vanish — together with the previous lemma this fully determines the m·h-expansion from the h-expansion.
- **How**: Below the cutoff, `laurentqExpansion.coeff_eq_zero_of_lt`; otherwise `laurentqExpansion.coeff_of_geq` plus `to_qExpansion_nat_mul` reduce to `PowerSeries.coeff_expand_of_not_dvd`, where divisibility of the shifted index k + m·M_h by m is converted back to m ∣ k by integer arithmetic (`Int.toNat_of_nonneg`, `linear_combination`).
- **Hypotheses**: m ≠ 0; cusp-meromorphy; h-periodicity; m ∤ k.
- **Uses from project**: [`poleOrder_nat_mul`, `laurentqExpansion.coeff_eq_zero_of_lt`, `laurentqExpansion.coeff_of_geq`, `to_qExpansion_nat_mul`, `UpperHalfPlane.laurentqExpansion`, `UpperHalfPlane.poleOrder`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 504–528, proof 24 lines
- **Notes**: none

### File Summary
- Total declarations: 23 (2 defs, 20 lemmas/theorems, 0 instances, 1 local notation)
- Key API (used by 3+ others): `shiftedLaurent` (3), `laurentqExpansion_eq_shiftedLaurent` (2, both main ring lemmas), `analyticAt_cuspFunction_const` (3), `analyticAt_cuspFunction_qpow_of_poleOrder_le` (2), `to_qExpansion_nat_mul` (2), plus heavy reliance on LaurentQExpansion.lean's `poleOrder`/`poleRemoved`/`to_qExpansion`/`laurentqExpansion`/`analyticAt_cuspFunction_poleRemoved`
- Unused declarations (not used by anything in this file): `laurentqExpansion_neg`, `laurentqExpansion_finset_sum`, `laurentqExpansion_finset_prod`, `laurentqExpansion_nat_mul_coeff`, `laurentqExpansion_nat_mul_coeff_of_not_dvd` (all are intended public API for downstream files)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: `laurentqExpansion_mul` (38), `analyticTaylor_comp_pow` (44), `to_qExpansion_nat_mul` (46), `laurentqExpansion_nat_mul_coeff` (33)
