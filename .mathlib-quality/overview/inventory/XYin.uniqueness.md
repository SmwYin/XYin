# Source: /Users/dfa25dxu/Projects/Lean/XYin/XYin/uniqueness.lean — Project-internal imports: [] (only mathlib: `Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass`, `Mathlib.Data.Nat.Choose.Cast`, `Mathlib.Topology.Algebra.Module.Cardinality`)

All declarations live in `namespace PeriodPair`, inside a `noncomputable section`, with `variable (L : PeriodPair)`. The `PeriodPair` structure, the Weierstrass functions `℘[L]`, `℘'[L]`, the pole-removed `℘[L - l₀]` (`weierstrassPExcept`), Eisenstein series `G`, and invariants `g₂`, `g₃` all come from mathlib's `Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass`, not from this project.

### `attribute [local fun_prop] AnalyticAt.contDiffAt`
- **Type**: n/a (attribute command)
- **What**: Locally registers mathlib's `AnalyticAt.contDiffAt` as a `fun_prop` lemma so `fun_prop` can discharge `ContDiffAt` side goals from analyticity facts.
- **How**: `attribute [local fun_prop]` command; enables the `by fun_prop` discharges of `ContDiff` hypotheses in `iteratedDeriv_sq_mul` and `recursion`.
- **Hypotheses**: n/a
- **Uses from project**: []
- **Used by**: implicitly by `iteratedDeriv_sq_mul` and `recursion` (via `fun_prop` calls)
- **Visibility**: scoped (local attribute, file-only)
- **Lines**: 30, n/a
- **Notes**: none

### `lemma eventually_notMem_lattice`
- **Type**: `(L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice`
- **What**: Every point of some punctured neighbourhood of `0` in `ℂ` is not a lattice point of `L`. (The lattice is discrete, so `0` is its only point near `0`.)
- **How**: The complement of `lattice \ {0}` is a neighbourhood of `0` (mathlib's `PeriodPair.compl_lattice_diff_singleton_mem_nhds`, i.e. discreteness/closedness of the lattice); intersect with `z ≠ 0` from `self_mem_nhdsWithin` via `filter_upwards`.
- **Hypotheses**: none beyond `L : PeriodPair`.
- **Uses from project**: []
- **Used by**: `eventually_deriv_derivWeierstrassP`, `key_eventuallyEq`
- **Visibility**: public
- **Lines**: 36–40, proof 3 lines
- **Notes**: none

### `lemma weierstrassP_eq`
- **Type**: `(L : PeriodPair) (z : ℂ) : ℘[L] z = ℘[L - (0 : ℂ)] z + 1 / z ^ 2`
- **What**: Global pole decomposition of `℘` at `0`: `℘` equals the pole-removed function `℘[L - 0]` plus the principal part `1/z²`, for every `z` (at `z = 0` both sides are `0` by junk-value conventions).
- **How**: Rewrites with mathlib's `PeriodPair.weierstrassPExcept_add 0` (which re-adds the omitted lattice-point term `1/(z-l₀)² - 1/l₀²` for `l₀ = 0`) and simplifies.
- **Hypotheses**: none (holds for all `z` including `0` by junk values).
- **Uses from project**: []
- **Used by**: `key_eventuallyEq`, `weierstrassP_eventuallyEq`
- **Visibility**: public
- **Lines**: 42–46, proof 2 lines
- **Notes**: none

### `lemma derivWeierstrassPExcept_zero_eq`
- **Type**: `(L : PeriodPair) (z : ℂ) : ℘'[L - (0 : ℂ)] z = ℘'[L] z + 2 / z ^ 3`
- **What**: Global pole decomposition of `℘'` at `0`: the pole-removed derivative equals `℘'` plus `2/z³` (the derivative of `-1/z²` with sign conventions matching mathlib's `℘'[L - 0]`).
- **How**: Direct `simpa` from mathlib's `PeriodPair.derivWeierstrassPExcept_def 0`.
- **Hypotheses**: none (all `z`, junk values at `0`).
- **Uses from project**: []
- **Used by**: `eventually_derivWeierstrassP_ne_zero`, `key_eventuallyEq`
- **Visibility**: public
- **Lines**: 48–51, proof 1 line
- **Notes**: none

### `lemma iteratedDeriv_weierstrassPExcept_zero`
- **Type**: `(L : PeriodPair) (n : ℕ) : iteratedDeriv n ℘[L - (0 : ℂ)] 0 = if n = 0 then 0 else ((n + 1)! : ℂ) * L.G (n + 2)`
- **What**: The Taylor coefficients of the pole-removed `℘` at `0` are (up to factorials) the Eisenstein series: the `n`-th derivative at `0` is `(n+1)! · G(n+2)` for `n ≥ 1`, and `0` for `n = 0`. This is the classical Laurent expansion `℘(z) = 1/z² + Σ (n+1) G(n+2) zⁿ`.
- **How**: Direct rewrite of mathlib's `PeriodPair.iteratedDeriv_weierstrassPExcept_self 0` followed by `simp` (the `l₀ = 0` case removes the extra `sumInvPow` correction terms).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `recursion`, `iteratedDeriv_eq_of_invariants`
- **Visibility**: public
- **Lines**: 53–58, proof 2 lines
- **Notes**: none

### `lemma eventually_derivWeierstrassP_ne_zero`
- **Type**: `(L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ℘'[L] z ≠ 0`
- **What**: `℘'` is nonvanishing on some punctured neighbourhood of `0`, because it blows up like `-2/z³` there.
- **How**: Quantitative comparison: `℘'[L-0]` is analytic at `0` with value `0` (mathlib's `analyticAt_derivWeierstrassPExcept` and `derivWeierstrassPExcept_zero_zero`), so eventually `‖℘'[L-0] z‖ < 1`; if `℘'[L] z = 0` then by `derivWeierstrassPExcept_zero_eq` one gets `‖2/z³‖ < 1`, contradicting `‖z‖³ < 1` near `0` (via `pow_lt_one₀` and `linarith`).
- **Hypotheses**: none.
- **Uses from project**: [`derivWeierstrassPExcept_zero_eq`]
- **Used by**: `eventually_deriv_derivWeierstrassP`
- **Visibility**: public
- **Lines**: 62–78, proof 15 lines
- **Notes**: none

### `lemma eventually_deriv_derivWeierstrassP`
- **Type**: `(L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2`
- **What**: The second-order differential equation `℘'' = 6℘² − g₂/2`, valid on a punctured neighbourhood of `0`. This is obtained by differentiating the first-order equation `℘'² = 4℘³ − g₂℘ − g₃`.
- **How**: Differentiates both sides of mathlib's `PeriodPair.derivWeierstrassP_sq` (which holds as an `EventuallyEq` off the lattice): `HasDerivAt` chain rules give `2℘'℘'' = 12℘²℘' − g₂℘'`, then cancels the factor `2℘' ≠ 0` (from `eventually_derivWeierstrassP_ne_zero`) via `mul_left_cancel₀` and `linear_combination`.
- **Hypotheses**: none (the nonvanishing of `℘'` near `0` is supplied internally).
- **Uses from project**: [`eventually_notMem_lattice`, `eventually_derivWeierstrassP_ne_zero`]
- **Used by**: `key_eventuallyEq`
- **Visibility**: public
- **Lines**: 80–101, proof 20 lines
- **Notes**: none

### `lemma key_eventuallyEq`
- **Type**: `(L : PeriodPair) : (fun z : ℂ ↦ z ^ 2 * deriv ℘'[L - (0 : ℂ)] z) =ᶠ[𝓝 (0 : ℂ)] fun z ↦ 6 * (z ^ 2 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z)) + 12 * ℘[L - (0 : ℂ)] z - L.g₂ / 2 * z ^ 2`
- **What**: The pole-cleared second-derivative ODE as a germ at `0`: writing `f = ℘[L - 0]`, one has `z² f''(z)... ` more precisely `z²·(℘[L-0])''` (as `deriv ℘'[L-0]`) equals `6z²f² + 12f − (g₂/2)z²` on a full (unpunctured) neighbourhood of `0`. Multiplying by `z²` removes all poles so the identity extends across `0`.
- **How**: On the punctured neighbourhood: substitute `℘ = f + 1/z²` (`weierstrassP_eq`) and `℘'[L-0] = ℘' + 2/z³` (`derivWeierstrassPExcept_zero_eq`) into `eventually_deriv_derivWeierstrassP`, compute the derivative of `2/z³` as `−6/z⁴` via `HasDerivAt.div`, and clear denominators with `field_simp; ring`. At `z = 0` both sides vanish (checked on the `pure 0` filter); the two are glued with `Filter.eventually_sup` and `nhdsNE_sup_pure` to get the full-neighbourhood germ.
- **Hypotheses**: none.
- **Uses from project**: [`eventually_notMem_lattice`, `derivWeierstrassPExcept_zero_eq`, `eventually_deriv_derivWeierstrassP`, `weierstrassP_eq`]
- **Used by**: `recursion`
- **Visibility**: public
- **Lines**: 103–135, proof 30 lines
- **Notes**: proof exactly 30 lines; the `𝓝[≠] ⊔ pure = 𝓝` glueing trick (`nhdsNE_sup_pure`) is the key filter step
- 
### `lemma iteratedDeriv_sq_mul`
- **Type**: `(g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0) {n : ℕ} (hn : 2 ≤ n) : iteratedDeriv n (fun z : ℂ ↦ z ^ 2 * g z) 0 = (n : ℂ) * ((n : ℂ) - 1) * iteratedDeriv (n - 2) g 0`
- **What**: Leibniz collapse: for `g` analytic at `0` and `n ≥ 2`, the `n`-th derivative of `z² g(z)` at `0` is `n(n−1)` times the `(n−2)`-th derivative of `g` at `0` — only the `i = 2` term of the Leibniz sum survives since derivatives of `z²` at `0` vanish except in degree 2.
- **How**: Applies mathlib's `iteratedDeriv_fun_mul` (Leibniz rule) and collapses the binomial sum with `Finset.sum_eq_single_of_mem` at `i = 2`, using `iteratedDeriv_fun_pow_zero` (derivatives of `zᵏ` at `0`) and `Nat.cast_choose_two` for `C(n,2)·2! = n(n−1)`.
- **Hypotheses**: `g` analytic at `0`; `2 ≤ n`.
- **Uses from project**: []
- **Used by**: `recursion` (twice: for the LHS and for the `6z²f²` term)
- **Visibility**: public
- **Lines**: 139–150, proof 8 lines
- **Notes**: general-purpose helper, not specific to elliptic functions

### `lemma recursion`
- **Type**: `(L : PeriodPair) {n : ℕ} (hn : 3 ≤ n) : ((n : ℂ) * ((n : ℂ) - 1) - 12) * iteratedDeriv n ℘[L - (0 : ℂ)] 0 = 6 * ((n : ℂ) * ((n : ℂ) - 1)) * ∑ k ∈ Finset.range (n - 1), ((n - 2).choose k : ℂ) * iteratedDeriv k ℘[L - (0 : ℂ)] 0 * iteratedDeriv (n - 2 - k) ℘[L - (0 : ℂ)] 0`
- **What**: The classical Eisenstein-series recursion in Taylor-coefficient form: for `n ≥ 3`, `(n(n−1) − 12)` times the `n`-th derivative of `f = ℘[L - 0]` at `0` equals `6n(n−1)` times the degree-`(n−2)` Leibniz convolution of lower derivatives of `f`. Hence each coefficient beyond the first few is determined by earlier ones (except when `n(n−1) = 12`, i.e. `n = 4`).
- **How**: Takes the `n`-th iterated derivative at `0` of both sides of the germ identity `key_eventuallyEq` (via `Filter.EventuallyEq.iteratedDeriv_eq`). The LHS collapses by `iteratedDeriv_sq_mul` applied to `deriv ℘'[L-0]`, then converts `iteratedDeriv (n-2) (deriv ℘'[L-0])` back to `iteratedDeriv n f` via `iteratedDeriv_succ'` and mathlib's `iteratedDeriv_derivWeierstrassPExcept_self` / project's `iteratedDeriv_weierstrassPExcept_zero` (the `sumInvPow_zero` correction vanishes). The RHS splits by `iteratedDeriv_fun_add/sub`, uses `iteratedDeriv_sq_mul` again on `z²f²` and the Leibniz rule `iteratedDeriv_fun_mul` on `f·f`; final bookkeeping by `linear_combination`.
- **Hypotheses**: `3 ≤ n`.
- **Uses from project**: [`iteratedDeriv_sq_mul`, `iteratedDeriv_weierstrassPExcept_zero`, `key_eventuallyEq`]
- **Used by**: `iteratedDeriv_eq_of_invariants`
- **Visibility**: public
- **Lines**: 152–203, proof 45 lines
- **Notes**: proof >30 lines (45); the mathematical heart of the file

### `lemma iteratedDeriv_eq_of_invariants`
- **Type**: `{L₁ L₂ : PeriodPair} (hg₂ : L₁.g₂ = L₂.g₂) (hg₃ : L₁.g₃ = L₂.g₃) (n : ℕ) : iteratedDeriv n ℘[L₁ - (0 : ℂ)] 0 = iteratedDeriv n ℘[L₂ - (0 : ℂ)] 0`
- **What**: If two period pairs have equal invariants `g₂`, `g₃`, then all Taylor coefficients of their pole-removed `℘` functions at `0` agree. This is the "invariants determine the Laurent expansion" step.
- **How**: Strong induction on `n`. Base cases `n ≤ 4` by `iteratedDeriv_weierstrassPExcept_zero`: `n = 0` gives `0`; odd `n` gives `0` via mathlib's `G_eq_zero_of_odd`; `n = 2, 4` reduce to `G 4`, `G 6` which are recovered from `g₂ = 60·G 4`, `g₃ = 140·G 6` by `mul_left_cancel₀`. Inductive step `n ≥ 5`: apply `recursion` to both `L₁`, `L₂`; the convolution sums agree by the induction hypothesis, and the coefficient `n(n−1) − 12 ≠ 0` (since `n(n−1) ≥ 20`), so cancel it with `mul_left_cancel₀`.
- **Hypotheses**: `L₁.g₂ = L₂.g₂` and `L₁.g₃ = L₂.g₃`.
- **Uses from project**: [`iteratedDeriv_weierstrassPExcept_zero`, `recursion`]
- **Used by**: `lattice_eq_of_g₂_eq_of_g₃_eq`
- **Visibility**: public
- **Lines**: 207–248, proof 40 lines
- **Notes**: proof >30 lines (40); crucially avoids the singular case `n = 4` of the recursion by handling `n ≤ 4` directly from `g₂`, `g₃`

### `lemma weierstrassP_eventuallyEq`
- **Type**: `{L₁ L₂ : PeriodPair} (h : ∀ n, iteratedDeriv n ℘[L₁ - (0 : ℂ)] 0 = iteratedDeriv n ℘[L₂ - (0 : ℂ)] 0) : ℘[L₁] =ᶠ[𝓝 (0 : ℂ)] ℘[L₂]`
- **What**: Equal Taylor coefficients at `0` force the two `℘` functions to agree on a neighbourhood of `0` (off nothing — the `1/z²` poles cancel).
- **How**: Both `℘[Lᵢ - 0]` are analytic at `0`, so each `HasFPowerSeriesAt` its Taylor series (`AnalyticAt.hasFPowerSeriesAt` producing `FormalMultilinearSeries.ofScalars` of `iteratedDeriv n · / n!`); the hypothesis makes the two series equal, so the difference has the zero power series and vanishes eventually (`HasFPowerSeriesAt.eventually_eq_zero`). Adding back the common pole `1/z²` via `weierstrassP_eq` gives the germ equality of the full `℘`s.
- **Hypotheses**: all iterated derivatives of the pole-removed functions agree at `0`.
- **Uses from project**: [`weierstrassP_eq`]
- **Used by**: `lattice_eq_of_g₂_eq_of_g₃_eq`
- **Visibility**: public
- **Lines**: 252–272, proof 19 lines
- **Notes**: none

### `lemma eqOn_weierstrassP`
- **Type**: `{L₁ L₂ : PeriodPair} (hev : ℘[L₁] =ᶠ[𝓝 (0 : ℂ)] ℘[L₂]) : Set.EqOn ℘[L₁] ℘[L₂] ((L₁.lattice : Set ℂ) ∪ (L₂.lattice : Set ℂ))ᶜ`
- **What**: Analytic continuation: if the two `℘` functions agree near `0` then they agree on the whole complement of the union of the two lattices.
- **How**: Identity theorem for analytic functions: both `℘`s are analytic on the complement (mathlib's `analyticOnNhd_weierstrassP`); the union of two lattices is countable (`countable_of_Lindelof_of_discrete`), so its complement is connected (mathlib's `Set.Countable.isConnected_compl_of_one_lt_rank`, using `rank_ℝ ℂ = 2 > 1`) and dense; pick a point `z₀` of the complement inside the neighbourhood where the germs agree (`Set.Countable.dense_compl`), then apply `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
- **Hypotheses**: germ equality of `℘[L₁]` and `℘[L₂]` at `0` (note `0` itself lies in both lattices, hence the detour through a nearby non-lattice point `z₀`).
- **Uses from project**: []
- **Used by**: `lattice_eq_of_g₂_eq_of_g₃_eq`
- **Visibility**: public
- **Lines**: 274–291, proof 16 lines
- **Notes**: elegant use of countable-complement connectivity to avoid choosing an explicit path

### `lemma lattice_le_of_eqOn`
- **Type**: `{L₁ L₂ : PeriodPair} (h : Set.EqOn ℘[L₁] ℘[L₂] ((L₁.lattice : Set ℂ) ∪ (L₂.lattice : Set ℂ))ᶜ) : L₁.lattice ≤ L₂.lattice`
- **What**: The lattice is recovered from `℘` as its polar set: if the two `℘`s agree off the union of the lattices, then every `L₁`-lattice point is an `L₂`-lattice point.
- **How**: Pole-order comparison. Suppose `x ∈ L₁.lattice` but `x ∉ L₂.lattice`. On a punctured neighbourhood of `x` avoiding both `L₂.lattice` and `L₁.lattice \ {x}` the functions agree, so their meromorphic orders at `x` coincide (`meromorphicOrderAt_congr`). But `℘[L₁]` has order `−2` at `x` (mathlib's `PeriodPair.order_weierstrassP`) while `℘[L₂]` is analytic at `x`, giving order `≥ 0` (`AnalyticOnNhd.meromorphicOrderAt_nonneg`) — contradiction since `−2 < 0`.
- **Hypotheses**: the `EqOn` off the lattice union.
- **Uses from project**: []
- **Used by**: `lattice_eq_of_g₂_eq_of_g₃_eq` (applied twice, once per direction)
- **Visibility**: public
- **Lines**: 293–313, proof 19 lines
- **Notes**: none

### `theorem lattice_eq_of_g₂_eq_of_g₃_eq`
- **Type**: `{L₁ L₂ : PeriodPair} (hg₂ : L₁.g₂ = L₂.g₂) (hg₃ : L₁.g₃ = L₂.g₃) : L₁.lattice = L₂.lattice`
- **What**: **Main theorem — uniqueness for complex lattices**: a period lattice is completely determined by its invariants `g₂` and `g₃`.
- **How**: Chains the pipeline: equal invariants give equal Taylor coefficients (`iteratedDeriv_eq_of_invariants`), hence germ-equal `℘`s at `0` (`weierstrassP_eventuallyEq`), hence globally equal `℘`s off both lattices (`eqOn_weierstrassP`), hence mutual lattice containment by the polar-set argument (`lattice_le_of_eqOn` in both directions, symmetrising with `Set.union_comm`), concluded by `le_antisymm`.
- **Hypotheses**: `L₁.g₂ = L₂.g₂` and `L₁.g₃ = L₂.g₃`.
- **Uses from project**: [`iteratedDeriv_eq_of_invariants`, `weierstrassP_eventuallyEq`, `eqOn_weierstrassP`, `lattice_le_of_eqOn`]
- **Used by**: `invariantsDetermineLattice`; externally by `XYin/PhD/Cox/LatticeJ.lean` (lines 369, 393, 432 — homothety/j-invariant results)
- **Visibility**: public
- **Lines**: 317–325, proof 7 lines
- **Notes**: none

### `theorem invariantsDetermineLattice`
- **Type**: `∀ L₁ L₂ : PeriodPair, L₁.g₂ = L₂.g₂ → L₁.g₃ = L₂.g₃ → L₁.lattice = L₂.lattice`
- **What**: Restatement of the uniqueness theorem in the fully-universally-quantified form matching a statement named `InvariantsDetermineLattice` from a `talk4.lean` (a file not present in the current tree).
- **How**: Immediate eta-expansion of `lattice_eq_of_g₂_eq_of_g₃_eq`.
- **Hypotheses**: none (quantified internally).
- **Uses from project**: [`lattice_eq_of_g₂_eq_of_g₃_eq`]
- **Used by**: unused in file (and no other file in the project references it; the referenced `talk4.lean` does not exist in the tree)
- **Visibility**: public
- **Lines**: 327–330, proof 1 line
- **Notes**: docstring references `talk4.lean`, which is absent from the repository — possible dead restatement

### File Summary
- Total declarations: 16 (0 defs, 15 lemmas/theorems, 0 instances, 0 tactic/meta decls; plus 1 attribute command)
- Key API (used by 3+ others): [] (within this file nothing reaches 3 users; heaviest in-file: `iteratedDeriv_weierstrassPExcept_zero`, `weierstrassP_eq`, `derivWeierstrassPExcept_zero_eq`, `eventually_notMem_lattice`, `iteratedDeriv_sq_mul` each with 2. Externally, `lattice_eq_of_g₂_eq_of_g₃_eq` has 3 call sites in `XYin/PhD/Cox/LatticeJ.lean`.)
- Unused declarations (not used by anything in this file): [`invariantsDetermineLattice`] (also unused project-wide)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [`recursion` (45 lines), `iteratedDeriv_eq_of_invariants` (40 lines)]
