# Inventory: XYin/uniqueness.lean  (297 lines)

Proves the classical **uniqueness theorem for complex lattices**: a `PeriodPair` lattice is determined by its Weierstrass invariants `g₂`, `g₃`. Route: derive `℘'' = 6℘² − g₂/2` from mathlib's `derivWeierstrassP_sq`, turn it into a recursion for the Taylor coefficients of `℘[L − 0]` at `0`, conclude `℘[L₁] = ℘[L₂]` by the identity theorem, and read the lattice off as the polar set. Builds entirely on mathlib's `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` (namespace `PeriodPair`). Imported only by `XYin/PhD/Cox/LatticeJ.lean` (uses `lattice_eq_of_g₂_eq_of_g₃_eq` at lines 328, 346, 380); NOT in the `XYin.lean` root import list.

## Declarations

### `attribute [local fun_prop] AnalyticAt.contDiffAt`
- **Type**: attribute registration (line 30)
- **What**: lets `fun_prop` discharge `ContDiffAt` side goals from analyticity (needed by `iteratedDeriv_fun_mul`/`_add`/`_sub` calls in `iteratedDeriv_sq_mul`, `recursion`).
- **How**: local attribute; no proof.
- **Hypotheses**: n/a
- **Uses from project**: []
- **Used by**: iteratedDeriv_sq_mul (L146), recursion (L171–176)
- **Visibility**: local
- **Lines**: 30
- **Notes**: fine; could be upstreamed as a global `@[fun_prop]` alias in mathlib.

### `lemma PeriodPair.eventually_notMem_lattice`
- **Type**: `(L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice`
- **What**: Points of a punctured neighbourhood of `0` are not lattice points (the lattice is discrete).
- **How**: `L.compl_lattice_diff_singleton_mem_nhds 0` (mathlib, Weierstrass.lean:138) gives `(L.lattice \ {0})ᶜ ∈ 𝓝 0`; intersect with `z ≠ 0` from `self_mem_nhdsWithin`.
- **Hypotheses**: none beyond `L` a period pair.
- **Uses from project**: []
- **Used by**: eventually_deriv_derivWeierstrassP, key_eventuallyEq
- **Visibility**: public
- **Lines**: 37–40, proof ≈ 3 lines
- **Notes**: none.

### `lemma PeriodPair.weierstrassP_eq`
- **Type**: `(L : PeriodPair) (z : ℂ) : ℘[L] z = ℘[L - (0 : ℂ)] z + 1 / z ^ 2`
- **What**: Global decomposition of `℘` into its pole part `1/z²` at `0` and the analytic remainder `℘[L − 0]` (valid at `z = 0` thanks to junk values).
- **How**: rewrite with mathlib `L.weierstrassPExcept_add 0 z` (Weierstrass.lean:267) and `simp`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: key_eventuallyEq, weierstrassP_eventuallyEq
- **Visibility**: public
- **Lines**: 44–46, proof ≈ 2 lines
- **Notes**: name is too generic; mathlib style would be `weierstrassP_eq_weierstrassPExcept_zero_add`.

### `lemma PeriodPair.derivWeierstrassPExcept_zero_eq`
- **Type**: `(L : PeriodPair) (z : ℂ) : ℘'[L - (0 : ℂ)] z = ℘'[L] z + 2 / z ^ 3`
- **What**: Global pole decomposition of `℘'` at `0`.
- **How**: `simpa using L.derivWeierstrassPExcept_def 0 z` (mathlib Weierstrass.lean:527).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: eventually_derivWeierstrassP_ne_zero, key_eventuallyEq
- **Visibility**: public
- **Lines**: 49–51, proof ≈ 1 line
- **Notes**: one-line wrapper around a mathlib lemma.

### `lemma PeriodPair.iteratedDeriv_weierstrassPExcept_zero`
- **Type**: `(L : PeriodPair) (n : ℕ) : iteratedDeriv n ℘[L - (0 : ℂ)] 0 = if n = 0 then 0 else ((n + 1)! : ℂ) * L.G (n + 2)`
- **What**: The Taylor coefficients of `℘[L − 0]` at `0` are (up to factorials) the Eisenstein sums `G_{n+2}`.
- **How**: mathlib `L.iteratedDeriv_weierstrassPExcept_self 0` (Weierstrass.lean:775) plus `sumInvPow_zero` (`L.sumInvPow 0 = L.G`, :942) and `weierstrassPExcept_zero` via `simp`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: recursion, iteratedDeriv_eq_of_invariants
- **Visibility**: public
- **Lines**: 54–58, proof ≈ 2 lines
- **Notes**: two-line specialisation of mathlib; fine as a convenience lemma.

### `lemma PeriodPair.eventually_derivWeierstrassP_ne_zero`
- **Type**: `(L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ℘'[L] z ≠ 0`
- **What**: `℘'` has no zeros in a punctured neighbourhood of `0` (it blows up like `−2/z³`).
- **How**: `℘'[L − 0]` is continuous at `0` with value `0` (`derivWeierstrassPExcept_zero_zero`, Weierstrass.lean:421), so `‖℘'[L−0] z‖ < 1` near `0`; if `℘'[L] z = 0` then by `derivWeierstrassPExcept_zero_eq` `℘'[L−0] z = 2/z³`, whose norm is `> 1` when `‖z‖ < 1` (`pow_lt_one₀`, `div_lt_one`) — `linarith` contradiction.
- **Hypotheses**: none.
- **Uses from project**: derivWeierstrassPExcept_zero_eq
- **Used by**: eventually_deriv_derivWeierstrassP
- **Visibility**: public
- **Lines**: 63–78, proof ≈ 14 lines
- **Notes**: a manual `‖·‖ < 1` estimate; mathlib's `tendsto_cobounded_of_meromorphicOrderAt_neg` (Meromorphic/Order.lean:149) + `order_weierstrassP`-style order `−3` for `℘'` would give `∀ᶠ z in 𝓝[≠] 0, ℘'[L] z ≠ 0` directly via `meromorphicOrderAt_ne_top_iff_eventually_ne_zero` (Order.lean:137), but mathlib has no `order_derivWeierstrassP`.

### `lemma PeriodPair.eventually_deriv_derivWeierstrassP`
- **Type**: `(L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2`
- **What**: The second-order Weierstrass differential equation `℘'' = 6℘² − g₂/2`, on a punctured neighbourhood of `0`.
- **How**: Differentiate the germ identity `℘'² = 4℘³ − g₂℘ − g₃` (mathlib `L.derivWeierstrassP_sq`, Weierstrass.lean:1069, upgraded to `=ᶠ[𝓝 z]` via `isClosed_lattice.isOpen_compl.mem_nhds`) using `HasDerivAt.fun_pow`, `Filter.EventuallyEq.deriv_eq` and `deriv_weierstrassP` (simp, :588); cancel the factor `2℘'(z) ≠ 0` (`mul_left_cancel₀` with `eventually_derivWeierstrassP_ne_zero`); `linear_combination`.
- **Hypotheses**: none (statement is local at `0`, but the argument works at every non-lattice point where `℘' ≠ 0`).
- **Uses from project**: eventually_notMem_lattice, eventually_derivWeierstrassP_ne_zero
- **Used by**: key_eventuallyEq
- **Visibility**: public
- **Lines**: 81–101, proof ≈ 19 lines
- **Notes**: mathlib has no `℘''` equation at all (grepped `deriv_derivWeierstrassP`, `6 * ℘`, `g₂ / 2` in Weierstrass.lean: only `deriv_derivWeierstrassPExcept_self` at :834). Upstream candidate `PeriodPair.deriv_derivWeierstrassP (hz : z ∉ L.lattice) : deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2` (pointwise, off the lattice — the `℘' ≠ 0` restriction can be removed by the identity theorem / density).

### `lemma PeriodPair.key_eventuallyEq`
- **Type**: `(L : PeriodPair) : (fun z ↦ z ^ 2 * deriv ℘'[L - 0] z) =ᶠ[𝓝 0] fun z ↦ 6 * (z ^ 2 * (℘[L - 0] z * ℘[L - 0] z)) + 12 * ℘[L - 0] z - L.g₂ / 2 * z ^ 2`
- **What**: The pole-cleared second-derivative equation as a germ at `0`: multiplying `℘'' = 6℘² − g₂/2` by `z²` and substituting `℘ = f + 1/z²` (f = `℘[L−0]`) removes all poles, giving an identity between functions analytic at `0`.
- **How**: On `𝓝[≠] 0`: substitute `℘'[L−0] = ℘'[L] + 2/z³` (`derivWeierstrassPExcept_zero_eq`, as a `funext`), differentiate `2/z³` (`HasDerivAt.div` with `hasDerivAt_pow 3`, value `−6/z⁴`), use `eventually_deriv_derivWeierstrassP` and `weierstrassP_eq`; `field_simp; ring`. At `z = 0` both sides are `0` (`Filter.eventually_pure`); glue with `nhdsNE_sup_pure` (mathlib Topology/NhdsWithin.lean:289).
- **Hypotheses**: none.
- **Uses from project**: eventually_notMem_lattice, eventually_deriv_derivWeierstrassP, derivWeierstrassPExcept_zero_eq, weierstrassP_eq
- **Used by**: recursion
- **Visibility**: public
- **Lines**: 105–135, proof ≈ 28 lines
- **Notes**: `hEq : ℘'[L - 0] = fun w ↦ …` is a global `funext` rewrite of a function — fragile; the `h1`/`h2`/`nhdsNE_sup_pure` pattern (L109–135) is the generic "extend a `𝓝[≠]` germ identity to `𝓝` when both sides agree at the point" = mathlib `eventuallyEq_nhds_of_eventuallyEq_nhdsNE` (Topology/NhdsWithin.lean:432), which would replace L130–135. Name `key_eventuallyEq` is non-descriptive.

### `lemma PeriodPair.iteratedDeriv_sq_mul`
- **Type**: `(g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0) {n : ℕ} (hn : 2 ≤ n) : iteratedDeriv n (fun z ↦ z ^ 2 * g z) 0 = (n : ℂ) * ((n : ℂ) - 1) * iteratedDeriv (n - 2) g 0`
- **What**: Leibniz collapse: the `n`-th derivative at `0` of `z² g(z)` is `n(n−1)` times the `(n−2)`-nd derivative of `g`.
- **How**: General Leibniz rule `iteratedDeriv_fun_mul` (mathlib IteratedDeriv/Lemmas.lean:417, `to_fun` alias) gives a binomial sum; `iteratedDeriv_fun_pow_zero` (:429) kills every term except `i = 2` (`Finset.sum_eq_single_of_mem`); `Nat.cast_choose_two` (Data/Nat/Choose/Cast.lean:44) and `Nat.factorial_two`.
- **Hypotheses**: `g` analytic at `0`; `2 ≤ n`.
- **Uses from project**: []
- **Used by**: recursion (twice, L163 and L175)
- **Visibility**: public (declared inside `namespace PeriodPair` although it has nothing to do with `PeriodPair`; the section variable `L` is not included)
- **Lines**: 140–150, proof ≈ 8 lines
- **Notes**: general calculus lemma misplaced in `PeriodPair`; mathlib gap next to `iteratedDeriv_fun_pow_zero`. Natural generalisation: `iteratedDeriv n (fun z ↦ (z - x) ^ k * g z) x = (n.descFactorial k : 𝕜) * iteratedDeriv (n - k) g x` for `ContDiffAt` `g`, any `k ≤ n`, over any nontrivially normed field `𝕜` with a normed algebra target (only `iteratedDeriv_fun_mul` and `iteratedDeriv_fun_pow_zero` are used, neither needs `ℂ` or analyticity — `ContDiffAt 𝕜 n g x` suffices).

### `lemma PeriodPair.recursion`
- **Type**: `(L : PeriodPair) {n : ℕ} (hn : 3 ≤ n) : ((n : ℂ) * ((n : ℂ) - 1) - 12) * iteratedDeriv n ℘[L - 0] 0 = 6 * ((n : ℂ) * ((n : ℂ) - 1)) * ∑ k ∈ Finset.range (n - 1), ((n - 2).choose k : ℂ) * iteratedDeriv k ℘[L - 0] 0 * iteratedDeriv (n - 2 - k) ℘[L - 0] 0`
- **What**: The coefficient recursion: for `n ≥ 3` the `n`-th Taylor coefficient `a_n` of `℘[L−0]` at `0` satisfies `(n(n−1) − 12) a_n = 6 n(n−1) Σ_{k ≤ n−2} C(n−2,k) a_k a_{n−2−k}` — i.e. it is determined by lower coefficients (this is the classical `G_{2m}` recursion in derivative form).
- **How**: Take the `n`-th derivative at `0` of both sides of `key_eventuallyEq` (`Filter.EventuallyEq.iteratedDeriv_eq`, IteratedDeriv/Lemmas.lean:434). LHS: `iteratedDeriv_sq_mul` on `deriv ℘'[L−0]`, then `iteratedDeriv_succ'`, mathlib `iteratedDeriv_derivWeierstrassPExcept_self` (Weierstrass.lean:825) and `iteratedDeriv_weierstrassPExcept_zero` + `sumInvPow_zero` identify `iteratedDeriv (n−2) (deriv ℘'[L−0]) 0` with `a_n`. RHS: `iteratedDeriv_fun_sub/add`, `iteratedDeriv_const_mul_field` (×3), `iteratedDeriv_fun_pow_zero`, `iteratedDeriv_sq_mul` on `f·f`, Leibniz `iteratedDeriv_fun_mul` for `f·f`; `linear_combination`.
- **Hypotheses**: `3 ≤ n`.
- **Uses from project**: key_eventuallyEq, iteratedDeriv_sq_mul, iteratedDeriv_weierstrassPExcept_zero
- **Used by**: iteratedDeriv_eq_of_invariants
- **Visibility**: public
- **Lines**: 154–179, proof ≈ 25 lines
- **Notes**: name `recursion` flagged as SHORT collision in `_mathlib-collisions.tsv`; non-descriptive (mathlib style: `iteratedDeriv_weierstrassPExcept_zero_recurrence` or state it for `L.G` directly: `(n(n−1) − 12)(n+1)! G_{n+2} = …`). Depends on the exact syntactic shape of `key_eventuallyEq`'s RHS (the `6 * (z^2 * (f*f))` bracketing) for the `rw` chain to fire.

### `lemma PeriodPair.iteratedDeriv_eq_of_invariants`
- **Type**: `{L₁ L₂ : PeriodPair} (hg₂ : L₁.g₂ = L₂.g₂) (hg₃ : L₁.g₃ = L₂.g₃) (n : ℕ) : iteratedDeriv n ℘[L₁ - 0] 0 = iteratedDeriv n ℘[L₂ - 0] 0`
- **What**: Equal invariants force equal Taylor coefficients of `℘[L − 0]` at `0` in every degree.
- **How**: Strong induction (`Nat.strong_induction_on`). Base `n < 5` by `interval_cases`: degrees 0,1,3 vanish (`iteratedDeriv_weierstrassPExcept_zero`, `G_eq_zero_of_odd` Weierstrass.lean:945), degree 2 is `G₄ = g₂/60`, degree 4 is `G₆ = g₃/140` (unfold `g₂`, `g₃`; `mul_left_cancel₀`). Step `n ≥ 5`: `recursion` for both lattices, sums agree by IH (`Finset.sum_congr`), and the coefficient `n(n−1) − 12 ≠ 0` since `n(n−1) ≥ 20` (`Nat.mul_le_mul`, cast juggling with `Nat.cast_sub`).
- **Hypotheses**: `g₂` and `g₃` agree.
- **Uses from project**: iteratedDeriv_weierstrassPExcept_zero, recursion
- **Used by**: lattice_eq_of_g₂_eq_of_g₃_eq
- **Visibility**: public
- **Lines**: 183–224, proof ≈ 39 lines (>30)
- **Notes**: no docstring. The `hcoef` block (L216–222, 7 lines) proving `(n:ℂ)(n−1) − 12 ≠ 0` from `n(n−1) ≠ 12` is cast bookkeeping that `norm_cast`/`exact_mod_cast` on a `Nat`-level statement would shorten; `hG4`/`hG6` (L188–195) duplicate a 3-line skeleton — a lemma `g₂_eq_iff : L₁.g₂ = L₂.g₂ ↔ L₁.G 4 = L₂.G 4` (or `G_four_eq_of_g₂_eq`) is missing.

### `lemma PeriodPair.weierstrassP_eventuallyEq`
- **Type**: `{L₁ L₂ : PeriodPair} (h : ∀ n, iteratedDeriv n ℘[L₁ - 0] 0 = iteratedDeriv n ℘[L₂ - 0] 0) : ℘[L₁] =ᶠ[𝓝 (0 : ℂ)] ℘[L₂]`
- **What**: Equal Taylor coefficients at `0` give `℘[L₁] = ℘[L₂]` near `0` (both are `℘[L−0] + 1/z²`).
- **How**: mathlib `AnalyticAt.hasFPowerSeriesAt` (IteratedDeriv/Defs.lean:339) exhibits `℘[Lᵢ−0]` as the sum of `ofScalars (iteratedDeriv n f 0 / n!)`; after `simp_rw [h]` both series coincide, so `HasFPowerSeriesAt.eventually_hasSum_sub` (Analytic/Basic.lean:326) + `HasSum.unique` give local equality; add `1/z²` back with `weierstrassP_eq`.
- **Hypotheses**: all iterated derivatives at `0` agree.
- **Uses from project**: weierstrassP_eq
- **Used by**: lattice_eq_of_g₂_eq_of_g₃_eq
- **Visibility**: public
- **Lines**: 228–235, proof ≈ 6 lines
- **Notes**: no docstring. The core (L231–235) is the general "two functions analytic at `x` with equal `iteratedDeriv` at `x` agree on `𝓝 x`" — no such lemma in mathlib (grepped `eventuallyEq_of_iteratedDeriv`, `eq_of_iteratedDeriv`, `Analysis/Analytic/Uniqueness.lean` has no `iteratedDeriv`): upstream candidate `AnalyticAt.eventuallyEq_of_iteratedDeriv_eq`.

### `lemma PeriodPair.eqOn_weierstrassP`
- **Type**: `{L₁ L₂ : PeriodPair} (hev : ℘[L₁] =ᶠ[𝓝 (0 : ℂ)] ℘[L₂]) : Set.EqOn ℘[L₁] ℘[L₂] ((L₁.lattice : Set ℂ) ∪ (L₂.lattice : Set ℂ))ᶜ`
- **What**: Identity theorem: local agreement at `0` propagates to agreement everywhere off both lattices.
- **How**: Each lattice is countable (`countable_of_Lindelof_of_discrete`, Topology/Compactness/Lindelof.lean:571, via the `DiscreteTopology L.lattice` instance), so the complement of the union is connected (`Set.Countable.isConnected_compl_of_one_lt_rank`, Analysis/Normed/Module/Connected.lean:115) and dense (`Set.Countable.dense_compl`); pick `z₀` in the complement inside the open set `U ∋ 0` where the functions agree (`mem_nhds_iff`, `Dense.exists_mem_open`), then `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` with mathlib `analyticOnNhd_weierstrassP` (Weierstrass.lean:893).
- **Hypotheses**: `℘[L₁] =ᶠ[𝓝 0] ℘[L₂]`.
- **Uses from project**: []
- **Used by**: lattice_eq_of_g₂_eq_of_g₃_eq
- **Visibility**: public
- **Lines**: 237–254, proof ≈ 17 lines
- **Notes**: no docstring. The countable-complement-connected argument (L239–245) is copied from mathlib's own private proof at Weierstrass.lean:441–442; a public `PeriodPair.countable_lattice` / `isConnected_compl_lattice` in mathlib would collapse it. The detour through `z₀ ∈ U` (L246–250) exists only because `0 ∈ L₁.lattice` is not in the connected set; `IsPreconnected.eqOn_of_eventuallyEq`-style lemmas require the base point inside.

### `lemma PeriodPair.lattice_le_of_eqOn`
- **Type**: `{L₁ L₂ : PeriodPair} (h : Set.EqOn ℘[L₁] ℘[L₂] ((L₁.lattice : Set ℂ) ∪ (L₂.lattice : Set ℂ))ᶜ) : L₁.lattice ≤ L₂.lattice`
- **What**: The lattice is the polar set of `℘`: if `℘[L₁] = ℘[L₂]` off both lattices, every point of `L₁` is a point of `L₂`.
- **How**: For `x ∈ L₁ \ L₂` the two functions agree on `𝓝[≠] x` (open complement of `L₂` + `compl_lattice_diff_singleton_mem_nhds`), so `meromorphicOrderAt_congr` (Meromorphic/Order.lean:261) transfers the order; mathlib `order_weierstrassP` (Weierstrass.lean:915) gives `−2` for `L₁`, while `℘[L₂]` is analytic at `x` (`analyticOnNhd_weierstrassP`) so its order is `≥ 0` (`AnalyticAt.meromorphicOrderAt_nonneg`, Order.lean:291); `decide` refutes `0 ≤ −2` in `WithTop ℤ`.
- **Hypotheses**: pointwise agreement off the union of lattices.
- **Uses from project**: []
- **Used by**: lattice_eq_of_g₂_eq_of_g₃_eq (twice)
- **Visibility**: public
- **Lines**: 256–276, proof ≈ 20 lines
- **Notes**: no docstring. The underlying fact `x ∈ L.lattice ↔ meromorphicOrderAt ℘[L] x < 0` is a clean mathlib-level characterisation absent from mathlib (it has only the `∈` direction `order_weierstrassP`).

### `theorem PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq`
- **Type**: `{L₁ L₂ : PeriodPair} (hg₂ : L₁.g₂ = L₂.g₂) (hg₃ : L₁.g₃ = L₂.g₃) : L₁.lattice = L₂.lattice`
- **What**: **Uniqueness theorem**: a period lattice is determined by its invariants `g₂`, `g₃`.
- **How**: Chain `iteratedDeriv_eq_of_invariants → weierstrassP_eventuallyEq → eqOn_weierstrassP`, then `lattice_le_of_eqOn` in both directions (`Set.union_comm`, symmetrised `EqOn`) and `le_antisymm`.
- **Hypotheses**: equal `g₂`, equal `g₃`.
- **Uses from project**: eqOn_weierstrassP, weierstrassP_eventuallyEq, iteratedDeriv_eq_of_invariants, lattice_le_of_eqOn
- **Used by**: invariantsDetermineLattice; externally LatticeJ.lean:328, 346, 380
- **Visibility**: public
- **Lines**: 282–288, proof ≈ 5 lines
- **Notes**: the file's deliverable; mathlib has nothing like it (grepped `lattice_eq`, `invariants`, `uniqueness`, `g₂_eq`, `determine` in `Mathlib/Analysis/SpecialFunctions/Elliptic/`).

### `theorem PeriodPair.invariantsDetermineLattice`
- **Type**: `∀ L₁ L₂ : PeriodPair, L₁.g₂ = L₂.g₂ → L₁.g₃ = L₂.g₃ → L₁.lattice = L₂.lattice`
- **What**: `∀`-quantified restatement of the previous theorem.
- **How**: `fun _ _ => lattice_eq_of_g₂_eq_of_g₃_eq`.
- **Hypotheses**: none (universally quantified).
- **Uses from project**: lattice_eq_of_g₂_eq_of_g₃_eq
- **Used by**: unused in file; unused anywhere in the project (grep: 0 external references)
- **Visibility**: public
- **Lines**: 291–293, proof ≈ 1 line
- **Notes**: docstring says "in the form of `InvariantsDetermineLattice` from `talk4.lean`" — `talk4.lean` does not exist in the repo (find: nothing); stale reference. Junk candidate.

## File Summary
- Total declarations: 15 (0 defs, 15 lemmas/theorems, 0 instances, 1 other = local attribute)
- Key API (used by 3+ others in the file): none reaches 3 — the file is a linear chain; `eventually_notMem_lattice`, `weierstrassP_eq`, `derivWeierstrassPExcept_zero_eq`, `iteratedDeriv_weierstrassPExcept_zero` each have 2 users
- Unused declarations (not used by anything in this file): `invariantsDetermineLattice` (also 0 external users); `lattice_eq_of_g₂_eq_of_g₃_eq` is used only by it in-file but has 3 external users in LatticeJ.lean
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `iteratedDeriv_eq_of_invariants` (≈39)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- Whole file is a natural upstream PR into `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` (namespace `PeriodPair`, 1075 lines, pinned rev): mathlib already has `derivWeierstrassP_sq` (:1069), `iteratedDeriv_weierstrassPExcept_self` (:775), `iteratedDeriv_derivWeierstrassPExcept_self` (:825), `order_weierstrassP` (:915), `G`/`g₂`/`g₃` (:939–954), `G_eq_zero_of_odd` (:945), `meromorphic_weierstrassP` (:902) but NO second-derivative equation, NO coefficient recursion, NO uniqueness theorem (grep-verified: `deriv_derivWeierstrassP`, `lattice_eq`, `invariants`, `g₂_eq`, `uniqueness` absent). The mathlib file even carries a `TODO: Establish connections with the ModularForm library` at :938 — this file plus LatticeJ.lean is that connection.
- `iteratedDeriv_sq_mul` (L140–150): general Leibniz collapse, belongs beside mathlib `iteratedDeriv_fun_pow_zero` (Analysis/Calculus/IteratedDeriv/Lemmas.lean:429); no mathlib analogue found (searched `iteratedDeriv_pow_mul`, `iteratedDeriv_mul_pow`, `iteratedDeriv_sq_mul`, `iteratedDeriv_id_pow_mul`).
- `weierstrassP_eventuallyEq` L231–235: "analytic functions with equal `iteratedDeriv` at `x` are `=ᶠ[𝓝 x]`" via `AnalyticAt.hasFPowerSeriesAt` (IteratedDeriv/Defs.lean:339) + `HasFPowerSeriesAt.eventually_hasSum_sub` (Analytic/Basic.lean:326) — no mathlib lemma (searched `eventuallyEq_of_iteratedDeriv`, `eq_of_iteratedDeriv`, `eq_of_forall_iteratedDeriv`); upstream candidate `AnalyticAt.eventuallyEq_of_iteratedDeriv_eq`.
- `key_eventuallyEq` L130–135 (`Filter.eventually_pure` + `Filter.eventually_sup` + `nhdsNE_sup_pure`) is exactly mathlib `eventuallyEq_nhds_of_eventuallyEq_nhdsNE` (Topology/NhdsWithin.lean:432); replace 6 lines with one call.
- `eqOn_weierstrassP` L239–245 duplicates mathlib's private argument at Weierstrass.lean:441–442 (`Set.Countable.isConnected_compl_of_one_lt_rank` + `countable_of_Lindelof_of_discrete`); a public `PeriodPair.countable_lattice`/`isConnected_compl_lattice` is the missing mathlib lemma.
- `eventually_derivWeierstrassP_ne_zero` L63–78 is a hand-rolled norm estimate standing in for `meromorphicOrderAt_ne_top_iff_eventually_ne_zero` (Meromorphic/Order.lean:137) applied to `℘'` — would need mathlib `order_derivWeierstrassP = -3` (absent; mathlib has `meromorphic_derivWeierstrassP` :911 only).
- `lattice_le_of_eqOn` L272–276: characterisation "`x ∈ L.lattice ↔ meromorphicOrderAt ℘[L] x < 0`" is absent from mathlib (only `order_weierstrassP`, the `→` direction); upstream candidate `PeriodPair.mem_lattice_iff_meromorphicOrderAt_neg`.
### Missing API / repeated patterns
- `hG4`/`hG6` (L188–195): the same 3-line `simp only [g₂] at h; exact mul_left_cancel₀ (by norm_num) h` twice → `PeriodPair.G_four_eq_of_g₂_eq` / `G_six_eq_of_g₃_eq` (or `g₂_inj`-style `g₂ = g₂ ↔ G 4 = G 4`).
- Cast bookkeeping `hcoef` L216–222 (7 lines) for `(n:ℂ)*((n:ℂ)-1) - 12 ≠ 0` — a `Nat.cast_pred`/`push_cast`-free path: state `recursion` with the integer coefficient `((n * (n - 1) - 12 : ℕ) : ℂ)` or with `n.descFactorial 2`.
- No `@[simp]` tags anywhere; `weierstrassP_eq`, `derivWeierstrassPExcept_zero_eq`, `iteratedDeriv_weierstrassPExcept_zero` are all natural `simp` lemmas (the latter mirrors mathlib's `iteratedDeriv_weierstrassPExcept_self`, which is also un-simp'd).
- The file lacks the pointwise form `deriv ℘'[L] z = 6 ℘[L] z ^ 2 - g₂/2` for `z ∉ L.lattice` (only the `𝓝[≠] 0` germ, L81–101); the pointwise version is what a mathlib user would want and follows from the same proof with `hz'` replaced by density of `{℘' ≠ 0}`.
### Junk candidates
- `invariantsDetermineLattice` (L290–293): unused anywhere (grep), docstring refers to nonexistent `talk4.lean`.
- `derivWeierstrassPExcept_zero_eq` (L49–51) is a one-line `simpa` wrapper around mathlib `derivWeierstrassPExcept_def`.
- Header (L1–18) is a plain `/- -/` comment placed BEFORE the `import`s rather than a `/-! -/` module docstring after them; no copyright header (every other XYin file has the `Copyright (c) 2026 … Apache 2.0` block); missing docstrings on `iteratedDeriv_eq_of_invariants`, `weierstrassP_eventuallyEq`, `eqOn_weierstrassP`, `lattice_le_of_eqOn`.
- Import `Mathlib.Topology.Algebra.Module.Cardinality` (L21): nothing from it is visibly used (`countable_of_Lindelof_of_discrete` lives in Topology/Compactness/Lindelof.lean, `isConnected_compl_of_one_lt_rank` in Analysis/Normed/Module/Connected.lean, both reachable from the Weierstrass import) — likely stale.
### Moral duplicates within this batch
- `key_eventuallyEq` L130–135 vs mathlib `eventuallyEq_nhds_of_eventuallyEq_nhdsNE`; also vs LaurentQExpansion.lean `analyticAt_cuspFunction_of_eventuallyEq` (L353–357) and Algebra.lean `cuspFunction_qpow_mul_eventuallyEq` (L66–67), which both use the mathlib lemma — three "extend `𝓝[≠]` germ to `𝓝`" sites in this batch, one hand-rolled.
- `eqOn_weierstrassP` connected-complement argument vs mathlib Weierstrass.lean:441.
### Generalization notes
- `iteratedDeriv_sq_mul`: stated for `ℂ` and `AnalyticAt`; proof uses only `iteratedDeriv_fun_mul` and `iteratedDeriv_fun_pow_zero`, so it holds for any `𝕜` nontrivially normed field, `g : 𝕜 → A` into a normed `𝕜`-algebra, with `ContDiffAt 𝕜 n g 0` (or `⊤`), and for any base point `x` with `(z - x)^k`.
- `eventually_deriv_derivWeierstrassP` / `key_eventuallyEq`: nothing about `0` is used except `weierstrassP_eq` at `0`; the same argument at any lattice point `l` (with `℘[L − l]`, `weierstrassPExcept_add`) gives the Laurent recursion at every pole — irrelevant for uniqueness but the natural mathlib statement.
- `weierstrassP_eventuallyEq`, `eqOn_weierstrassP`, `lattice_le_of_eqOn` never use `g₂`/`g₃`; they are statements about arbitrary pairs of period pairs and could be stated as `EqOn`/`≤` lemmas for `PeriodPair` in general (they are).
