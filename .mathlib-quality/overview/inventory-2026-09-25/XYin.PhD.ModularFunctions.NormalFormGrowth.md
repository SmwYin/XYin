# Inventory: XYin/PhD/ModularFunctions/NormalFormGrowth.lean  (66 lines)

Two lemmas: a meromorphic function in normal form that is locally bounded at a point is analytic there, and hence an exponential bound on a normal-form function on ℍ excludes poles sufficiently high in the half-plane (`∀ᶠ τ in atImInfty, MDiffAt f τ`). Supplies the holomorphy hypothesis of `isOfExponentialGrowth_iff_meromorphicAt_cuspFunction` for modular functions (Cusps.lean).

## Declarations

### `lemma MeromorphicNFAt.analyticAt_of_eventually_norm_le`
- **Type**: `{f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicNFAt f x) (hbound : ∃ C : ℝ, ∀ᶠ z in 𝓝 x, ‖f z‖ ≤ C) : AnalyticAt ℂ f x`
- **What**: locally bounded normal-form meromorphic functions are analytic (no pole).
- **How**: mathlib `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`; if the order were negative, `tendsto_cobounded_of_meromorphicOrderAt_neg` + `tendsto_norm_atTop_iff_cobounded` contradict the bound on `𝓝[≠] x`.
- **Hypotheses**: `f` in normal form at `x`; `‖f‖ ≤ C` near `x`.
- **Uses from project**: []
- **Used by**: `eventually_mdifferentiableAt_of_meromorphicNFOn_of_exponential_bound`
- **Visibility**: public
- **Lines**: 21–32, proof body ≈ 9 lines
- **Notes**: no mathlib analogue (searched `bounded|norm_le|isBigO` in `Mathlib/Analysis/Meromorphic/NormalForm.lean`, `Order.lean`, `Basic.lean`); ingredients at `NormalForm.lean:114`, `Order.lean:149`, `Mathlib/Analysis/Normed/Group/Bounded.lean:45–46`. Hypothesis is `BoundedAtFilter (𝓝 x) f`/`IsBoundedUnder` in disguise. Upstream candidate.

### `lemma UpperHalfPlane.eventually_mdifferentiableAt_of_meromorphicNFOn_of_exponential_bound`
- **Type**: `{f : ℍ → ℂ} (hf : MeromorphicNFOn (f ∘ ofComplex) {z : ℂ | 0 < z.im}) (hbound : ∃ ρ : ℝ, 0 ≤ ρ ∧ IsBoundedAtImInfty (fun τ ↦ (Real.exp (-ρ * τ.im) : ℂ) * f τ)) : ∀ᶠ τ in atImInfty, MDiffAt f τ`
- **What**: a normal-form function with an exponential bound is holomorphic on a half-plane `im τ > A + 1`.
- **How**: unfold `isBoundedAtImInfty_iff` to `M, A`; on `im τ > A + 1` the bound `‖f z‖ ≤ M / exp(-ρ im z)` holds on a neighbourhood (three `ContinuousAt.eventually_lt` facts), so `MeromorphicNFAt.analyticAt_of_eventually_norm_le` gives analyticity, then `mdifferentiableAt_iff`.
- **Hypotheses**: normal form on ℍ; exponential bound (the unfolded `IsOfExponentialGrowth f`).
- **Uses from project**: `MeromorphicNFAt.analyticAt_of_eventually_norm_le`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 36–64, proof body ≈ 27 lines
- **Notes**: used by Cusps.lean:32. `hbound` restates `IsOfExponentialGrowth f` verbatim because the file does not import CuspGrowth.lean. Uses `{z : ℂ | 0 < z.im}` instead of `upperHalfPlaneSet` (defeq; inconsistent spelling within the folder). Hand-written continuity proof at 50–53 (`fun_prop` would do).

## File Summary
- Total declarations: 2 (0 defs, 2 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): none
- Unused declarations (not used by anything in this file): `eventually_mdifferentiableAt_of_meromorphicNFOn_of_exponential_bound` (used by Cusps.lean)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest ≈ 27)

## Observations
### Mathlib API candidates
- `MeromorphicNFAt.analyticAt_of_eventually_norm_le` (21): strong upstream candidate for `Mathlib/Analysis/Meromorphic/NormalForm.lean`, ideally stated with `BoundedAtFilter (𝓝 x) f` (`Mathlib/Order/Filter/ZeroAndBoundedAtFilter.lean:75`) and combined with `tendsto_cobounded_iff_meromorphicOrderAt_neg` (`Order.lean:211`).
- Second lemma: manual `∃ M A` unfolding (43–45, 58–64) and manual `ContinuousAt` construction (50–53); with the `IsBigO` form of the growth predicate and `fun_prop`, this shrinks to ≈ 10 lines.
### Missing API / repeated patterns
- Restated growth definition at 39–40 (moral copy of CuspGrowth.lean:26–28): import order should be fixed so the lemma takes `IsOfExponentialGrowth f`.
- The `‖exp(-ρ·im) · f‖ = exp(-ρ·im) · ‖f‖` normalisation (61–63) recurs in CuspGrowth.lean:40–41, 100–101 and GrowthAtCusp.lean:40–41: a `@[simp]` lemma `norm_exp_neg_mul_im_mul` would collapse the four copies.
### Junk candidates
- none.
### Moral duplicates within this batch
- `hbound` ≡ `IsOfExponentialGrowth f` (CuspGrowth.lean:26).
### Generalization notes
- `analyticAt_of_eventually_norm_le` holds for `f : 𝕜 → E` over any `NontriviallyNormedField 𝕜`, complete `E` (the two mathlib ingredients are stated in that generality); ℂ → ℂ is an unnecessary specialisation.
