# Inventory: XYin/PhD/ModularFunctions/CuspGrowth.lean  (114 lines)

Defines the period-free growth predicate `UpperHalfPlane.IsOfExponentialGrowth f` (some weight `exp(-ρ·im τ)` makes `f` bounded at `atImInfty`) and proves that, for an `h`-periodic function holomorphic high in ℍ, it is equivalent to meromorphy of mathlib's `cuspFunction h f` at `q = 0`. This is the analytic core behind the `bdd_at_cusps'` field of `ModularFunction`.

## Declarations

### `def UpperHalfPlane.IsOfExponentialGrowth`
- **Type**: `(f : ℍ → ℂ) : Prop := ∃ ρ : ℝ, 0 ≤ ρ ∧ IsBoundedAtImInfty (fun τ ↦ (Real.exp (-ρ * τ.im) : ℂ) * f τ)`
- **What**: `f` is `O(exp(ρ·im τ))` as `im τ → ∞` for some `ρ ≥ 0`.
- **How**: definition on top of mathlib's `IsBoundedAtImInfty` (`= BoundedAtFilter atImInfty = (· =O[atImInfty] 1)`).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `isOfExponentialGrowth_of_meromorphicAt_cuspFunction`, `isOfExponentialGrowth_iff_meromorphicAt_cuspFunction`
- **Visibility**: public
- **Lines**: 24–28
- **Notes**: no mathlib analogue (searched `IsOfExponentialGrowth`, `ExponentialGrowth`, `expGrowth` — mathlib's `Mathlib/Analysis/Asymptotics/ExpGrowth.lean` is about sequences). Equivalent `IsBigO` form: `∃ ρ ≥ 0, f =O[atImInfty] fun τ ↦ Real.exp (ρ * τ.im)` (typechecks; scratch-checked). Used by GrowthAtCusp, Cusps, JInvariant, Congruence, Cox/ModularPolynomial/Construction.

### `lemma UpperHalfPlane.norm_qParam_pow` (private)
- **Type**: `(h : ℝ) (n : ℕ) (τ : ℍ) : ‖Periodic.qParam h τ ^ n‖ = Real.exp (-(2 * π * n / h) * τ.im)`
- **What**: norm of a power of the q-parameter.
- **How**: `norm_pow`, mathlib `Periodic.norm_qParam`, `Real.exp_nat_mul`, `ring`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `weighted_bound_iff`, `isOfExponentialGrowth_iff_meromorphicAt_cuspFunction`
- **Visibility**: private
- **Lines**: 30–35, proof body ≈ 4 lines
- **Notes**: —

### `lemma UpperHalfPlane.weighted_bound_iff` (private)
- **Type**: `(h : ℝ) (n : ℕ) (f : ℍ → ℂ) : IsBoundedAtImInfty (fun τ ↦ (exp (-(2πn/h) τ.im) : ℂ) * f τ) ↔ IsBoundedAtImInfty (fun τ ↦ Periodic.qParam h τ ^ n * f τ)`
- **What**: the exponential weight `exp(-2πn·im/h)` and the weight `q^n` give the same boundedness condition.
- **How**: unfold `isBoundedAtImInfty_iff`, `norm_mul`, `norm_qParam_pow`, `Complex.norm_real`, `abs_of_pos (exp_pos _)`.
- **Hypotheses**: none.
- **Uses from project**: `norm_qParam_pow`
- **Used by**: `isOfExponentialGrowth_of_meromorphicAt_cuspFunction`
- **Visibility**: private
- **Lines**: 37–41, proof body ≈ 2 lines
- **Notes**: —

### `lemma UpperHalfPlane.meromorphicAt_zero_of_bounded_pow` (private)
- **Type**: `{g : ℂ → ℂ} (n : ℕ) (hd : ∀ᶠ q in 𝓝[≠] 0, DifferentiableAt ℂ g q) (hb : BoundedAtFilter (𝓝[≠] 0) (fun q ↦ q ^ n * g q)) : MeromorphicAt g 0`
- **What**: a function differentiable on a punctured neighbourhood of 0 with `q^n g` bounded near 0 is meromorphic at 0 (pole order ≤ n+1).
- **How**: `q^(n+1) g → 0` (`ZeroAtFilter.mul_boundedAtFilter`), so `q^(n+1) g` extends continuously; Riemann removable singularity `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` + `continuousAt_iff_punctured_nhds` gives `AnalyticAt` of `q^(n+1) g`, i.e. `MeromorphicAt g 0` with witness `n+1`.
- **Hypotheses**: as stated.
- **Uses from project**: []
- **Used by**: `isOfExponentialGrowth_iff_meromorphicAt_cuspFunction`
- **Visibility**: private
- **Lines**: 43–56, proof body ≈ 11 lines
- **Notes**: general and reusable; no mathlib analogue found (searched `bounded|isBigO` in `Mathlib/Analysis/Meromorphic/{Basic,Order,NormalForm}.lean`; only `tendsto_cobounded_*` order lemmas). Stated only at `0`; holds at any `x : ℂ`.

### `lemma UpperHalfPlane.bounded_pow_cuspFunction` (private)
- **Type**: `{h} (hh : 0 < h) {f} (n : ℕ) (hb : IsBoundedAtImInfty (fun τ ↦ qParam h τ ^ n * f τ)) : BoundedAtFilter (𝓝[≠] 0) (fun q ↦ q ^ n * cuspFunction h f q)`
- **What**: a `q^n`-weighted bound at `im → ∞` transfers to a bound of `q^n · cuspFunction` near `q = 0`.
- **How**: compose the bound with `tendsto_comap_im_ofComplex ∘ Periodic.invQParam_tendsto` and rewrite on `𝓝[≠] 0` using `im_invQParam_pos_of_norm_lt_one`, `ofComplex_apply_of_im_pos`, `cuspFunction_eq_of_nonzero`, `qParam_right_inv`.
- **Hypotheses**: `h > 0`.
- **Uses from project**: []
- **Used by**: `isOfExponentialGrowth_iff_meromorphicAt_cuspFunction`
- **Visibility**: private
- **Lines**: 58–70, proof body ≈ 11 lines
- **Notes**: the `n = 0` case is mathlib's `Function.Periodic.boundedAtFilter_cuspFunction` (`Mathlib/Analysis/Complex/Periodic.lean:192`); the general case follows by applying it to `𝕢^n · f`, since `q^n · cuspFunction h f q = cuspFunction h (𝕢^n · f) q` for `q ≠ 0`.

### `theorem UpperHalfPlane.isOfExponentialGrowth_of_meromorphicAt_cuspFunction`
- **Type**: `{h} (hh : 0 < h) {f} (hfper : Periodic (f ∘ ofComplex) h) (hf : MeromorphicAt (cuspFunction h f) 0) : IsOfExponentialGrowth f`
- **What**: meromorphy of the cusp function at 0 gives exponential growth with `ρ = 2πn/h`, `n` the pole-order witness.
- **How**: `q^n · cuspFunction` is analytic hence continuous at 0, so bounded along `qParam_tendsto_atImInfty` (`Tendsto.isBigO_one`); rewrite with `eq_cuspFunction` and `weighted_bound_iff`.
- **Hypotheses**: `h > 0`, `f` `h`-periodic.
- **Uses from project**: `IsOfExponentialGrowth`, `weighted_bound_iff`
- **Used by**: `isOfExponentialGrowth_iff_meromorphicAt_cuspFunction`
- **Visibility**: public
- **Lines**: 72–81, proof body ≈ 6 lines
- **Notes**: used by Cusps, JInvariant, Congruence, Cox/ModularPolynomial/Construction.

### `theorem UpperHalfPlane.isOfExponentialGrowth_iff_meromorphicAt_cuspFunction`
- **Type**: `{h} (hh : 0 < h) {f} (hfper : Periodic (f ∘ ofComplex) h) (hfhol : ∀ᶠ τ in atImInfty, MDiffAt f τ) : IsOfExponentialGrowth f ↔ MeromorphicAt (cuspFunction h f) 0`
- **What**: for periodic functions holomorphic high in ℍ, exponential growth ⇔ meromorphy of the cusp function at 0.
- **How**: (←) previous theorem. (→) choose `n > ρh/2π` (`exists_nat_gt`), dominate `exp(-ρ im)` by `exp(-2πn im/h)` (manual `isBoundedAtImInfty_iff` unfolding, `Real.exp_le_exp`), transfer holomorphy to `comap im atTop` (`tendsto_comap_im_ofComplex`, `mdifferentiableAt_iff`), then `Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero` + `bounded_pow_cuspFunction` + `meromorphicAt_zero_of_bounded_pow`.
- **Hypotheses**: `h > 0`, periodicity, eventual holomorphy at `atImInfty`.
- **Uses from project**: `IsOfExponentialGrowth`, `isOfExponentialGrowth_of_meromorphicAt_cuspFunction`, `norm_qParam_pow`, `meromorphicAt_zero_of_bounded_pow`, `bounded_pow_cuspFunction`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 83–112, proof body ≈ 24 lines
- **Notes**: used by Cusps.lean:31. Lines 96–104 are a manual `∃ M A, ∀ τ, A ≤ im τ → ‖·‖ ≤ M` comparison that is `IsBigO.trans`/`IsBigO.of_norm_le` in `IsBigO` form.

## File Summary
- Total declarations: 7 (1 def, 6 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): none (`IsOfExponentialGrowth` used by 2, `norm_qParam_pow` by 2)
- Unused declarations (not used by anything in this file): `isOfExponentialGrowth_iff_meromorphicAt_cuspFunction` (used by Cusps.lean)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest `isOfExponentialGrowth_iff_meromorphicAt_cuspFunction` ≈ 24)

## Observations
### Mathlib API candidates
- Growth predicate (question c): `IsOfExponentialGrowth` is NOT a raw `∃ C ρ, ∀ z, …` — it is built on `IsBoundedAtImInfty` (`Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean:46`), which is `BoundedAtFilter atImInfty` = `f =O[atImInfty] 1` (`Mathlib/Order/Filter/ZeroAndBoundedAtFilter.lean:75`). The API-rich form `∃ ρ ≥ 0, f =O[atImInfty] (fun τ ↦ Real.exp (ρ * τ.im))` is equivalent and would turn `IsOfExponentialGrowth.slash` (GrowthAtCusp.lean:24–42) and the comparison at 96–104 into `IsBigO.comp_tendsto`/`IsBigO.mul`/`IsBigO.trans` one-liners; the project's own BigO.lean (Modularforms) contains only `cofinite` lattice-sum big-O lemmas, nothing for `atImInfty`.
- `bounded_pow_cuspFunction` (58) ⊂ `Function.Periodic.boundedAtFilter_cuspFunction` (`Mathlib/Analysis/Complex/Periodic.lean:192`) applied to `𝕢^n · f` (needs `tendsto_comap_im_ofComplex`, `FunctionsBoundedAtInfty.lean:78`, to move between `atImInfty` on ℍ and `I∞` on ℂ).
- `meromorphicAt_zero_of_bounded_pow` (43): mathlib candidate `MeromorphicAt.of_boundedAtFilter_pow` (bounded `(z-x)^n • g` + differentiable on `𝓝[≠] x` ⇒ `MeromorphicAt g x`); ingredients `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` (`Mathlib/Analysis/Complex/RemovableSingularity.lean:36`), `ZeroAtFilter.mul_boundedAtFilter` (`ZeroAndBoundedAtFilter.lean:107`).
- `isOfExponentialGrowth_of_meromorphicAt_cuspFunction` correctly uses `Filter.Tendsto.isBigO_one` (`Mathlib/Analysis/Asymptotics/Lemmas.lean:111`), `qParam_tendsto_atImInfty` (`QExpansion.lean:67`), `eq_cuspFunction` (`QExpansion.lean:79`).
### Missing API / repeated patterns
- No companions for `IsOfExponentialGrowth`: `.add`, `.mul`, `.neg`, `.const`, `.smul`, `.of_isBoundedAtImInfty` (ρ = 0), `.mono` (enlarge ρ), `.congr`. Cox files construct modular functions by hand because of this.
- Manual `isBoundedAtImInfty_iff` unfolding (96–104) recurs in GrowthAtCusp.lean:36–42 and NormalFormGrowth.lean:43–64: a lemma `IsBoundedAtImInfty.of_norm_le_of_eventually` or the `IsBigO` reformulation removes all three.
### Junk candidates
- none (all privates are used).
### Moral duplicates within this batch
- `weighted_bound_iff` (37) and the inline comparison at 96–104 both convert `exp(-ρ im)`-weights to `q^n`-weights; a single `IsOfExponentialGrowth ↔ ∃ n, IsBoundedAtImInfty (𝕢^n · f)` lemma would subsume both and shorten the main theorem.
### Generalization notes
- `meromorphicAt_zero_of_bounded_pow` holds at any `x : ℂ` (translate) and for `g : ℂ → E` with `E` complete (`analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` is stated for `f : ℂ → E`).
- `IsOfExponentialGrowth` could be defined for `f : ℍ → E` with any normed `E`; nothing in the file uses ℂ-valuedness except `cuspFunction` (which is ℂ → ℂ).
