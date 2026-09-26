# Inventory: XYin/PhD/Cox/ModularFunction.lean  (439 lines)

Cox Lemma 11.10 and Theorem 11.9(i): a level-one modular function holomorphic on ℍ is a polynomial in `j` (strong induction on the pole order at ∞, subtracting `a·j^m`), and pole-clearing on a truncated fundamental domain shows every level-one modular function is rational in `j`. Public entry points take the bundled `ModularFunction 𝒮ℒ`; all working lemmas are stated on the raw `LevelOneCuspData` predicate. Imports `LatticeJ` (for nothing used here except transitively) and `ModularFunction.LevelJ`.

## Declarations

### `private theorem Cox.levelOne_constant_of_holomorphic`
- **Type**: `{f : ℍ → ℂ} (hf : LevelOneCuspData f) (hfH : MDiff f) (hf_cusp : AnalyticAt ℂ (cuspFunction 1 f) 0) : ∃ c : ℂ, f = fun _ ↦ c`
- **What**: Cox Lemma 11.10(i): a level-one modular function holomorphic on ℍ and at ∞ is constant.
- **How**: Packages `f` as a weight-0 `ModularForm (mapGL ℝ).range` (boundedness at ∞ from `hf_cusp.continuousAt.tendsto.comp qParam_tendsto_atImInfty` then `Tendsto.isBigO_one`; boundedness at other cusps via `OnePoint.isBoundedAt_iff_exists_SL2Z` + `isCusp_SL2Z_iff'` and SL₂-invariance) and applies mathlib `ModularFormClass.levelOne_weight_zero_const`.
- **Hypotheses**: `f` has level-one cusp data (meromorphic on ℍ, Γ₀(1)-invariant, cusp-meromorphic), is holomorphic on ℍ, and its width-1 cusp function is analytic at 0.
- **Uses from project**: `LevelOneCuspData`, `periodic_comp_sl2`, `UpperHalfPlane.cuspFunction` (mathlib), `CuspData` projection `hf.2.1`
- **Used by**: `CuspData.polynomialInJ_of_holomorphic`
- **Visibility**: private
- **Lines**: 30–61, proof body ≈ 28 lines
- **Notes**: Docstring present. Builds a full `ModularForm` structure inline (lines 50–60) just to invoke one mathlib lemma.

### `private lemma Cox.cuspFunction_sub_const_mul_pow_eventuallyEq`
- **Type**: `(h : ℝ) (f g : ℍ → ℂ) (a : ℂ) (m : ℕ) : cuspFunction h (fun τ ↦ f τ - a * g τ ^ m) =ᶠ[nhdsWithin 0 {0}ᶜ] fun q ↦ cuspFunction h f q - a * cuspFunction h g q ^ m`
- **What**: Away from `q = 0`, the cusp function of `f - a·g^m` is the same expression in the cusp functions of `f` and `g`.
- **How**: `filter_upwards [self_mem_nhdsWithin]`, unfold and rewrite with `Periodic.cuspFunction_eq_of_nonzero` three times, `rfl`.
- **Hypotheses**: none (pure algebra of the definition off `q = 0`).
- **Uses from project**: `[]`
- **Used by**: `cuspData_sub_const_mul_pow`, `exists_const_poleOrder_sub_mul_pow_lt`
- **Visibility**: private
- **Lines**: 63–73, proof body ≈ 7 lines
- **Notes**: Same skeleton as `CuspData.lean:86` (`cuspFunction_mul_eventuallyEq`), `CuspData.lean:125` (`cuspFunction_polynomial_eval_eventuallyEq`), `LaurentQExpansion.lean:68/79/90` (`cuspFunction_add/mul/const_eventuallyEq`).

### `private lemma Cox.cuspData_sub_const_mul_pow`
- **Type**: `(N : ℕ+) {f g : ℍ → ℂ} (hf : CuspData N f) (hg : CuspData N g) (a : ℂ) (m : ℕ) : CuspData N (fun τ ↦ f τ - a * g τ ^ m)`
- **What**: Raw cusp data is preserved by `f ↦ f - a·g^m`.
- **How**: Three components: `MeromorphicAt.sub/mul/pow` on ℍ; pointwise invariance via `congrArg₂` on the slash identities; cusp meromorphy via `MeromorphicAt.congr` with `cuspFunction_sub_const_mul_pow_eventuallyEq`.
- **Hypotheses**: both `f` and `g` carry level-`N` cusp data.
- **Uses from project**: `CuspData`, `cuspFunction_sub_const_mul_pow_eventuallyEq`
- **Used by**: `CuspData.polynomialInJ_of_holomorphic`
- **Visibility**: private
- **Lines**: 75–94, proof body ≈ 16 lines
- **Notes**: Same three-bullet skeleton as `CuspData.mul` and `CuspData.polynomialIn` (CuspData.lean:98, 137). Would be a one-liner from `CuspData.sub`/`CuspData.const_mul`/`CuspData.pow` (missing) or from `CuspData.polynomialIn` with a bivariate polynomial.

### `private lemma Cox.meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq`
- **Type**: `{f g : ℂ → ℂ} {x : ℂ} {n : ℤ} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) (hfn : meromorphicOrderAt f x = n) (hgn : meromorphicOrderAt g x = n) (htc : meromorphicTrailingCoeffAt f x = meromorphicTrailingCoeffAt g x) : (n : WithTop ℤ) < meromorphicOrderAt (fun z ↦ f z - g z) x`
- **What**: If two meromorphic functions have the same finite order and the same leading (trailing) coefficient, their difference has strictly larger order.
- **How**: Unpack `meromorphicOrderAt_eq_int_iff` to `f = (z-x)^n·F`, `g = (z-x)^n·G` with `F x, G x ≠ 0`; `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE` identifies `F x = G x`; then `H = F - G` is analytic with `H x = 0`, so `meromorphicOrderAt H x > 0` via `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`; conclude with `meromorphicOrderAt_mul` and `meromorphicOrderAt_zpow_id_sub_const`.
- **Hypotheses**: both meromorphic at `x`, orders both equal to the integer `n`, equal trailing coefficients.
- **Uses from project**: `[]`
- **Used by**: `exists_const_poleOrder_sub_mul_pow_lt`
- **Visibility**: private
- **Lines**: 96–130, proof body ≈ 29 lines
- **Notes**: Fully generic mathlib-only lemma stated for ℂ; see Generalization notes. Candidate mathlib contribution (the cancelling case complementary to `MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub`).

### `private lemma Cox.poleOrder_lt_of_neg_lt_meromorphicOrderAt`
- **Type**: `{F : ℍ → ℂ} {m : ℕ} (hm : 0 < m) (hord : ((-(m : ℤ) : ℤ) : WithTop ℤ) < meromorphicOrderAt (cuspFunction 1 F) 0) : poleOrder 1 F < m`
- **What**: If the width-1 cusp order of `F` exceeds `-m` then its pole order at ∞ is below `m`.
- **How**: `poleOrder_eq_toNat_neg_meromorphicOrderAt`, case split on `WithTop ℤ`, `omega`.
- **Hypotheses**: `m > 0` and the strict order bound.
- **Uses from project**: `poleOrder`, `poleOrder_eq_toNat_neg_meromorphicOrderAt`
- **Used by**: `exists_const_poleOrder_sub_mul_pow_lt`
- **Visibility**: private
- **Lines**: 132–144, proof body ≈ 8 lines
- **Notes**: Natural companion lemma for `poleOrder` that belongs in `LaurentQExpansion.lean` next to `poleOrder_eq_toNat_neg_meromorphicOrderAt` (LaurentQExpansion.lean:261).

### `private lemma Cox.exists_const_poleOrder_sub_mul_pow_lt`
- **Type**: `{f g : ℍ → ℂ} (hfmer : MeromorphicAt (cuspFunction 1 f) 0) (hgmer : MeromorphicAt (cuspFunction 1 g) 0) (hgorder : poleOrder 1 g = 1) (hm : 0 < poleOrder 1 f) : ∃ a : ℂ, poleOrder 1 (fun τ ↦ f τ - a * g τ ^ poleOrder 1 f) < poleOrder 1 f`
- **What**: The pole-killing step of Lemma 11.10(ii): with `g` having a simple pole at ∞, subtracting `a·g^m` (`a` = ratio of leading coefficients) lowers the pole order of `f`.
- **How**: `a := cF / cG^m` with `cF, cG` the `meromorphicTrailingCoeffAt` of the cusp functions (nonzero by `MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero`); computes order and trailing coefficient of `a·G^m` by `meromorphicOrderAt_mul_of_ne_zero`, `meromorphicOrderAt_pow`, `meromorphicTrailingCoeffAt_mul/_pow/_const`; then `meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq` and `poleOrder_lt_of_neg_lt_meromorphicOrderAt`.
- **Hypotheses**: both cusp functions meromorphic at 0; `g` has pole order exactly 1; `f` has a genuine pole.
- **Uses from project**: `poleOrder`, `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder`, `poleOrder_lt_of_neg_lt_meromorphicOrderAt`, `cuspFunction_sub_const_mul_pow_eventuallyEq`, `meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq`
- **Used by**: `CuspData.polynomialInJ_of_holomorphic`
- **Visibility**: private
- **Lines**: 146–194, proof body ≈ 42 lines
- **Notes**: Proof >30 lines. Lines 174–188 (order and trailing coefficient of `fun q ↦ a * G q ^ m`) are a self-contained pair of lemmas `meromorphicOrderAt_const_mul_pow` / `meromorphicTrailingCoeffAt_const_mul_pow` that would halve this proof.

### `theorem Cox.CuspData.polynomialInJ_of_holomorphic`
- **Type**: `{f : ℍ → ℂ} (hf : LevelOneCuspData f) (hfH : MDiff f) : ∃ P : Polynomial ℂ, f = Cox.polynomialIn P j`
- **What**: Cox Lemma 11.10(ii): a level-one modular function holomorphic on ℍ is a polynomial in `j`.
- **How**: `Nat.strong_induction_on` on `poleOrder 1 f`. Base case (`poleOrder = 0`): `analyticAt_cuspFunction_iff_poleOrder_eq_zero` then `levelOne_constant_of_holomorphic`. Step: `exists_const_poleOrder_sub_mul_pow_lt` with `g = j` (`j_cuspFunction_meromorphicAt`, `j_poleOrder`) gives `a`; `f' := f - a·j^m` keeps cusp data (`cuspData_sub_const_mul_pow`, `j_levelOneCuspData`) and holomorphy (`ModularFunction.j_mdifferentiable`), IH gives `P`, return `P + monomial m a` via `linear_combination`.
- **Hypotheses**: level-one cusp data and holomorphy on ℍ.
- **Uses from project**: `LevelOneCuspData`, `poleOrder`, `Cox.polynomialIn`, `analyticAt_cuspFunction_iff_poleOrder_eq_zero`, `levelOne_constant_of_holomorphic`, `exists_const_poleOrder_sub_mul_pow_lt`, `j_cuspFunction_meromorphicAt`, `j_poleOrder`, `cuspData_sub_const_mul_pow`, `j_levelOneCuspData`, `ModularFunction.j_mdifferentiable`, `j`
- **Used by**: `CuspData.rationalInJ`, `levelOne_polynomialInJ_of_holomorphic`
- **Visibility**: public
- **Lines**: 198–241, proof body ≈ 41 lines
- **Notes**: Proof >30 lines. The inductive step (lines 218–233) is a standalone lemma "∃ a, `f - a·j^m` has `LevelOneCuspData`, `MDiff`, and smaller `poleOrder`" that would collapse the main proof to ≈15 lines. Externally unused (only via `rationalInJ` and `levelOne_polynomialInJ_of_holomorphic`).

### `private lemma Cox.eventually_mdifferentiableAt_atImInfty`
- **Type**: `{f : ℍ → ℂ} (hf : LevelOneCuspData f) : ∀ᶠ τ in atImInfty, MDiffAt f τ`
- **What**: A level-one modular function is holomorphic on a high enough half-plane.
- **How**: The cusp function is meromorphic at 0 hence analytic on a punctured neighbourhood (`MeromorphicAt.eventually_analyticAt`); pull back along `Periodic.qParam_tendsto.comp tendsto_coe_atImInfty`; transfer to `MDiffAt` via `mdifferentiableAt_iff`, `DifferentiableAt.comp` with `Periodic.differentiable_qParam`, and `eq_cuspFunction`.
- **Hypotheses**: level-one cusp data.
- **Uses from project**: `LevelOneCuspData`, `periodic_comp_sl2`
- **Used by**: `exists_polynomial_clearing_poles_on_fd_aux`
- **Visibility**: private
- **Lines**: 243–264, proof body ≈ 19 lines
- **Notes**: Generic fact about any function with meromorphic width-1 cusp expansion; belongs next to `poleOrder` API in `LaurentQExpansion.lean`.

### `private lemma Cox.finite_not_mdifferentiableAt_truncatedFundamentalDomain`
- **Type**: `{f : ℍ → ℂ} (hf : LevelOneCuspData f) (y : ℝ) : {τ | τ ∈ ModularGroup.truncatedFundamentalDomain y ∧ ¬MDiffAt f τ}.Finite`
- **What**: A meromorphic function on ℍ has only finitely many non-holomorphic points in a truncated fundamental domain.
- **How**: The analytic locus is codiscrete (`MeromorphicOn.eventually_codiscreteWithin_analyticAt`), restrict via `Filter.codiscreteWithin_mono` to the compact image `coe '' K` (`ModularGroup.isCompact_truncatedFundamentalDomain`, `UpperHalfPlane.isEmbedding_coe.isCompact_iff`), then `IsCompact.finite_diff_of_mem_codiscreteWithin` and pull back along the injective coercion (`Set.Finite.of_finite_image`).
- **Hypotheses**: level-one cusp data (only the first component, meromorphy on ℍ, is used).
- **Uses from project**: `LevelOneCuspData`
- **Used by**: `exists_polynomial_clearing_poles_on_fd_aux`
- **Visibility**: private
- **Lines**: 266–292, proof body ≈ 24 lines
- **Notes**: Hypothesis is far stronger than needed (only `MeromorphicOn (f ∘ ofComplex) upperHalfPlaneSet` is used); the compact set is arbitrary, so this is "meromorphic on ℍ ⇒ finitely many singularities in any compact `K ⊆ ℍ`".

### `private lemma Cox.exists_analyticAt_pow_succ_mul_of_meromorphicAt_of_analyticAt_zero`
- **Type**: `{F J : ℂ → ℂ} {x : ℂ} (hF : MeromorphicAt F x) (hJ : AnalyticAt ℂ J x) (hJ0 : J x = 0) : ∃ n : ℕ, AnalyticAt ℂ (fun z ↦ J z ^ (n + 1) * F z) x`
- **What**: A high power of any analytic function vanishing at `x` clears the pole of a meromorphic `F` at `x`.
- **How**: Unfold `MeromorphicAt` to `(z-x)^n • F` analytic; write `J z = (z - x) * dslope J x z` (`sub_smul_dslope_of_zero`), with `dslope J x` analytic via `HasFPowerSeriesAt.has_fpower_series_dslope_fslope`; then `J^(n+1)·F = J·(dslope)^n·((z-x)^n F)` is a product of analytic functions.
- **Hypotheses**: `F` meromorphic at `x`, `J` analytic at `x` with `J x = 0`.
- **Uses from project**: `[]`
- **Used by**: `exists_mdifferentiableAt_j_sub_pow_succ_mul`
- **Visibility**: private
- **Lines**: 294–317, proof body ≈ 20 lines
- **Notes**: Generic mathlib-only lemma; see Generalization notes.

### `private lemma Cox.exists_mdifferentiableAt_j_sub_pow_succ_mul`
- **Type**: `{f : ℍ → ℂ} (hf : LevelOneCuspData f) (τ : ℍ) : ∃ n : ℕ, MDiffAt (fun z ↦ (j z - j τ) ^ (n + 1) * f z) τ`
- **What**: At each point `τ`, a power of `j - j(τ)` clears the pole of `f` at `τ`.
- **How**: Specializes the previous lemma to `J = j ∘ ofComplex - j τ` (analytic by `ModularFunction.j_mdifferentiable` and `DifferentiableOn.analyticAt`) and `F = f ∘ ofComplex`, then `mdifferentiableAt_iff`.
- **Hypotheses**: level-one cusp data (only meromorphy on ℍ used).
- **Uses from project**: `LevelOneCuspData`, `j`, `ModularFunction.j_mdifferentiable`, `exists_analyticAt_pow_succ_mul_of_meromorphicAt_of_analyticAt_zero`
- **Used by**: `exists_polynomial_clearing_poles_on_fd_aux`
- **Visibility**: private
- **Lines**: 319–336, proof body ≈ 15 lines
- **Notes**: —

### `private lemma Cox.mdifferentiable_polynomialIn_j`
- **Type**: `(P : Polynomial ℂ) : MDiff (Cox.polynomialIn P j)`
- **What**: Polynomials in `j` are holomorphic on ℍ.
- **How**: `mdifferentiable_iff` and `Polynomial.differentiable.comp_differentiableOn`.
- **Hypotheses**: none.
- **Uses from project**: `Cox.polynomialIn`, `ModularFunction.j_mdifferentiable`
- **Used by**: `exists_polynomial_clearing_poles_on_fd_aux` (three times)
- **Visibility**: private
- **Lines**: 338–342, proof body ≈ 3 lines
- **Notes**: Should be a public companion lemma of `Cox.polynomialIn` (e.g. `MDifferentiable.polynomialIn`); the same fact is re-proved as `Polynomial.differentiable.comp` in `Construction.lean` neighbourhood (see `coxPhiFunction_coeff_mdifferentiable`).

### `private lemma Cox.levelOne_invariant_apply`
- **Type**: `{f : ℍ → ℂ} (hf : LevelOneCuspData f) (γ : SL(2, ℤ)) (τ : ℍ) : f (γ • τ) = f τ`
- **What**: Pointwise SL₂(ℤ)-invariance of a level-one function.
- **How**: Lift `γ` to `Gamma0 1` via `Subsingleton.elim`, apply `hf.2.1`, simplify `SL_slash_apply` at weight 0.
- **Hypotheses**: level-one cusp data.
- **Uses from project**: `LevelOneCuspData`
- **Used by**: `exists_polynomial_clearing_poles`
- **Visibility**: private
- **Lines**: 344–350, proof body ≈ 4 lines
- **Notes**: The four-line "`Gamma0 1` via `Subsingleton.elim` + `SL_slash_apply, neg_zero, zpow_zero, mul_one`" idiom is repeated at lines 46–49 (inside `levelOne_constant_of_holomorphic`), CuspData.lean:104–109, 144–148, Congruence.lean:75–77, Interpolation.lean:283–287. A public `CuspData.apply_smul` / `LevelOneCuspData.apply_sl2_smul` would remove all of them.

### `private lemma Cox.exists_polynomial_clearing_poles_on_fd_aux`
- **Type**: `{f : ℍ → ℂ} (hf : LevelOneCuspData f) : ∃ P : Polynomial ℂ, P ≠ 0 ∧ ∀ τ ∈ ModularGroup.fd, MDiffAt (fun z ↦ P.eval (j z) * f z) τ`
- **What**: A nonzero polynomial in `j` clears all poles of `f` on the fundamental domain.
- **How**: Take `y` from `eventually_mdifferentiableAt_atImInfty` (`atImInfty_mem`), the finite bad set `S` below `y` from `finite_not_mdifferentiableAt_truncatedFundamentalDomain`, exponents `e τ` by `Classical.choose` on `exists_mdifferentiableAt_j_sub_pow_succ_mul`, and `P := ∏_{τ∈S} (X - C (j τ))^(e τ + 1)` (nonzero by `Finset.prod_ne_zero_iff`, `Polynomial.X_sub_C_ne_zero`). At a bad `τ`, split `P = factor τ * Q` with `Finset.mul_prod_erase` and use `mdifferentiable_polynomialIn_j`.
- **Hypotheses**: level-one cusp data.
- **Uses from project**: `LevelOneCuspData`, `eventually_mdifferentiableAt_atImInfty`, `finite_not_mdifferentiableAt_truncatedFundamentalDomain`, `exists_mdifferentiableAt_j_sub_pow_succ_mul`, `mdifferentiable_polynomialIn_j`, `Cox.polynomialIn`, `j`
- **Used by**: `CuspData.exists_polynomial_clearing_poles`
- **Visibility**: private
- **Lines**: 352–395, proof body ≈ 40 lines
- **Notes**: Proof >30 lines; `classical`. Helper that would collapse it: `mdifferentiableAt_finsetProd_mul_of_forall` — "if `S` finite and for each `s ∈ S`, `g_s * f` is `MDiffAt s` with `g_s` holomorphic everywhere, then `(∏ g_s) * f` is `MDiffAt` at every `s ∈ S`" (lines 377–395).

### `theorem Cox.CuspData.exists_polynomial_clearing_poles`
- **Type**: `{f : ℍ → ℂ} (hf : LevelOneCuspData f) : ∃ P : Polynomial ℂ, P ≠ 0 ∧ MDiff (fun τ ↦ P.eval (j τ) * f τ)`
- **What**: A nonzero polynomial in `j` clears all poles of a level-one modular function on all of ℍ.
- **How**: From the fundamental-domain version, translate any `τ` into `fd` by `ModularGroup.exists_smul_mem_fd`; `H := P(j)·f` is SL₂-invariant (`j_modularGroup_smul`, `levelOne_invariant_apply`) so `MDiffAt` transfers via `MDifferentiableAt.comp` with `UpperHalfPlane.mdifferentiable_smul`.
- **Hypotheses**: level-one cusp data.
- **Uses from project**: `LevelOneCuspData`, `exists_polynomial_clearing_poles_on_fd_aux`, `j_modularGroup_smul`, `levelOne_invariant_apply`, `j`
- **Used by**: `CuspData.rationalInJ`
- **Visibility**: public
- **Lines**: 398–415, proof body ≈ 15 lines
- **Notes**: Externally unused. Lines 406–415 are the generic "SL₂-invariant + MDiffAt on fd ⇒ MDiff" argument, which is missing as a lemma.

### `theorem Cox.CuspData.rationalInJ`
- **Type**: `{f : ℍ → ℂ} (hf : LevelOneCuspData f) : RationalIn f j`
- **What**: Every function with level-one cusp data is a rational function of `j` (pointwise off the denominator's zero set).
- **How**: Pole-clearing gives `P ≠ 0` with `P(j)·f` holomorphic; `P(j)·f` still has cusp data (`CuspData.polynomialIn`, `CuspData.mul`), so `polynomialInJ_of_holomorphic` gives `Q`; divide (`eq_div_iff`).
- **Hypotheses**: level-one cusp data.
- **Uses from project**: `LevelOneCuspData`, `RationalIn`, `CuspData.exists_polynomial_clearing_poles`, `j_levelOneCuspData`, `CuspData.polynomialIn`, `CuspData.mul`, `CuspData.polynomialInJ_of_holomorphic`, `Cox.polynomialIn`, `j`
- **Used by**: `theorem_11_9_i`; externally `Interpolation.lean:494` (`theorem_11_9_ii_pointwise`)
- **Visibility**: public
- **Lines**: 418–428, proof body ≈ 9 lines
- **Notes**: The only external consumer of the raw-data rationality theorem; it is load-bearing for 11.9(ii).

### `theorem Cox.theorem_11_9_i`
- **Type**: `(f : ModularFunction 𝒮ℒ) : RationalIn f j`
- **What**: Cox Theorem 11.9(i): every level-one (bundled) modular function is a rational function of `j`.
- **How**: `CuspData.of_levelOneModularFunction` then `CuspData.rationalInJ`.
- **Hypotheses**: `f` is a bundled modular function for `SL₂(ℤ)` (as `𝒮ℒ = (mapGL ℝ).range`).
- **Uses from project**: `ModularFunction`, `RationalIn`, `CuspData.of_levelOneModularFunction`, `CuspData.rationalInJ`, `j`
- **Used by**: unused in file; externally `ModularFunctionField.lean:106` (`toMeromorphicField_eq_ratFunc`)
- **Visibility**: public
- **Lines**: 431–432, proof body ≈ 1 line
- **Notes**: Spine statement. Conclusion `RationalIn f j` = `∃ P Q : ℂ[X], Q ≠ 0 ∧ ∀ τ, Q.eval (j τ) ≠ 0 → f τ = P.eval (j τ) / Q.eval (j τ)`. Project lemmas consumed transitively: `CuspData.of_levelOneModularFunction` → `CuspData.of_modularFunction` (`ModularFunction.meromorphicOn`, `cuspFunction_gamma0`), `rationalInJ` → {`exists_polynomial_clearing_poles`, `polynomialInJ_of_holomorphic`, `j_levelOneCuspData`, `CuspData.polynomialIn`, `CuspData.mul`} → {`j_cuspFunction_meromorphicAt`, `j_poleOrder`, `j_modularGroup_smul`, `ModularFunction.j_mdifferentiable`, `poleOrder` API in `LaurentQExpansion.lean`, `periodic_comp_sl2_of_gamma0_invariant`}.

### `theorem Cox.levelOne_polynomialInJ_of_holomorphic`
- **Type**: `(f : ModularFunction 𝒮ℒ) (hf : MDiff f) : ∃ P : Polynomial ℂ, (f : ℍ → ℂ) = Cox.polynomialIn P j`
- **What**: A bundled level-one modular function holomorphic on ℍ is a polynomial in `j`.
- **How**: `CuspData.of_levelOneModularFunction` then `CuspData.polynomialInJ_of_holomorphic`.
- **Hypotheses**: bundled level-one modular function, holomorphic on ℍ.
- **Uses from project**: `ModularFunction`, `Cox.polynomialIn`, `CuspData.of_levelOneModularFunction`, `CuspData.polynomialInJ_of_holomorphic`, `j`
- **Used by**: unused in file; externally `Construction.lean:286` (`coxPhiFunction_coeff_polynomialInJ`)
- **Visibility**: public
- **Lines**: 435–437, proof body ≈ 1 line
- **Notes**: Load-bearing for the modular-polynomial construction.

## File Summary
- Total declarations: 18 (0 defs, 18 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `LevelOneCuspData` (imported; used by 12), `mdifferentiable_polynomialIn_j` (3 call sites, all inside one proof), `cuspFunction_sub_const_mul_pow_eventuallyEq` (2)
- Unused declarations (not used by anything in this file): `theorem_11_9_i` (used externally by `ModularFunctionField.lean:106`), `levelOne_polynomialInJ_of_holomorphic` (used externally by `Construction.lean:286`)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `exists_const_poleOrder_sub_mul_pow_lt` (42), `CuspData.polynomialInJ_of_holomorphic` (41), `exists_polynomial_clearing_poles_on_fd_aux` (40)

## Observations

### Mathlib API candidates
- `levelOne_constant_of_holomorphic` (30–61) rides on `ModularFormClass.levelOne_weight_zero_const` (`.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean:104`); it hand-builds a `ModularForm (mapGL ℝ).range 0` structure. Mathlib has no "modular function" notion (grep `ModularFunction|modular function` over `Mathlib/`: nothing), so bridging through `ModularForm` is the only route.
- `meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq` (96–130): no direct analogue. Nearest is `MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub` (`Mathlib/Analysis/Meromorphic/TrailingCoefficient.lean:337`), which covers the complementary non-cancelling case; `meromorphicOrderAt_add` (`Mathlib/Analysis/Meromorphic/Order.lean:563`) gives only `≥ n`. Searched: `meromorphicOrderAt_sub`, `lt_meromorphicOrderAt`, `trailingCoeff.*sub`. This is a candidate mathlib addition.
- `exists_analyticAt_pow_succ_mul_of_meromorphicAt_of_analyticAt_zero` (294–317): no analogue found; searched `MeromorphicAt.*pow`, `analyticAt.*meromorphicAt.*mul`, `exists_eventuallyEq_pow_smul` (`Mathlib/Analysis/Meromorphic/Basic.lean:290` is the `(z-x)^n` version only). Uses mathlib `sub_smul_dslope_of_zero` (`Mathlib/Analysis/Calculus/DSlope.lean:145`).
- `finite_not_mdifferentiableAt_truncatedFundamentalDomain` (266–292) already rides on `IsCompact.finite_diff_of_mem_codiscreteWithin` (`Mathlib/Topology/DiscreteSubset.lean:396`) and `MeromorphicOn.eventually_codiscreteWithin_analyticAt` (`Mathlib/Analysis/Meromorphic/Basic.lean`); it is a 24-line wrapper whose only nontrivial content is transporting along `UpperHalfPlane.isEmbedding_coe` (`Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean:37`).
- `cuspFunction_sub_const_mul_pow_eventuallyEq` (63–73): mathlib has only the `ContinuousAt`-at-0 pointwise versions `UpperHalfPlane.cuspFunction_mul` / `cuspFunction_smul` (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:440,448`) and `Periodic.cuspFunction_smul` (`Mathlib/Analysis/Complex/Periodic.lean:257`); the `=ᶠ[𝓝[≠] 0]` form is absent from mathlib and is re-implemented 6× in this project (see Missing API).
- `poleOrder_lt_of_neg_lt_meromorphicOrderAt` (132–144) and `eventually_mdifferentiableAt_atImInfty` (243–264) are generic `poleOrder`/cusp-function facts with no Cox content; they belong in `LaurentQExpansion.lean` next to `poleOrder_eq_toNat_neg_meromorphicOrderAt` (`LaurentQExpansion.lean:261`).

### Missing API / repeated patterns
- **`cuspFunction … =ᶠ[𝓝[≠] 0] …` skeleton** (`filter_upwards [self_mem_nhdsWithin]; simp only [UpperHalfPlane.cuspFunction]; rw [Periodic.cuspFunction_eq_of_nonzero …]×k; rfl`) appears at ModularFunction.lean:63–73, CuspData.lean:86–95, CuspData.lean:125–134, LaurentQExpansion.lean:68, 79, 90, Algebra.lean:55. One lemma `UpperHalfPlane.cuspFunction_comp₂_eventuallyEq (op : ℂ → ℂ → ℂ) (h) (f g) : cuspFunction h (fun τ ↦ op (f τ) (g τ)) =ᶠ[𝓝[≠] 0] fun q ↦ op (cuspFunction h f q) (cuspFunction h g q)` (plus a unary `cuspFunction_comp_eventuallyEq (φ : ℂ → ℂ)`) collapses all seven.
- **`Gamma0 1` lift + `SL_slash_apply, neg_zero, zpow_zero, mul_one`** idiom: lines 46–49 and 344–350 here, CuspData.lean:104–109 and 144–148, Interpolation.lean:283–287, Congruence.lean:75–77. Missing lemma: `Cox.CuspData.apply_smul (hf : CuspData N f) (γ : Gamma0 N) (τ) : f (γ • τ) = f τ` and `LevelOneCuspData.apply_sl2_smul`.
- **Three-bullet `CuspData` closure skeleton** (`refine ⟨?_, ?_, ?_⟩` with `MeromorphicAt.*`, `funext; congrArg`, `MeromorphicAt.congr (…eventuallyEq).symm`): lines 75–94 here, CuspData.lean:98–113 and 137–152. A single `CuspData.map₂ (op) (hop_mer : ∀ z, MeromorphicAt … ) ` or the concrete `CuspData.sub`, `CuspData.const_mul`, `CuspData.pow` companions would make `cuspData_sub_const_mul_pow` a one-liner.
- `Cox.polynomialIn` lacks `MDifferentiable`/`fun_prop` companion: `mdifferentiable_polynomialIn_j` (338–342) is private here while `Construction.lean:212–220` re-derives holomorphy of polynomial expressions in `j`.
- Missing: "SL₂(ℤ)-invariant and `MDiffAt` on `fd` ⇒ `MDiff`" lemma (lines 406–415).
- Missing: the inductive-step lemma of Lemma 11.10(ii) (lines 218–233) and the `∏(X - C c)^e` pole-clearing lemma (lines 377–395).

### Junk candidates
- None dead. `LatticeJ` import (line 7) supplies nothing used directly in this file (all `j_*` facts come via `LevelJ → CuspData → Congruence → JInvariant → jfunction`); it is needed only transitively by downstream importers (`Construction.lean` imports this file). Worth checking with `lake env lean` whether the import can move.
- `levelOne_constant_of_holomorphic` docstring says "Cox Lemma 11.10(i)" but the lemma is stated for raw `LevelOneCuspData` rather than a bundled function — fine, but the docstring of the file header (lines 13–15) says "The public statements use the bundled definition" while 3 of the 5 public theorems here take raw `LevelOneCuspData`.

### Moral duplicates within this batch
- `cuspFunction_sub_const_mul_pow_eventuallyEq` (63) ≈ `CuspData.lean:86 cuspFunction_mul_eventuallyEq` ≈ `CuspData.lean:125 cuspFunction_polynomial_eval_eventuallyEq` ≈ `LaurentQExpansion.lean:79 cuspFunction_mul_eventuallyEq` (identical name and statement to CuspData.lean:86, both private).
- `cuspData_sub_const_mul_pow` (75) ≈ `CuspData.mul` (CuspData.lean:98) ≈ `CuspData.polynomialIn` (CuspData.lean:137): same proof skeleton, different pointwise operation.
- `levelOne_invariant_apply` (344) ≈ the inline `hinv` at 46–49.

### Generalization notes
- `meromorphicOrderAt_sub_gt_of_eq_and_trailingCoeff_eq` (96–130): every cited lemma (`meromorphicOrderAt_eq_int_iff`, `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE`, `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`, `meromorphicOrderAt_mul`, `meromorphicOrderAt_zpow_id_sub_const`) is stated for `{𝕜} [NontriviallyNormedField 𝕜] {E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]`; the lemma holds verbatim for `f g : 𝕜 → E` (the `simp … smul_eq_mul, mul_sub` at line 121 becomes `smul_sub`).
- `exists_analyticAt_pow_succ_mul_of_meromorphicAt_of_analyticAt_zero` (294–317): holds for `F : 𝕜 → E`, `J : 𝕜 → 𝕜` over any complete nontrivially normed field (`sub_smul_dslope_of_zero`, `HasFPowerSeriesAt.has_fpower_series_dslope_fslope` are generic).
- `finite_not_mdifferentiableAt_truncatedFundamentalDomain` (266–292): only uses `hf.1`; the truncated fundamental domain can be any compact `K ⊆ ℍ`.
