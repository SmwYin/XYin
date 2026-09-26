# Inventory: XYin/PhD/Modularforms/Eisenstein.lean  (692 lines)

Defines `E₄`, `E₆ : ModularForm ↑Γ(1) k` (as `(1/2) • eisensteinSeriesMF _ 0`, i.e. `E 4 _`, `E 6 _`), proves their periodicity/`S`-transformation, computes q-expansion coefficients (`E4_q_exp : 1, 240σ₃(m)`; `E6_q_exp : 1, −504σ₅(m)`; general `Ek_q_exp`), builds the cusp form `Delta_E4_E6_aux = (E₄³ − E₆²)/1728`, proves the imaginary-axis reality `ResToImagAxis.Real` of `E_k` (even `k ≥ 4`) and of `E₂`, and proves `E₂` is bounded at `i∞` via the explicit Lambert-series bound `‖Σ n qⁿ/(1−qⁿ)‖ ≤ ‖q‖/(1−‖q‖)³`. Also carries a grab-bag of q-expansion/cusp-function utilities (`cuspfunc_lim_coef`, `q_exp_unique`, …), the `φ₀, φ₋₂, φ₋₄` quotients by `Δ`, and Bernoulli/`I^6` constants. Externally only `E₄`, `E₆`, `bernoulli'_six`, `Delta_E4_E6_aux`, `Delta_q_one_term` are used.

## Declarations

### `lemma exists_smul_eq_of_rank_one`
- **Type**: `{M} [AddCommGroup M] [Module ℂ M] (hrank : Module.rank ℂ M = 1) {e : M} (he : e ≠ 0) (f : M) : ∃ c : ℂ, f = c • e`
- **What**: In a one-dimensional ℂ-space every vector is a multiple of any nonzero vector.
- **How**: `finrank_eq_one_iff_of_nonzero'` after `Module.rank_eq_one_iff_finrank_eq_one`.
- **Hypotheses**: rank 1, `e ≠ 0`.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 34–38, proof body ≈ 3 lines
- **Notes**: Unused anywhere. Wrapper of `finrank_eq_one_iff_of_nonzero'` (used identically by mathlib at `LevelOne/DimensionFormula.lean:165,226,229`). Belongs in a linear-algebra file, not here.

### `lemma exists_smul_eq_of_rank_one'`
- **Type**: same as above with conclusion `∃ c : ℂ, c • e = f`
- **What**: Symmetric form.
- **How**: Term-mode `finrank_eq_one_iff_of_nonzero'`.
- **Hypotheses**: rank 1, `e ≠ 0`.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 41–43, proof body ≈ 1 line
- **Notes**: Unused anywhere; `eq_comm` of the previous.

### `lemma smul_modularForm_eq_pointwise`
- **Type**: `{Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f g : ModularForm Γ k} {c : ℂ} (h : f = c • g) (z : ℍ) : (f : ℍ → ℂ) z = c * (g : ℍ → ℂ) z`
- **What**: Turns an equality of modular forms `f = c • g` into a pointwise identity.
- **How**: `congrFun (congrArg coe h) z` + `ModularForm.coe_smul`.
- **Hypotheses**: `f = c • g`.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 46–49, proof body ≈ 2 lines
- **Notes**: Unused anywhere. Equivalent to `by rw [h]; simp` / `ModularForm.smul_apply`.

### `def E₄`
- **Type**: `ModularForm (CongruenceSubgroup.Gamma ↑1) 4`
- **What**: The normalised weight-4 Eisenstein series.
- **How**: `(1/2 : ℂ) • eisensteinSeriesMF (by norm_num) standardcongruencecondition` (definitionally `E 4 _`).
- **Hypotheses**: none
- **Uses from project**: `standardcongruencecondition` (Eisensteinqexpansions.lean:20)
- **Used by**: `E4_eq`, `E4_apply`, `E₄_periodic`, `E₄_S_transform`, `φ₀`, `φ₂'`, `φ₄'`, `auxasdf`, `E4_q_exp`, `E4E6_coeff_zero_eq_zero`, `Delta_E4_E6_aux`, `E4_pow_q_exp_one`, `E4_ne_zero`, `E₄_imag_axis_real`, `E₄_isBoundedAtImInfty`, `E₂_mul_E₄_isBoundedAtImInfty`
- **Visibility**: public
- **Lines**: 55–57, proof body ≈ 0 lines
- **Notes**: Externally used by `ResToImagAxis.lean` (docstring only), `DimensionFormulas.lean`, `qExpansion_tactic/{link,Qj}.lean`, `jFunction/Deltaqexpansions.lean`, `Cox/LatticeJ.lean`. mathlib `ModularForm.E₄ : ModularForm 𝒮ℒ 4 := E (by norm_num)` (`Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean:51`) — hence `open ModularForm hiding E₄ E₆` at line 21. Re-expands the definition of `E` instead of writing `E 4 (by norm_num)`. Inline comment 56–57 duplicates `Eisensteinqexpansions.lean:23–24`; comment 53 is `/- -/` not a docstring.

### `def E₆`
- **Type**: `ModularForm (CongruenceSubgroup.Gamma ↑1) 6`
- **What**: The normalised weight-6 Eisenstein series.
- **How**: As `E₄` with weight 6.
- **Hypotheses**: none
- **Uses from project**: `standardcongruencecondition`
- **Used by**: `E6_eq`, `E6_apply`, `E₆_periodic`, `E₆_S_transform`, `φ₀`, `φ₂'`, `auxasdf`, `E6_q_exp`, `E4E6_coeff_zero_eq_zero`, `Delta_E4_E6_aux`, `E6_ne_zero`, `E₆_imag_axis_real`
- **Visibility**: public
- **Lines**: 59–60, proof body ≈ 0 lines
- **Notes**: mathlib `ModularForm.E₆` (`EisensteinSeries/Basic.lean:54`). Same external users as `E₄`.

### `lemma E4_eq`
- **Type**: `E₄ = E 4 (by norm_num)`
- **What**: `E₄` is `E 4`.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: `E₄`, `E` (Eisensteinqexpansions.lean:22)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 62, proof body ≈ 0 lines
- **Notes**: Unused anywhere (all callers unfold with `simp [E₄, ModularForm.E, …]` instead).

### `lemma E6_eq`
- **Type**: `E₆ = E 6 (by norm_num)`
- **What**: `E₆` is `E 6`.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: `E₆`, `E`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 64, proof body ≈ 0 lines
- **Notes**: Unused anywhere.

### `lemma E4_apply`
- **Type**: `(z : ℍ) : E₄ z = E 4 (by norm_num) z`
- **What**: Pointwise form of `E4_eq`.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: `E₄`, `E`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 66, proof body ≈ 0 lines
- **Notes**: Unused anywhere.

### `lemma E6_apply`
- **Type**: `(z : ℍ) : E₆ z = E 6 (by norm_num) z`
- **What**: Pointwise form of `E6_eq`.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: `E₆`, `E`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 68, proof body ≈ 0 lines
- **Notes**: Unused anywhere.

### `lemma E₄_periodic`
- **Type**: `(z : ℍ) : E₄ ((1 : ℝ) +ᵥ z) = E₄ z`
- **What**: 1-periodicity of `E₄`.
- **How**: `SlashInvariantForm.vAdd_width_periodic 1 4 1 E₄.toSlashInvariantForm z`.
- **Hypotheses**: none
- **Uses from project**: `E₄`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 71–72, proof body ≈ 1 line
- **Notes**: Unused anywhere. `vAdd_width_periodic` is `Mathlib/NumberTheory/ModularForms/Identities.lean:37`.

### `lemma E₆_periodic`
- **Type**: `(z : ℍ) : E₆ ((1 : ℝ) +ᵥ z) = E₆ z`
- **What**: 1-periodicity of `E₆`.
- **How**: As `E₄_periodic`.
- **Hypotheses**: none
- **Uses from project**: `E₆`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 75–76, proof body ≈ 1 line
- **Notes**: Unused anywhere; 4↔6 twin.

### `lemma E₄_S_transform`
- **Type**: `(z : ℍ) : E₄ (ModularGroup.S • z) = z ^ (4 : ℕ) * E₄ z`
- **What**: `E₄(−1/z) = z⁴ E₄(z)`.
- **How**: `E₄.slash_action_eq'` at `S` (membership via `mem_Gamma_one`), `SL_slash_apply`, `ModularGroup.denom_S`, `field_simp`.
- **Hypotheses**: none
- **Uses from project**: `E₄`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 79–88, proof body ≈ 9 lines
- **Notes**: Unused anywhere. Same skeleton as `E₆_S_transform`, `Δ_S_transform` (Delta.lean:69), `E₂_S_transform` (E2.lean:87).

### `lemma E₆_S_transform`
- **Type**: `(z : ℍ) : E₆ (ModularGroup.S • z) = z ^ (6 : ℕ) * E₆ z`
- **What**: `E₆(−1/z) = z⁶ E₆(z)`.
- **How**: Identical to `E₄_S_transform` with `4 ↦ 6`.
- **Hypotheses**: none
- **Uses from project**: `E₆`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 91–100, proof body ≈ 9 lines
- **Notes**: Unused anywhere; verbatim 4↔6 twin (10 lines duplicated).

### `def φ₀`
- **Type**: `(z : ℍ) → ℂ`
- **What**: `φ₀ = (E₂E₄ − E₆)² / Δ` (the weight-0 quasi-modular quotient used for Ramanujan-style identities).
- **How**: Direct formula.
- **Hypotheses**: none
- **Uses from project**: `E₂` (E2.lean:21), `E₄`, `E₆`, `Δ` (Delta.lean:26)
- **Used by**: `φ₀''`, `φ₀''_def`, `φ₀''_mem_upperHalfPlane`, `φ₀''_coe_upperHalfPlane`
- **Visibility**: public
- **Lines**: 111, proof body ≈ 0 lines
- **Notes**: Unused anywhere outside the `φ` block. Comment 110 explains the naming (`φ₂'` means `φ₋₂`). No return type annotation (inferred ℂ).

### `def φ₂'`
- **Type**: `(z : ℍ) → ℂ`
- **What**: `φ₋₂ = E₄(E₂E₄ − E₆)/Δ`.
- **How**: Direct formula.
- **Hypotheses**: none
- **Uses from project**: `E₂`, `E₄`, `E₆`, `Δ`
- **Used by**: `φ₂''`
- **Visibility**: public
- **Lines**: 112, proof body ≈ 0 lines
- **Notes**: Unused anywhere else.

### `def φ₄'`
- **Type**: `(z : ℍ) → ℂ`
- **What**: `φ₋₄ = E₄²/Δ`.
- **How**: Direct formula.
- **Hypotheses**: none
- **Uses from project**: `E₄`, `Δ`
- **Used by**: `φ₄''`
- **Visibility**: public
- **Lines**: 113, proof body ≈ 0 lines
- **Notes**: Unused anywhere else.

### `def φ₀''`
- **Type**: `ℂ → ℂ`
- **What**: Extension of `φ₀` by zero to all of ℂ.
- **How**: `if hz : 0 < z.im then φ₀ ⟨z, hz⟩ else 0`.
- **Hypotheses**: none
- **Uses from project**: `φ₀`
- **Used by**: `φ₀''_def`, `φ₀''_mem_upperHalfPlane`, `φ₀''_coe_upperHalfPlane`
- **Visibility**: public
- **Lines**: 115, proof body ≈ 0 lines
- **Notes**: Unused anywhere else. mathlib's idiom for this is `φ₀ ∘ ofComplex` (`UpperHalfPlane.ofComplex`, with `ofComplex_apply_of_im_pos`), used elsewhere in this very file (line 142).

### `def φ₂''`
- **Type**: `ℂ → ℂ`
- **What**: Zero-extension of `φ₂'`.
- **How**: dite on `0 < z.im`.
- **Hypotheses**: none
- **Uses from project**: `φ₂'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 116, proof body ≈ 0 lines
- **Notes**: Unused anywhere.

### `def φ₄''`
- **Type**: `ℂ → ℂ`
- **What**: Zero-extension of `φ₄'`.
- **How**: dite on `0 < z.im`.
- **Hypotheses**: none
- **Uses from project**: `φ₄'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 117, proof body ≈ 0 lines
- **Notes**: Unused anywhere.

### `lemma φ₀''_def`
- **Type**: `{z : ℂ} (hz : 0 < z.im) : φ₀'' z = φ₀ ⟨z, hz⟩`
- **What**: Unfolding on ℍ.
- **How**: `simp [φ₀'', hz]`.
- **Hypotheses**: `0 < im z`.
- **Uses from project**: `φ₀''`, `φ₀`
- **Used by**: `φ₀''_mem_upperHalfPlane`, `φ₀''_coe_upperHalfPlane`
- **Visibility**: public
- **Lines**: 119, proof body ≈ 0 lines
- **Notes**: Missing `@[simp]`.

### `lemma φ₀''_mem_upperHalfPlane`
- **Type**: `{z : ℂ} (hz : z ∈ upperHalfPlaneSet) : φ₀'' z = φ₀ ⟨z, hz⟩`
- **What**: `φ₀''_def` phrased with `upperHalfPlaneSet`.
- **How**: `φ₀''_def hz`.
- **Hypotheses**: `z ∈ upperHalfPlaneSet`.
- **Uses from project**: `φ₀''_def`, `φ₀''`, `φ₀`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 121–122, proof body ≈ 1 line
- **Notes**: Unused anywhere; definitional restatement.

### `lemma φ₀''_coe_upperHalfPlane`
- **Type**: `(z : ℍ) : φ₀'' (z : ℂ) = φ₀ z`
- **What**: `φ₀''` restricted to ℍ is `φ₀`.
- **How**: `φ₀''_def` with `UpperHalfPlane.im_pos`.
- **Hypotheses**: none
- **Uses from project**: `φ₀''_def`, `φ₀''`, `φ₀`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 124–125, proof body ≈ 1 line
- **Notes**: Unused anywhere. Missing `@[simp]`.

### `local notation "𝕢"`
- **Type**: notation for `Periodic.qParam`
- **What**: Abbreviation `𝕢 h z = exp(2πi z / h)`.
- **How**: `local notation`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `cuspfunc_lim_coef`, `modfom_q_exp_cuspfunc`, `qParam_surj_onto_ball`, `q_exp_unique`, `qexpsummable`, `Ek_q_exp`
- **Visibility**: local
- **Lines**: 132
- **Notes**: Same local notation is declared in mathlib `QExpansion.lean:55`, `DedekindEta.lean:36`, `Discriminant.lean:54`.

### `theorem cuspfunc_lim_coef`
- **Type**: `{k : ℤ} {F} [FunLike F ℍ ℂ] (n : ℕ) (c : ℕ → ℂ) (f : F) [ModularFormClass F Γ(n) k] [NeZero n] (hf : ∀ τ, HasSum (fun m ↦ c m • 𝕢 n τ ^ m) (f τ)) (q : ℂ) (hq : ‖q‖ < 1) (hq1 : q ≠ 0) : HasSum (fun m ↦ c m • q ^ m) (cuspFunction n f q)`
- **What**: If a power series in `q` represents `f` on ℍ, it represents `cuspFunction n f` at every nonzero point of the unit disc.
- **How**: Pull `q` back to `τ = invQParam n q ∈ ℍ` (`Periodic.im_invQParam_pos_of_norm_lt_one`), then `Periodic.cuspFunction_eq_of_nonzero` and `Periodic.qParam_right_inv` turn `hf τ` into the claim.
- **Hypotheses**: `f` a modular form of level `n ≠ 0`; `0 < ‖q‖ < 1`.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 135–143, proof body ≈ 5 lines
- **Notes**: Unused anywhere. Exactly mathlib's private `hasSum_cuspFunction_of_hasSum_punctured` (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:230`, stated for any `f : ℍ → ℂ`, `0 < h`); the `ModularFormClass` hypotheses here are unused by the proof. Statement uses `Type u_1` and named instance binders `[inst : …]` (copy-pasted from a goal display).

### `theorem summable_zero_pow`
- **Type**: `{G} [NormedField G] (f : ℕ → G) : Summable fun m ↦ f m * 0 ^ m`
- **What**: `Σ f m · 0^m` is summable (only the `m = 0` term is nonzero).
- **How**: `summable_nat_add_iff 1` + `zero_pow` + `summable_zero`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `tsum_zero_pow`
- **Visibility**: public
- **Lines**: 145–150, proof body ≈ 4 lines
- **Notes**: mathlib: `(hasSum_ite_eq 0 (f 0)).summable` after `zero_pow_eq`/`mul_ite` (`InfiniteSum/Basic.lean:170`, to_additive), or `summable_of_finite_support`. `NormedField` is far stronger than needed (see Generalization).

### `lemma tsum_zero_pow`
- **Type**: `(f : ℕ → ℂ) : (∑' m, f m * 0 ^ m) = f 0`
- **What**: Evaluating a power series at `0` gives the constant term.
- **How**: `Summable.tsum_eq_zero_add` + `summable_zero_pow`.
- **Hypotheses**: none
- **Uses from project**: `summable_zero_pow`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 152–156, proof body ≈ 4 lines
- **Notes**: Unused anywhere. mathlib `tsum_ite_eq` (`InfiniteSum/Basic.lean:503`, to_additive) after `simp [zero_pow_eq]`.

### `lemma cuspfunc_Zero`
- **Type**: `[NeZero n] [ModularFormClass F Γ(n) k] : cuspFunction n f 0 = (qExpansion n f).coeff 0`
- **What**: The constant q-coefficient is the cusp-function value at 0.
- **How**: `simp [qExpansion_coeff]` (`iteratedDeriv_zero`, `Nat.factorial_zero`).
- **Hypotheses**: level `n ≠ 0`.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 159–161, proof body ≈ 1 line
- **Notes**: Unused anywhere. Holds for any `f : ℍ → ℂ` and any `h` (the `ModularFormClass`/`NeZero` hypotheses are unused): it is `by simp [qExpansion_coeff]` from `Mathlib/NumberTheory/ModularForms/QExpansion.lean:169`. Compare mathlib `qExpansion_coeff_zero : (qExpansion h f).coeff 0 = valueAtInfty f` (line 173).

### `lemma modfom_q_exp_cuspfunc`
- **Type**: `(c : ℕ → ℂ) (f : F) [ModularFormClass F Γ(n) k] [NeZero n] (hf : ∀ τ, HasSum (fun m ↦ c m • 𝕢 n τ ^ m) (f τ)) : ∀ q, ‖q‖ < 1 → HasSum (fun m ↦ c m • q ^ m) (cuspFunction n f q)`
- **What**: Same as `cuspfunc_lim_coef` but including `q = 0`.
- **How**: Identify `c` with the canonical coefficients via `ModularFormClass.qExpansion_coeff_unique`, then `hasSum_qExpansion_of_norm_lt` (with `periodic_comp_ofComplex`, `holo`, `bdd_at_infty`).
- **Hypotheses**: as above.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 164–175, proof body ≈ 9 lines
- **Notes**: Unused anywhere. Composite of mathlib `ModularFormClass.qExpansion_coeff_unique` (`QExpansion.lean:701`) and `hasSum_qExpansion_of_norm_lt` (179). Typo `modfom`.

### `lemma qParam_surj_onto_ball`
- **Type**: `(r : ℝ) (hr : 0 < r) (hr2 : r < 1) [NeZero n] : ∃ (z : ℍ), ‖𝕢 n z‖ = r`
- **What**: Every radius in `(0,1)` is attained by `‖𝕢 n z‖` for some `z ∈ ℍ`.
- **How**: `z = invQParam n r`, positivity of its imaginary part from `im_invQParam_pos_of_norm_lt_one`, and `qParam_right_inv`.
- **Hypotheses**: `0 < r < 1`, `n ≠ 0`.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 177–183, proof body ≈ 5 lines
- **Notes**: Unused anywhere. No mathlib analogue found (searched `qParam_surj`, `norm_qParam_eq`, `exists_norm_qParam`); trivial from `Periodic.norm_qParam` (`Analysis/Complex/Periodic.lean:49`) by choosing `im z = -h log r/(2π)`.

### `lemma q_exp_unique`
- **Type**: `(c : ℕ → ℂ) (f : ModularForm Γ(n) k) [NeZero n] (hf : ∀ τ, HasSum (fun m ↦ c m • 𝕢 n τ ^ m) (f τ)) : c = (fun m => (qExpansion n f).coeff m)`
- **What**: Uniqueness of q-expansion coefficients (function-level).
- **How**: `funext` + `ModularFormClass.qExpansion_coeff_unique`.
- **Hypotheses**: level `n ≠ 0`.
- **Uses from project**: `[]`
- **Used by**: `Ek_q_exp`
- **Visibility**: public
- **Lines**: 186–191, proof body ≈ 3 lines
- **Notes**: `funext` wrapper of mathlib `ModularFormClass.qExpansion_coeff_unique` (`QExpansion.lean:701`); the `(by simp)` discharges `(n:ℝ) ∈ Γ(n).strictPeriods`.

### `lemma deriv_mul_eq`
- **Type**: `(f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) : deriv (f * g) = deriv f * g + f * deriv g`
- **What**: Product rule at the function level.
- **How**: `ext; deriv_mul`.
- **Hypotheses**: both globally differentiable.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 193–196, proof body ≈ 2 lines
- **Notes**: Unused anywhere; `funext` of mathlib `deriv_mul`.

### `lemma auxasdf`
- **Type**: `(n : ℕ) : (PowerSeries.coeff n) (qExpansion 1 E₄ * qExpansion 1 E₆) = ∑ p ∈ antidiagonal n, coeff p.1 (qExpansion 1 E₄) * coeff p.2 (qExpansion 1 E₆)`
- **What**: Cauchy product formula specialised to `qExpansion 1 E₄ * qExpansion 1 E₆`.
- **How**: `PowerSeries.coeff_mul`.
- **Hypotheses**: none
- **Uses from project**: `E₄`, `E₆`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 198–201, proof body ≈ 1 line
- **Notes**: Unused anywhere; a needless specialisation of `PowerSeries.coeff_mul`. Placeholder name.

### `lemma sigma_bound`
- **Type**: `(k n : ℕ) : σ k n ≤ n ^ (k + 1)`
- **What**: Trivial bound on the divisor function.
- **How**: `ArithmeticFunction.sigma_le_pow_succ`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `E_even_imag_axis_real`
- **Visibility**: public
- **Lines**: 203–204, proof body ≈ 1 line
- **Notes**: Verbatim wrapper of mathlib `ArithmeticFunction.sigma_le_pow_succ` (`Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:213`); `qexpsummable` (line 217) already calls the mathlib name directly.

### `def Ek_q`
- **Type**: `(k : ℕ) → ℕ → ℂ`
- **What**: The candidate q-coefficients of `E_k`: `1` at `m = 0`, else `(1/ζ(k))·((−2πi)^k/(k−1)!)·σ_{k−1}(m)`.
- **How**: `if m = 0 then 1 else …`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `qexpsummable`, `Ek_q_exp` (via `simp [c, Ek_q]`)
- **Visibility**: public
- **Lines**: 206–207, proof body ≈ 0 lines
- **Notes**: `Ek_q_exp` re-declares the same function as a local `c` (231–232) instead of using `Ek_q`, then unfolds both. mathlib states the coefficients directly in `E_qExpansion_coeff` (`EisensteinSeries/QExpansion.lean:324`) as `-(2k/B_k) σ_{k-1}(m)`.

### `lemma qexpsummable`
- **Type**: `(k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) : Summable fun m ↦ Ek_q k m • 𝕢 1 z ^ m`
- **What**: The candidate q-series converges on ℍ.
- **How**: Dominate `σ_{k−1}(m) qᵐ` by `m^k ‖q‖^m` (`sigma_le_pow_succ`, `Summable.of_norm_bounded` against `summable_norm_pow_mul_geometric_of_norm_lt_one k (norm_exp_two_pi_I_lt_one z)`), then shift by one (`summable_nat_add_iff`) and `mul_left`.
- **Hypotheses**: `3 ≤ k`.
- **Uses from project**: `Ek_q`
- **Used by**: `Ek_q_exp`
- **Visibility**: public
- **Lines**: 209–220, proof body ≈ 10 lines
- **Notes**: Hand-rolled summability; mathlib's private `summable_sigma_mul_cexp_pow` (`EisensteinSeries/QExpansion.lean:312`) is the same argument, and the public `summable_pow_mul_cexp` (line 192) gives the majorant. `summable_norm_pow_mul_geometric_of_norm_lt_one` is `Analysis/SpecificLimits/Normed.lean:423`.

### `lemma Ek_q_exp_zero`
- **Type**: `(k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) : (qExpansion 1 (E k hk)).coeff 0 = 1`
- **What**: Constant term of `E_k` is 1.
- **How**: Transport of mathlib `E_qExpansion_coeff_zero` through the `E`/`ModularForm.E` unfolding.
- **Hypotheses**: `3 ≤ k`, `k` even.
- **Uses from project**: `E`, `standardcongruencecondition`
- **Used by**: `Ek_ne_zero`
- **Visibility**: public
- **Lines**: 222–225, proof body ≈ 2 lines
- **Notes**: mathlib `EisensteinSeries.E_qExpansion_coeff_zero` (`EisensteinSeries/QExpansion.lean:348`).

### `lemma Ek_q_exp`
- **Type**: `(k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) : (fun m => (qExpansion 1 (E k hk)).coeff m) = fun m => if m = 0 then 1 else (1/ζ(k))·((−2πi)^k/(k−1)!)·σ(k−1) m`
- **What**: All q-coefficients of `E_k` (ζ-normalised form).
- **How**: `q_exp_unique` reduces to `HasSum (c m • qᵐ) (E_k z)`; `E_k_q_expansion` gives the value; `tsum_eq_zero_add'` + `tsum_pnat_eq_tsum_succ` split off `m = 0`; summability from `qexpsummable`; `tsum_mul_left`, `Complex.exp_nsmul`, `ring_nf`/`field_simp` match the terms.
- **Hypotheses**: `3 ≤ k`, `k` even.
- **Uses from project**: `q_exp_unique`, `E_k_q_expansion` (Eisensteinqexpansions.lean:149), `qexpsummable`, `Ek_q`, `E`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 227–263, proof body ≈ 33 lines
- **Notes**: Proof >30 lines; unused anywhere. mathlib `EisensteinSeries.E_qExpansion_coeff` (`EisensteinSeries/QExpansion.lean:324`) has the identical proof shape (`qExpansion_coeff_unique` + `hasSum_nat_add_iff' 1` + `tsum_pnat_eq_tsum_succ`) with the Bernoulli-form constant; the ζ-form here differs from mathlib's by `q_expansion_riemannZeta` vs `q_expansion_bernoulli` (lines 276/299). Proof uses `simp at *` (238, 241, 256, 259, 262) five times and a `have V := …; rw [← V]` on a `simp`-normalised statement — fragile.

### `lemma E4_q_exp`
- **Type**: `(fun m => (qExpansion 1 E₄).coeff m) = fun m => if m = 0 then 1 else (240 : ℂ) * σ 3 m`
- **What**: `E₄ = 1 + 240 Σ σ₃(m) qᵐ`.
- **How**: mathlib `E_qExpansion_coeff` with `k = 4` and `bernoulli 4 = −1/30` (`bernoulli_eq_bernoulli'_of_ne_one` + `bernoulli'_four`), `norm_num`.
- **Hypotheses**: none
- **Uses from project**: `E₄`, `standardcongruencecondition`
- **Used by**: `E4_q_exp_zero`, `E4_q_exp_one`
- **Visibility**: public
- **Lines**: 265–270, proof body ≈ 4 lines
- **Notes**: mathlib has the `m = 1` instance `E₄_qExpansion_coeff_one : (qExpansion 1 E₄).coeff 1 = 240` (`LevelOne/DimensionFormula.lean:203`) but not the all-`m` closed form for `E₄` specifically — this lemma is a reasonable specialisation.

### `lemma E4_q_exp_zero`
- **Type**: `(qExpansion 1 E₄).coeff 0 = 1`
- **What**: Constant term of `E₄`.
- **How**: `congr_fun E4_q_exp 0`.
- **Hypotheses**: none
- **Uses from project**: `E4_q_exp`, `E₄`
- **Used by**: `E4E6_coeff_zero_eq_zero`, `E4_pow_q_exp_one`
- **Visibility**: public
- **Lines**: 272–273, proof body ≈ 1 line
- **Notes**: Also `Ek_q_exp_zero 4 _ _` / mathlib `E_qExpansion_coeff_zero`.

### `theorem Complex.I_pow_six`
- **Type**: `Complex.I ^ 6 = -1`
- **What**: `i⁶ = −1`.
- **How**: `pow_mul` + `I_sq`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: unused directly (may fire inside `norm_num` in `E6_q_exp` via `@[simp]`)
- **Visibility**: public
- **Lines**: 276–279, proof body ≈ 2 lines
- **Notes**: `@[simp]`. mathlib has `Complex.I_pow_four` (`Mathlib/Data/Complex/Basic.lean:617`) and `I_pow_eq_pow_mod` (619); `I ^ 6` is `by simp [I_pow_eq_pow_mod]`. Declared in the `Complex` namespace from a project file. Unused anywhere by name.

### `theorem bernoulli'_five`
- **Type**: `bernoulli' 5 = 0`
- **What**: The fifth Bernoulli number vanishes.
- **How**: `bernoulli'_def` + `Finset.sum_range_succ` unrolling + `Nat.choose 5 2 = 10` by `decide`, `norm_num`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 281–285, proof body ≈ 3 lines
- **Notes**: `@[simp]`. mathlib stops at `bernoulli'_four` (`Mathlib/NumberTheory/Bernoulli.lean:135`); `bernoulli'_five`/`bernoulli'_six` are genuine small mathlib candidates (mathlib also has `bernoulli'_odd_eq_zero` for the general odd case, which covers `5`). Unused anywhere by name.

### `theorem bernoulli'_six`
- **Type**: `bernoulli' 6 = 1 / 42`
- **What**: `B₆ = 1/42`.
- **How**: Same unrolling with `choose 6 4 = choose 6 2 = 15` by `decide`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `E6_q_exp` (implicitly, via the `@[simp]` set inside `norm_num [bernoulli_eq_bernoulli'_of_ne_one]`)
- **Visibility**: public
- **Lines**: 287–292, proof body ≈ 4 lines
- **Notes**: `@[simp]`. Externally used by `jFunction/Deltaqexpansions.lean` and `Cox/LatticeJ.lean`. Comments `-- shrug` (289, 290). Not in mathlib (grep `bernoulli'_six`: none).

### `lemma E6_q_exp`
- **Type**: `(fun m => (qExpansion 1 E₆).coeff m) = fun m => if m = 0 then 1 else -(504 : ℂ) * σ 5 m`
- **What**: `E₆ = 1 − 504 Σ σ₅(m) qᵐ`.
- **How**: As `E4_q_exp` with `bernoulli 6 = 1/42`.
- **Hypotheses**: none
- **Uses from project**: `E₆`, `standardcongruencecondition`, `bernoulli'_six` (simp)
- **Used by**: `E6_q_exp_zero`, `E6_q_exp_one`
- **Visibility**: public
- **Lines**: 294–299, proof body ≈ 4 lines
- **Notes**: 4↔6 twin of `E4_q_exp`. mathlib `E₆_qExpansion_coeff_one` (`DimensionFormula.lean:206`).

### `lemma E6_q_exp_zero`
- **Type**: `(qExpansion 1 E₆).coeff 0 = 1`
- **What**: Constant term of `E₆`.
- **How**: `congr_fun E6_q_exp 0`.
- **Hypotheses**: none
- **Uses from project**: `E6_q_exp`, `E₆`
- **Used by**: `E4E6_coeff_zero_eq_zero`
- **Visibility**: public
- **Lines**: 301–302, proof body ≈ 1 line
- **Notes**: 4↔6 twin.

### `theorem E4E6_coeff_zero_eq_zero`
- **Type**: `(PowerSeries.coeff 0) (qExpansion 1 ((1/1728 : ℂ) • ((DirectSum.of (ModularForm Γ(1)) 4 E₄ ^ 3 − DirectSum.of _ 6 E₆ ^ 2) 12)) = 0`
- **What**: `(E₄³ − E₆²)/1728` has vanishing constant term (so it is a cusp form).
- **How**: `ModularForm.directSum_of_pow` turns the graded expression into `E₄.pow 3 − E₆.pow 2`; `qExpansion_smul`/`qExpansion_sub`/`qExpansion_pow` (needing `analyticAt_cuspFunction_zero`, `cuspFunction_sub`) reduce to `1³ − 1² = 0` from `E4_q_exp_zero`, `E6_q_exp_zero`.
- **Hypotheses**: none
- **Uses from project**: `E₄`, `E₆`, `E4_q_exp_zero`, `E6_q_exp_zero`
- **Used by**: `Delta_E4_E6_aux`
- **Visibility**: public
- **Lines**: 304–324, proof body ≈ 15 lines
- **Notes**: mathlib: private `E₄CubeSubE₆SqForm_isCuspForm` (`LevelOne/GradedRing.lean:46`) proves the same for the same form; `directSum_of_pow` is `ModularForms/Basic.lean:647`; `qExpansion_smul/sub/pow` are `QExpansion.lean:477,494,603`.

### `def Delta_E4_E6_aux`
- **Type**: `CuspForm (CongruenceSubgroup.Gamma 1) 12`
- **What**: The cusp form `(E₄³ − E₆²)/1728` (which equals `Δ`).
- **How**: `cuspFormOfCoeffZero` applied to the graded-ring element with `E4E6_coeff_zero_eq_zero`.
- **Hypotheses**: none
- **Uses from project**: `E₄`, `E₆`, `E4E6_coeff_zero_eq_zero`, `cuspFormOfCoeffZero` (IsCuspForm.lean:123)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 326–329, proof body ≈ 3 lines
- **Notes**: Externally used by `DimensionFormulas.lean:120,131,143,148` (`Delta_E4_eqn : Delta = Delta_E4_E6_aux`). mathlib: private `E₄CubeSubE₆SqForm` (`GradedRing.lean:31`) and the public theorem `discriminant_eq_E₄_cube_sub_E₆_sq (z) : Δ z = (E₄ z ^ 3 − E₆ z ^ 2)/1728` (`GradedRing.lean:59`) plus graded form (78). `cuspFormOfCoeffZero` = mathlib `ModularForm.toCuspForm` (`CuspFormSubmodule.lean:127`).

### `lemma Delta_cuspFuntion_eq`
- **Type**: `Set.EqOn (cuspFunction 1 Delta) (fun y => y * ∏' i, (1 − y^(i+1))^24) (Metric.ball 0 (1/2))`
- **What**: The cusp function of `Δ` is `q ∏(1−qⁿ)²⁴` near `0`.
- **How**: `funext Delta_eq_eta_pow` + mathlib `discriminant_cuspFunction_eqOn.mono (ball_subset_ball _)`.
- **Hypotheses**: none
- **Uses from project**: `Delta` (Delta.lean:170), `Delta_eq_eta_pow` (Delta.lean:36)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 331–335, proof body ≈ 3 lines
- **Notes**: Unused anywhere. Typo `cuspFuntion`. mathlib `discriminant_cuspFunction_eqOn` (`Discriminant.lean:197`) holds on the full unit ball, so the restriction to `ball 0 (1/2)` is a weakening.

### `lemma Delta_ne_zero`
- **Type**: `Delta ≠ 0`
- **What**: The cusp form `Δ` is not the zero form.
- **How**: `DFunLike.ne_iff` with witness `UpperHalfPlane.I` and `Δ_ne_zero`.
- **Hypotheses**: none
- **Uses from project**: `Delta`, `Δ_ne_zero` (Delta.lean:44)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 337–340, proof body ≈ 3 lines
- **Notes**: Unused anywhere; mathlib does the same inline at `DimensionFormula.lean:165` (`DFunLike.ne_iff.mpr ⟨I, discriminant_ne_zero _⟩`).

### `lemma asdf`
- **Type**: `TendstoLocallyUniformlyOn (fun n y => ∏ x ∈ range n, (1 − y^(x+1))) (fun x => ∏' i, (1 − x^(i+1))) atTop (Metric.ball 0 (1/2))`
- **What**: Partial products of `∏(1 − qⁿ⁺¹)` converge locally uniformly on `|q| < 1/2`.
- **How**: Uniform convergence on the compact `closedBall 0 (1/2)` via `Summable.hasProdUniformlyOn_nat_one_add` with geometric majorant `(1/2)^(n+1)` (`pow_le_pow_left₀`), then `tendstoUniformlyOn_finsetRange` and `.mono ball_subset_closedBall`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 342–366, proof body ≈ 20 lines
- **Notes**: Unused anywhere. Placeholder name. mathlib `ModularForm.multipliableLocallyUniformlyOn_one_sub_pow` (`DedekindEta.lean:73`) proves `MultipliableLocallyUniformlyOn (fun n q ↦ 1 − q^(n+1)) (ball 0 1)`; `.hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange` (`Topology/Algebra/InfiniteSum/UniformOn.lean:281`) gives this statement on the whole unit ball in one line. `hasProdUniformlyOn_nat_one_add` is `Analysis/Normed/Module/MultipliableUniformlyOn.lean:112`.

### `theorem diffwithinat_prod_1`
- **Type**: `DifferentiableWithinAt ℂ (fun y ↦ ∏' i, (1 − y^(i+1))^24) (ball 0 (1/2)) 0`
- **What**: The 24th-power product is differentiable at `0` within the half-ball.
- **How**: mathlib `differentiableOn_tprod_one_sub_pow_pow 24` at the interior point `0`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 368–372, proof body ≈ 2 lines
- **Notes**: Unused anywhere; wrapper of `ModularForm.differentiableOn_tprod_one_sub_pow_pow` (`DedekindEta.lean:97`).

### `lemma Delta_q_one_term`
- **Type**: `(qExpansion 1 Delta).coeff 1 = 1`
- **What**: `Δ = q + O(q²)`.
- **How**: `funext Delta_eq_eta_pow` + mathlib `discriminant_qExpansion_coeff_one`.
- **Hypotheses**: none
- **Uses from project**: `Delta`, `Delta_eq_eta_pow`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 374–377, proof body ≈ 3 lines
- **Notes**: Externally used by `DimensionFormulas.lean`, `qExpansion_tactic/link.lean`, `jFunction/jfunction.lean`. Wrapper of `ModularForm.discriminant_qExpansion_coeff_one` (`Discriminant.lean:210`). The `heq` proof is duplicated from `Delta_cuspFuntion_eq` (line 333).

### `lemma E4_q_exp_one`
- **Type**: `(qExpansion 1 E₄).coeff 1 = 240`
- **What**: First coefficient of `E₄`.
- **How**: `congr_fun E4_q_exp 1`.
- **Hypotheses**: none
- **Uses from project**: `E4_q_exp`, `E₄`
- **Used by**: `E4_pow_q_exp_one`
- **Visibility**: public
- **Lines**: 383–384, proof body ≈ 1 line
- **Notes**: mathlib `E₄_qExpansion_coeff_one` (`LevelOne/DimensionFormula.lean:203`). Preceded by dead `variable {α β γ : Type*}` / `variable [CommMonoid α] [TopologicalSpace α] [UniformSpace α]` (379–381) which nothing uses (and `TopologicalSpace α` + `UniformSpace α` together would be an instance clash if used).

### `lemma E6_q_exp_one`
- **Type**: `(qExpansion 1 E₆).coeff 1 = -504`
- **What**: First coefficient of `E₆`.
- **How**: `congr_fun E6_q_exp 1`.
- **Hypotheses**: none
- **Uses from project**: `E6_q_exp`, `E₆`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 386–387, proof body ≈ 1 line
- **Notes**: Unused anywhere; mathlib `E₆_qExpansion_coeff_one` (`DimensionFormula.lean:206`).

### `lemma antidiagonal_one`
- **Type**: `Finset.antidiagonal 1 = {(1,0), (0,1)}`
- **What**: The two pairs summing to 1.
- **How**: `ext ⟨x,y⟩; simp; omega`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `E4_pow_q_exp_one`
- **Visibility**: public
- **Lines**: 389–392, proof body ≈ 3 lines
- **Notes**: mathlib `Finset.Nat.antidiagonal_succ` (`Mathlib/Data/Finset/NatAntidiagonal.lean:67`) + `antidiagonal_zero` (65) — mathlib computes exactly this `E₄³` coefficient with `norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one, …]` at `GradedRing.lean:54`. Not `@[simp]`, in the root namespace.

### `lemma E4_pow_q_exp_one`
- **Type**: `(qExpansion 1 ((E₄).mul ((E₄).mul E₄))).coeff 1 = 3 * 240`
- **What**: `q`-coefficient of `E₄³` is `720`.
- **How**: `qExpansion_mul_coeff` twice, `PowerSeries.coeff_mul`, `antidiagonal_one`, `E4_q_exp_one`, `E4_q_exp_zero`, `ring`.
- **Hypotheses**: none
- **Uses from project**: `E₄`, `qExpansion_mul_coeff` (qExpansion_lems.lean:53), `antidiagonal_one`, `E4_q_exp_one`, `E4_q_exp_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 394–402, proof body ≈ 8 lines
- **Notes**: Unused anywhere. States the cube as `E₄.mul (E₄.mul E₄)` rather than `E₄.pow 3` / `DirectSum` power used at 307; mathlib's private `E₄CubeSubE₆SqForm_qExpansion_coeff_one` (`GradedRing.lean:51`) is the same computation.

### `lemma Ek_ne_zero`
- **Type**: `(k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) : E k hk ≠ 0`
- **What**: `E_k ≠ 0` (its constant term is 1).
- **How**: If `E k = 0` then `qExpansion_zero` gives constant coefficient `0`, contradicting `Ek_q_exp_zero`.
- **Hypotheses**: `3 ≤ k`, `k` even.
- **Uses from project**: `E`, `Ek_q_exp_zero`
- **Used by**: `E4_ne_zero`, `E6_ne_zero`
- **Visibility**: public
- **Lines**: 404–413, proof body ≈ 9 lines
- **Notes**: mathlib `EisensteinSeries.E_ne_zero` (`EisensteinSeries/QExpansion.lean:353`), a 1-line proof of the same statement for `ModularForm.E`. Stale comment 415 ("This is in the mod forms repo").

### `lemma E4_ne_zero`
- **Type**: `E₄ ≠ 0`
- **What**: `E₄` is nonzero.
- **How**: `Ek_ne_zero 4`.
- **Hypotheses**: none
- **Uses from project**: `Ek_ne_zero`, `E₄`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 416–417, proof body ≈ 1 line
- **Notes**: Unused anywhere. mathlib uses `E_ne_zero _ ⟨2, rfl⟩` inline (`DimensionFormula.lean:226`).

### `lemma E6_ne_zero`
- **Type**: `E₆ ≠ 0`
- **What**: `E₆` is nonzero.
- **How**: `Ek_ne_zero 6`.
- **Hypotheses**: none
- **Uses from project**: `Ek_ne_zero`, `E₆`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 419–420, proof body ≈ 1 line
- **Notes**: Unused anywhere; 4↔6 twin, mis-indented (4 spaces).

### `lemma modularForm_normalise`
- **Type**: `(f : ModularForm Γ(1) k) (hf : ¬ IsCuspForm Γ(1) k f) : (qExpansion 1 (((qExpansion 1 f).coeff 0)⁻¹ • f)).coeff 0 = 1`
- **What**: A non-cusp form can be rescaled to have constant term 1.
- **How**: `qExpansion_smul2` (project) moves the scalar out, `inv_mul_cancel₀` with non-vanishing from `IsCuspForm_iff_coeffZero_eq_zero`.
- **Hypotheses**: `f` not a cusp form.
- **Uses from project**: `qExpansion_smul2` (qExpansion_lems.lean:68), `IsCuspForm` (IsCuspForm.lean:81), `IsCuspForm_iff_coeffZero_eq_zero` (IsCuspForm.lean:134)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 422–428, proof body ≈ 6 lines
- **Notes**: Unused anywhere. mathlib: `ModularForm.IsCuspForm` and `isCuspForm_iff_coeffZero_eq_zero` (`CuspFormSubmodule.lean:73,136`), `ModularFormClass.qExpansion_smul` (`QExpansion.lean:556`). The `rw [← Nat.cast_one (R := ℝ), …, Nat.cast_one]` dance (424) is a cast workaround also seen at 234 and 395.

### `lemma PowerSeries.coeff_add`
- **Type**: `(f g : PowerSeries ℂ) (n : ℕ) : (f + g).coeff n = f.coeff n + g.coeff n`
- **What**: Coefficients are additive.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 430–432, proof body ≈ 1 line
- **Notes**: Unused anywhere (external `coeff_add` hits in `Cox/*` are `HahnSeries.coeff_add`/`Polynomial.coeff_add`). mathlib has no `PowerSeries.coeff_add` by that name because `PowerSeries.coeff n` is an `R`-linear map, so `map_add` (and `simp`) already do this; declaring it in the `PowerSeries` namespace from a project file is a name-squat risk.

### `lemma neg_two_pi_I_pow_even_real`
- **Type**: `(k : ℕ) (hk : Even k) : ((-2 * Real.pi * Complex.I) ^ k : ℂ).im = 0`
- **What**: `(−2πi)^k` is real for even `k`.
- **How**: Split as `(−2π)^k · i^k`; `i^{2m} = (−1)^m` via `pow_mul`, `I_sq`, `Even.neg_one_pow`/`Odd.neg_one_pow`.
- **Hypotheses**: `k` even.
- **Uses from project**: `[]`
- **Used by**: `E_even_imag_axis_real`
- **Visibility**: public
- **Lines**: 447–457, proof body ≈ 9 lines
- **Notes**: No direct mathlib lemma (searched `I_pow_even`, `im_I_pow`); `Complex.I_pow_eq_pow_mod` + `Even` case split would shorten it. Unused outside this file.

### `lemma exp_imag_axis_arg`
- **Type**: `(t : ℝ) (ht : 0 < t) (n : ℕ+) : 2 * π * I * (⟨I * t, _⟩ : ℍ) * n = (-(2 * π * n * t) : ℝ)`
- **What**: On `z = it` the exponent `2πi z n` is the real number `−2πnt`.
- **How**: `push_cast; ring_nf; simp [I_sq]; ring`.
- **Hypotheses**: `0 < t` (only to build the point of ℍ).
- **Uses from project**: `[]`
- **Used by**: `E_even_imag_axis_real`, `E₂_imag_axis_real`
- **Visibility**: public
- **Lines**: 461–467, proof body ≈ 4 lines
- **Notes**: Same computation as `Delta.lean:cexp_aux1/cexp_aux2` and the `hArg` in `Delta_imag_axis_real` (Delta.lean:333–338). `E₂_imag_axis_real` needs it with the factors in a different order and re-normalises with `simpa [mul_assoc, mul_left_comm, mul_comm]` (555).

### `theorem E_even_imag_axis_real`
- **Type**: `(k : ℕ) (hk : (3 : ℤ) ≤ k) (hk2 : Even k) : ResToImagAxis.Real (E k hk).toFun`
- **What**: `E_k(it) ∈ ℝ` for `t > 0`, even `k ≥ 4`.
- **How**: q-expansion `E_k_q_expansion`; each term `σ_{k−1}(n) e^{−2πnt}` is real (`exp_imag_axis_arg`, `exp_ofReal_im`); the series is summable (dominated by `n^k e^{−2πnt}` via `sigma_bound` and project `a33`), so `Complex.im_tsum` gives `im Σ = 0`; the prefactor `(1/ζ(k))·(−2πi)^k/(k−1)!` is real by `riemannZeta_im_eq_zero_of_one_lt` and `neg_two_pi_I_pow_even_real`; finish with `mul_im`/`div_im`.
- **Hypotheses**: `3 ≤ k`, `k` even.
- **Uses from project**: `E`, `E_k_q_expansion`, `exp_imag_axis_arg`, `sigma_bound`, `a33` (Summability/Basic.lean:107), `neg_two_pi_I_pow_even_real`, `ResToImagAxis.Real` (ResToImagAxis.lean:53), `resToImagAxis`
- **Used by**: `E₄_imag_axis_real`, `E₆_imag_axis_real`
- **Visibility**: public
- **Lines**: 471–526, proof body ≈ 54 lines
- **Notes**: Proof >30 lines. `Complex.im_tsum` is `Mathlib/Analysis/Complex/Basic.lean:612`; `riemannZeta_im_eq_zero_of_one_lt` is `Mathlib/NumberTheory/LSeries/Dirichlet.lean:347`. The summability block (491–510, 20 lines) re-proves the bound already established in `qexpsummable` (209–220) and in mathlib's `summable_pow_mul_cexp` (`EisensteinSeries/QExpansion.lean:192`); a `calc` with `norm_mul` twice could be `gcongr`. Stated for `(E k hk).toFun` rather than `⇑(E k hk)`.

### `theorem E₄_imag_axis_real`
- **Type**: `ResToImagAxis.Real E₄.toFun`
- **What**: `E₄(it)` is real.
- **How**: `E_even_imag_axis_real 4`.
- **Hypotheses**: none
- **Uses from project**: `E_even_imag_axis_real`, `E₄`, `ResToImagAxis.Real`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 530–531, proof body ≈ 1 line
- **Notes**: `@[fun_prop]` (on a `Prop`-valued predicate `ResToImagAxis.Real`, itself tagged `@[fun_prop]` in ResToImagAxis.lean:52). Unused anywhere.

### `theorem E₆_imag_axis_real`
- **Type**: `ResToImagAxis.Real E₆.toFun`
- **What**: `E₆(it)` is real.
- **How**: `E_even_imag_axis_real 6`.
- **Hypotheses**: none
- **Uses from project**: `E_even_imag_axis_real`, `E₆`, `ResToImagAxis.Real`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 535–536, proof body ≈ 1 line
- **Notes**: `@[fun_prop]`. Unused anywhere.

### `theorem E₂_imag_axis_real`
- **Type**: `ResToImagAxis.Real E₂`
- **What**: `E₂(it)` is real.
- **How**: Lambert form `E₂_eq`; each term `n e^{−2πnt}/(1 − e^{−2πnt})` is real (`exp_imag_axis_arg`, `div_im`); summability from `summable_norm_pow_mul_geometric_div_one_sub 1` (with `‖q‖ < 1` from project `exp_upperHalfPlane_lt_one`) transported along `PNat.coe_injective`; `Complex.im_tsum`; `mul_im`.
- **Hypotheses**: none
- **Uses from project**: `E₂` (E2.lean:21), `E₂_eq` (E2.lean:104), `exp_imag_axis_arg`, `exp_upperHalfPlane_lt_one` (exp_lems.lean:14), `ResToImagAxis.Real`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 540–584, proof body ≈ 43 lines
- **Notes**: Proof >30 lines; `@[fun_prop]`; unused anywhere. `summable_norm_pow_mul_geometric_div_one_sub` is `Mathlib/NumberTheory/TsumDivisorsAntidiagonal.lean:69`; `exp_upperHalfPlane_lt_one` is a project wrapper of mathlib `UpperHalfPlane.norm_exp_two_pi_I_lt_one` (`Analysis/Complex/UpperHalfPlane/Exp.lean:43`). Steps 1–3 (549–582) are the same skeleton as `E_even_imag_axis_real` 482–515 and `Delta_imag_axis_real` (Delta.lean:339–351).

### `lemma norm_exp_two_pi_I_le_exp_neg_two_pi`
- **Type**: `(z : ℍ) (hz : 1 ≤ z.im) : ‖cexp (2 * π * I * z)‖ ≤ Real.exp (-2 * π)`
- **What**: `|q| ≤ e^{−2π}` when `im z ≥ 1`.
- **How**: `Complex.norm_exp`, compute `re(2πi z) = −2π im z`, `Real.exp_le_exp`, `nlinarith [pi_pos]`.
- **Hypotheses**: `1 ≤ im z`.
- **Uses from project**: `[]`
- **Used by**: `E₂_isBoundedAtImInfty`
- **Visibility**: public
- **Lines**: 593–599, proof body ≈ 5 lines
- **Notes**: mathlib has the `im ≥ 1/2` variant `Function.Periodic.norm_qParam_le_of_one_half_le_im : ‖𝕢 1 ξ‖ ≤ rexp (-π)` (`UpperHalfPlane/Exp.lean:32`) and the exact formula `Periodic.norm_qParam : ‖𝕢 h z‖ = rexp (-2π im z / h)` (`Analysis/Complex/Periodic.lean:49`), from which this is `exp_le_exp.mpr (by nlinarith)`. Unused outside this file.

### `lemma norm_tsum_logDeriv_expo_le`
- **Type**: `{q : ℂ} (hq : ‖q‖ < 1) : ‖∑' n : ℕ+, (n : ℂ) * q ^ n / (1 - q ^ n)‖ ≤ ‖q‖ / (1 - ‖q‖) ^ 3`
- **What**: Explicit bound for the Lambert series `Σ n qⁿ/(1−qⁿ)` on the unit disc.
- **How**: Termwise `|n qⁿ/(1−qⁿ)| ≤ n rⁿ/(1−r)` with `r = ‖q‖` (denominator bound `1 − r ≤ 1 − rⁿ ≤ |1 − qⁿ|` via `pow_le_of_le_one` and `norm_sub_norm_le`); majorant summable from `summable_pow_mul_geometric_of_norm_lt_one 1`; `norm_tsum_le_tsum_norm` + `Summable.tsum_le_tsum`; the majorant sums to `r/(1−r)³` by project `tsum_pnat_coe_mul_geometric` (`Σ n rⁿ = r/(1−r)²`).
- **Hypotheses**: `‖q‖ < 1`.
- **Uses from project**: `tsum_pnat_coe_mul_geometric` (Summability/Basic.lean:66)
- **Used by**: `norm_tsum_logDeriv_expo_le_of_norm_le`
- **Visibility**: public
- **Lines**: 609–640, proof body ≈ 31 lines
- **Notes**: Proof >30 lines. Hand-rolled majorant argument; the summability half duplicates mathlib `summable_norm_pow_mul_geometric_div_one_sub 1 hq` (`TsumDivisorsAntidiagonal.lean:69`, whose proof contains the same `1 − ‖r‖ ≤ ‖1 − rⁿ‖` estimate), but the explicit numeric bound `r/(1−r)³` is not in mathlib (searched `tsum_pow_div_one_sub`, `norm_tsum_le` in `TsumDivisorsAntidiagonal.lean`, `EisensteinSeries/E2/*`). Docstring good. Unused outside this file.

### `lemma norm_tsum_logDeriv_expo_le_of_norm_le`
- **Type**: `{q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (hr : r < 1) : ‖∑' n : ℕ+, n * q ^ n / (1 - q ^ n)‖ ≤ r / (1 - r) ^ 3`
- **What**: Monotone version of the previous bound.
- **How**: `norm_tsum_logDeriv_expo_le` + monotonicity of `x ↦ x/(1−x)³` by `gcongr`.
- **Hypotheses**: `‖q‖ ≤ r < 1`.
- **Uses from project**: `norm_tsum_logDeriv_expo_le`
- **Used by**: `E₂_isBoundedAtImInfty`
- **Visibility**: public
- **Lines**: 644–653, proof body ≈ 8 lines
- **Notes**: Unused outside this file.

### `lemma E₂_isBoundedAtImInfty`
- **Type**: `IsBoundedAtImInfty E₂`
- **What**: `E₂` is bounded as `im z → ∞`.
- **How**: `isBoundedAtImInfty_iff` with bound `1 + 24 r₀/(1−r₀)³`, `r₀ = e^{−2π}`, valid for `im z ≥ 1`: rewrite `E₂_eq`, identify `exp(2πi n z) = qⁿ` (`Complex.exp_nat_mul`), `norm_sub_le`, and `norm_tsum_logDeriv_expo_le_of_norm_le` with `norm_exp_two_pi_I_le_exp_neg_two_pi`.
- **Hypotheses**: none
- **Uses from project**: `E₂`, `E₂_eq`, `norm_exp_two_pi_I_le_exp_neg_two_pi`, `norm_tsum_logDeriv_expo_le_of_norm_le`
- **Used by**: `E₂_mul_E₄_isBoundedAtImInfty`
- **Visibility**: public
- **Lines**: 660–684, proof body ≈ 23 lines
- **Notes**: No mathlib analogue (searched `E2` + `IsBoundedAtImInfty`/`isBigO` in `EisensteinSeries/E2/*`, `DedekindEta.lean`, `Discriminant.lean`): a genuine addition. Alternative shorter route: `E2 = 1 − 24 Σ σ₁(n) qⁿ` (`E2_eq_tsum_cexp`) and `qParam_tendsto_atImInfty` give continuity of the cusp function at 0, hence boundedness, without the explicit constant. `isBoundedAtImInfty_iff` is `UpperHalfPlane/FunctionsBoundedAtInfty.lean:65`. Unused outside this file.

### `lemma E₄_isBoundedAtImInfty`
- **Type**: `IsBoundedAtImInfty E₄.toFun`
- **What**: `E₄` is bounded at `i∞` (it is a modular form).
- **How**: `ModularFormClass.bdd_at_infty E₄`.
- **Hypotheses**: none
- **Uses from project**: `E₄`
- **Used by**: `E₂_mul_E₄_isBoundedAtImInfty`
- **Visibility**: public
- **Lines**: 687–688, proof body ≈ 1 line
- **Notes**: One-line wrapper; unused outside this file.

### `lemma E₂_mul_E₄_isBoundedAtImInfty`
- **Type**: `IsBoundedAtImInfty (E₂ * E₄.toFun)`
- **What**: `E₂E₄` is bounded at `i∞`.
- **How**: `IsBoundedAtImInfty.mul` (= `BoundedAtFilter.mul`).
- **Hypotheses**: none
- **Uses from project**: `E₂`, `E₄`, `E₂_isBoundedAtImInfty`, `E₄_isBoundedAtImInfty`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 691–692, proof body ≈ 1 line
- **Notes**: Unused anywhere. `BoundedAtFilter.mul` is `Mathlib/Order/Filter/ZeroAndBoundedAtFilter.lean:101`. Presumably intended for `φ₂'`-type quotients (`E₂E₄ − E₆`), which are dead.

## File Summary
- Total declarations: 72 (12 defs: `E₄`, `E₆`, `φ₀`, `φ₂'`, `φ₄'`, `φ₀''`, `φ₂''`, `φ₄''`, `Ek_q`, `Delta_E4_E6_aux`, plus 0 instances; 59 lemmas/theorems; 1 other: `local notation "𝕢"`)
- Key API (used by 3+ others in the file): `E₄` (16), `E₆` (12), `φ₀` (4), `E4_q_exp_zero` (2), `exp_imag_axis_arg` (2), `E_even_imag_axis_real` (2)
- Unused declarations (not used by anything in this file): `exists_smul_eq_of_rank_one`, `exists_smul_eq_of_rank_one'`, `smul_modularForm_eq_pointwise`, `E4_eq`, `E6_eq`, `E4_apply`, `E6_apply`, `E₄_periodic`, `E₆_periodic`, `E₄_S_transform`, `E₆_S_transform`, `φ₂''`, `φ₄''`, `φ₀''_mem_upperHalfPlane`, `φ₀''_coe_upperHalfPlane`, `cuspfunc_lim_coef`, `tsum_zero_pow`, `cuspfunc_Zero`, `modfom_q_exp_cuspfunc`, `qParam_surj_onto_ball`, `deriv_mul_eq`, `auxasdf`, `Ek_q_exp`, `Complex.I_pow_six`, `bernoulli'_five`, `Delta_E4_E6_aux` (used externally), `Delta_cuspFuntion_eq`, `Delta_ne_zero`, `asdf`, `diffwithinat_prod_1`, `Delta_q_one_term` (used externally), `E6_q_exp_one`, `E4_pow_q_exp_one`, `E4_ne_zero`, `E6_ne_zero`, `modularForm_normalise`, `PowerSeries.coeff_add`, `E₄_imag_axis_real`, `E₆_imag_axis_real`, `E₂_imag_axis_real`, `E₂_mul_E₄_isBoundedAtImInfty`. Of the whole file, only `E₄`, `E₆`, `bernoulli'_six`, `Delta_E4_E6_aux`, `Delta_q_one_term` are used outside it (grep -rlw over `XYin`).
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `E_even_imag_axis_real` (54), `E₂_imag_axis_real` (43), `Ek_q_exp` (33), `norm_tsum_logDeriv_expo_le` (31)

## Observations (evidence for the analysis phases)
### Mathlib API candidates
- `E₄`/`E₆` ↔ `ModularForm.E₄`/`ModularForm.E₆` (`.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean:51,54`; group `𝒮ℒ` vs `↑Γ(1)`, see the `open ModularForm hiding E₄ E₆` at line 21). Unlocks directly: `E_qExpansion_coeff`/`_zero`, `E_ne_zero` (`EisensteinSeries/QExpansion.lean:324,348,353`) ⇒ replaces `Ek_q_exp_zero`, `Ek_q_exp`, `Ek_ne_zero`, `E4_ne_zero`, `E6_ne_zero`; `E₄_qExpansion_coeff_one`/`E₆_qExpansion_coeff_one` (`LevelOne/DimensionFormula.lean:203,206`) ⇒ `E4_q_exp_one`, `E6_q_exp_one`; `discriminant_eq_E₄_cube_sub_E₆_sq(_graded)` (`LevelOne/GradedRing.lean:59,78`) ⇒ `Delta_E4_E6_aux` + `DimensionFormulas.Delta_E4_eqn`; `levelOne_weight_four_rank_one`, `levelOne_weight_six_rank_one`, `dimension_level_one` (`DimensionFormula.lean:193,198,249`).
- `cuspfunc_lim_coef` = mathlib private `hasSum_cuspFunction_of_hasSum_punctured` (`QExpansion.lean:230`); `q_exp_unique` = `funext` of `ModularFormClass.qExpansion_coeff_unique` (701); `modfom_q_exp_cuspfunc` = `qExpansion_coeff_unique` + `hasSum_qExpansion_of_norm_lt` (179); `cuspfunc_Zero` = `simp [qExpansion_coeff]` (169).
- `sigma_bound` = `ArithmeticFunction.sigma_le_pow_succ` (`ArithmeticFunction/Misc.lean:213`); `auxasdf` = `PowerSeries.coeff_mul`; `deriv_mul_eq` = `funext deriv_mul`; `PowerSeries.coeff_add` = `map_add`; `antidiagonal_one` = `Finset.Nat.antidiagonal_succ`+`antidiagonal_zero` (`Data/Finset/NatAntidiagonal.lean:65,67`); `tsum_zero_pow`/`summable_zero_pow` = `tsum_ite_eq`/`hasSum_ite_eq` (`Topology/Algebra/InfiniteSum/Basic.lean:503,170`) after `zero_pow_eq`; `Complex.I_pow_six` = `I_pow_eq_pow_mod` (`Data/Complex/Basic.lean:619`).
- `Delta_cuspFuntion_eq`, `Delta_q_one_term`, `diffwithinat_prod_1`, `Delta_ne_zero` = `discriminant_cuspFunction_eqOn` (`Discriminant.lean:197`), `discriminant_qExpansion_coeff_one` (210), `differentiableOn_tprod_one_sub_pow_pow` (`DedekindEta.lean:97`), `discriminant_ne_zero` (123).
- `asdf` ⊂ `multipliableLocallyUniformlyOn_one_sub_pow` (`DedekindEta.lean:73`) + `HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange` (`Topology/Algebra/InfiniteSum/UniformOn.lean:281`) — mathlib's version covers the whole unit ball.
- `modularForm_normalise`, `Delta_E4_E6_aux`'s `cuspFormOfCoeffZero`, `IsCuspForm_iff_coeffZero_eq_zero` ↔ `ModularForm.IsCuspForm`, `toCuspForm`, `isCuspForm_iff_coeffZero_eq_zero` (`CuspFormSubmodule.lean:73,127,136`).
- `norm_exp_two_pi_I_le_exp_neg_two_pi` ↔ `Periodic.norm_qParam` (`Analysis/Complex/Periodic.lean:49`) / `norm_qParam_le_of_one_half_le_im` (`UpperHalfPlane/Exp.lean:32`).
- `bernoulli'_five`, `bernoulli'_six`: NOT in mathlib (only up to `bernoulli'_four`, `Bernoulli.lean:135`; `bernoulli'_five` also follows from `bernoulli'_odd_eq_zero`) — upstream candidates. `E₂_isBoundedAtImInfty`, `norm_tsum_logDeriv_expo_le`, `E_even_imag_axis_real`, `E₂_imag_axis_real`, `E₂_eq`-based reality: no mathlib analogue found (searched `E2` with `BoundedAt`/`IsBigO`/`im_eq_zero` in `EisensteinSeries/E2/*`, `DedekindEta.lean`, `Discriminant.lean`).
- Hand-rolled summability: `qexpsummable` 211–217, `E_even_imag_axis_real` 491–510, `E₂_imag_axis_real` 563–577, `norm_tsum_logDeriv_expo_le` 613–632 — four separate `Summable.of_norm_bounded`/`of_nonneg_of_le` majorant arguments; mathlib `summable_pow_mul_cexp` (`EisensteinSeries/QExpansion.lean:192`) and `summable_norm_pow_mul_geometric_div_one_sub` (`TsumDivisorsAntidiagonal.lean:69`) cover them. Project `a33` (Summability/Basic.lean:107) duplicates `summable_pow_mul_cexp`.
### Missing API / repeated patterns
- "Term real ⇒ summable ⇒ `im_tsum` = 0" (482–515, 549–582; Delta.lean 339–351 for `tprod`): add `Complex.im_tsum_eq_zero_of_forall_im_eq_zero (hf : Summable f) (h : ∀ n, (f n).im = 0) : (∑' n, f n).im = 0` (and `tprod` twin) — collapses ~40 lines.
- `ResToImagAxis.Real` unfolding preamble (474–476, 542–544; Delta.lean 330–331, 404–405): add `ResToImagAxis.Real_iff : ResToImagAxis.Real F ↔ ∀ t > 0, (F ⟨I*t, _⟩).im = 0` in `ResToImagAxis.lean`.
- 4↔6 twins: `E4_eq/E6_eq`, `E4_apply/E6_apply`, `E₄_periodic/E₆_periodic`, `E₄_S_transform/E₆_S_transform` (10 lines each), `E4_q_exp/E6_q_exp`, `E4_q_exp_zero/E6_q_exp_zero`, `E4_q_exp_one/E6_q_exp_one`, `E4_ne_zero/E6_ne_zero`, `E₄_imag_axis_real/E₆_imag_axis_real` — every one is `general lemma for E k` specialised; the general lemmas exist (`Ek_q_exp_zero`, `Ek_ne_zero`, `E_even_imag_axis_real`) except for periodicity/`S`-transform, where a `SlashInvariantForm ↑Γ(1) k`-level `S_smul_eq`/`vAdd_one_eq` would serve all of `E₂, E₄, E₆, Δ`.
- `have heq : (Delta : ℍ → ℂ) = ModularForm.discriminant := funext Delta_eq_eta_pow` at 333 and 375 (and `DimensionFormulas.lean:122`): make `Delta.lean`'s private `delta_eq_discriminant` public.
- Cast workaround `rw [← Nat.cast_one (R := ℝ), …]` at 234, 395, 424 to match `qExpansion (1 : ℝ)` vs `qExpansion ↑(1 : ℕ)`: the project lemmas `q_exp_unique`, `qExpansion_mul_coeff`, `qExpansion_smul2` are stated with `n : ℕ` cast to ℝ; restating them (or using mathlib's `h : ℝ` versions with `one_mem_strictPeriods_SL`) removes the dance.
- `Ek_q` (206) vs local `c` in `Ek_q_exp` (231): the same function declared twice.
- Missing `@[simp]`: `E4_apply`, `E6_apply`, `φ₀''_def`, `φ₀''_coe_upperHalfPlane`, `E4_q_exp_zero`, `E6_q_exp_zero`, `E4_q_exp_one`, `E6_q_exp_one`, `Delta_q_one_term`.
### Junk candidates
- Placeholder names: `auxasdf` (198), `asdf` (342); typos `cuspFuntion` (331), `modfom` (164), `diffwithinat` (368).
- Dead declarations unused anywhere (see File Summary) — in particular the whole `φ` block 110–125 (9 decls), the cusp-function utilities 135–196 (8 decls), `Ek_q_exp` (37 lines), `asdf` (25 lines), `E₂_imag_axis_real` (45 lines), `E_even_imag_axis_real`+`E₄/E₆_imag_axis_real` (used only by each other), and the boundedness block 593–692 (only used internally). Live content used elsewhere: `E₄`, `E₆`, `bernoulli'_six`, `E4E6_coeff_zero_eq_zero`→`Delta_E4_E6_aux`, `Delta_q_one_term` (~40 lines of 692).
- Dead `variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)` (102); dead `variable {α β γ : Type*}` + `[CommMonoid α] [TopologicalSpace α] [UniformSpace α]` (379–381); `variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)` (128) leaks `n`, `f` into unrelated lemma signatures (`cuspfunc_Zero`, `modfom_q_exp_cuspfunc`, `qParam_surj_onto_ball`, `q_exp_unique`).
- Stale/noise comments: 53 (`/- -/` header), 56–57 (duplicate of Eisensteinqexpansions 23–24), 110, 114, 289–290 (`-- shrug`), 415 ("This is in the mod forms repo" — it is in mathlib as `E_ne_zero`), 455, 488 & 556 ("simp gives false positive linter warning"), 520.
- Namespace squatting from a project file: `Complex.I_pow_six`, `PowerSeries.coeff_add`, `bernoulli'_five/six` in root.
- Redundant opens: `open Complex Real` (106) then `open _root_.Complex hiding I` (444); `open ArithmeticFunction` (434) after `open scoped ArithmeticFunction.sigma` (27); `MeasureTheory intervalIntegral Metric` unused. Two nested `noncomputable section`s (29, 108) with only the outer closed implicitly.
### Moral duplicates within this batch
- `Ek_q_exp_zero` (222) vs `E4_q_exp_zero` (272) vs `E6_q_exp_zero` (301) vs `Ek_q_exp` at `m = 0`.
- `Ek_ne_zero`/`E4_ne_zero`/`E6_ne_zero` vs mathlib `E_ne_zero`; `Delta_ne_zero` (337) vs `Δ_ne_zero` (Delta.lean:44) vs `discriminant_ne_zero`.
- `Delta_cuspFuntion_eq`/`Delta_q_one_term` both re-prove `⇑Delta = discriminant`.
- `qexpsummable` (209) vs the inner `hsum` of `E_even_imag_axis_real` (491) vs `a33`: three proofs of `Σ σ_{k−1}(n) qⁿ` / `Σ nᵏ qⁿ` summability.
- `E₂_imag_axis_real`'s `hsum` (563–577) vs `norm_tsum_logDeriv_expo_le`'s `hsumm_norms` (631): both prove summability of `n qⁿ/(1−qⁿ)`.
- `exp_imag_axis_arg` (461) vs `Delta.lean:cexp_aux1/2` vs `hArg` (Delta.lean:333).
- `norm_exp_two_pi_I_le_exp_neg_two_pi` (593) vs `Delta.lean:cexp_two_pi_I_im_antimono` (119): both are `Complex.norm_exp` + monotonicity in `im`.
### Generalization notes
- `exists_smul_eq_of_rank_one(')`: `Module ℂ M` → any `[DivisionRing K] [Module K V]` (that is the generality of `finrank_eq_one_iff_of_nonzero'`).
- `summable_zero_pow`: `[NormedField G]` → `[AddCommGroup G] [MonoidWithZero G]`-ish with a topology (`summable_nat_add_iff` needs a topological additive group; `zero_pow` needs `MonoidWithZero` + `NoZeroDivisors` not even that); `tsum_zero_pow` (ℂ) likewise.
- `PowerSeries.coeff_add`: ℂ → any `Semiring R` (it is `map_add`).
- `smul_modularForm_eq_pointwise`: `Γ : Subgroup SL(2,ℤ)` → any `Γ : Subgroup (GL (Fin 2) ℝ)` (only `coe_smul` is used).
- `cuspfunc_lim_coef`, `cuspfunc_Zero`: the `[ModularFormClass F Γ(n) k]`/`[NeZero n]` hypotheses are unused by the proofs; both hold for arbitrary `f : ℍ → ℂ` and `0 < h : ℝ` (mathlib's private version is stated that way).
- `norm_tsum_logDeriv_expo_le(_of_norm_le)`: ℂ → any `NormedField`/`RCLike` `𝕜` with `‖q‖ < 1` (matches `summable_norm_pow_mul_geometric_div_one_sub`'s generality); the only ℂ-specific step is `Complex.norm_natCast`.
- `neg_two_pi_I_pow_even_real`: only `I^2 = −1` and evenness are used; holds for `(c * I)^k` with any real `c`.
- `antidiagonal_one`: holds in any `Finset.antidiagonal` over `ℕ`; already general in mathlib.
