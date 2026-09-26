# Inventory: XYin/PhD/Modularforms/Delta.lean  (408 lines)

Defines the modular discriminant `Δ(z) = q ∏(1−qⁿ)²⁴` as a function on ℍ, identifies it with mathlib's `ModularForm.discriminant = η²⁴`, packages it as `Discriminant_SIF : SlashInvariantForm ↑Γ(1) 12` and `Delta : CuspForm ↑Γ(1) 12`, builds the division map `CuspForm ↑Γ(1) k → ModularForm ↑Γ(1) (k−12)`, `f ↦ f/Δ` (used by `DimensionFormulas.lean`), and proves `Δ(it)` is real and positive on the imaginary axis (`ResToImagAxis.Real/Pos Δ`). Also contains dead helper material (`ℕ+`-scaling of ℍ, `atImInfty` monotonicity, `cexp` limits). Core results are all thin wrappers over mathlib `Discriminant.lean`; the group index `↑Γ(1)` (vs mathlib's `𝒮ℒ`) is the only reason the wrappers exist.

## Declarations

### `def Δ`
- **Type**: `(z : UpperHalfPlane) → ℂ`
- **What**: `Δ(z) = e^{2πiz} ∏_{n≥0} (1 − e^{2πi(n+1)z})²⁴`, the discriminant as an explicit product.
- **How**: Direct definition via `∏'` over `ℕ`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `DiscriminantProductFormula`, `Delta_eq_eta_pow`, `delta_eq_discriminant`, `Δ_ne_zero`, `Discriminant_T_invariant`, `Discriminant_S_invariant`, `Discriminant_SIF`, `Δ_periodic`, `Δ_S_transform`, `Discriminant_zeroAtImInfty`, `Delta_apply`, `Delta_isTheta_rexp`, `CuspForm_div_Discriminant_apply`, `Delta_imag_axis_real`, `re_ResToImagAxis_Delta_eq_real_prod`, `Delta_imag_axis_pos`
- **Visibility**: public
- **Lines**: 26–27, proof body ≈ 0 lines
- **Notes**: Heavily used externally (`DimensionFormulas.lean`, `jFunction/{jfunction,Deltaqexpansions,qexp_coeffs,jInvariantLink}.lean`, `Cox/LatticeJ.lean`, `qExpansion_tactic/{Examples,link,Qj}.lean`). mathlib: `ModularForm.discriminant (z : ℍ) := eta z ^ 24` (`Mathlib/NumberTheory/ModularForms/Discriminant.lean:50`) with `discriminant_eq_q_prod : Δ z = 𝕢 1 z * ∏' n, (1 - eta_q n z) ^ 24` (line 115), where `eta_q n z = cexp (2πi (n+1) z)` (`DedekindEta.lean:46`) — i.e. mathlib already provides this exact product form. Non-doc comment `/- The discriminant form -/` (line 25).

### `lemma DiscriminantProductFormula`
- **Type**: `(z : ℍ) : Δ z = cexp (2πi z) * ∏' (n : ℕ+), (1 - cexp (2πi n z)) ^ 24`
- **What**: Same product indexed by `ℕ+`.
- **How**: `tprod_pnat_eq_tprod_succ` under `congrArg`.
- **Hypotheses**: none
- **Uses from project**: `Δ`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 29–34, proof body ≈ 4 lines
- **Notes**: Unused anywhere. `tprod_pnat_eq_tprod_succ` is `Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean:545`.

### `lemma Delta_eq_eta_pow`
- **Type**: `(z : ℍ) : Δ z = (η z) ^ 24`
- **What**: `Δ = η²⁴`.
- **How**: `simpa [Δ, discriminant, Periodic.qParam, eta_q_eq_cexp] using (discriminant_eq_q_prod z).symm`.
- **Hypotheses**: none
- **Uses from project**: `Δ`
- **Used by**: `delta_eq_discriminant`, `Δ_ne_zero`, `Delta` (holo')
- **Visibility**: public
- **Lines**: 36–38, proof body ≈ 2 lines
- **Notes**: Externally used by `DimensionFormulas.lean:122`, `Eisenstein.lean:333,375`, `jFunction/Deltaqexpansions.lean:273`, `Cox/LatticeJ.lean:216,266` — always in the shape `funext Delta_eq_eta_pow` / `show Delta z = ModularForm.discriminant z`, i.e. as the bridge to mathlib. mathlib `discriminant_eq_q_prod` (`Discriminant.lean:115`).

### `private lemma delta_eq_discriminant`
- **Type**: `Δ = ModularForm.discriminant`
- **What**: Function-level equality with mathlib's discriminant.
- **How**: `funext Delta_eq_eta_pow`.
- **Hypotheses**: none
- **Uses from project**: `Δ`, `Delta_eq_eta_pow`
- **Used by**: `Discriminant_T_invariant`, `Discriminant_S_invariant`, `Discriminant_zeroAtImInfty`, `Delta_isTheta_rexp`
- **Visibility**: private
- **Lines**: 40–41, proof body ≈ 1 line
- **Notes**: Being `private`, downstream files re-prove it inline (`Eisenstein.lean:333, 375: have heq : (Delta : ℍ → ℂ) = ModularForm.discriminant := funext Delta_eq_eta_pow`; `DimensionFormulas.lean:122`). Should be public (and `@[simp]`-able as `Delta_coe_eq_discriminant`).

### `lemma Δ_ne_zero`
- **Type**: `(z : UpperHalfPlane) : Δ z ≠ 0`
- **What**: `Δ` never vanishes on ℍ.
- **How**: `Delta_eq_eta_pow` + mathlib `eta_ne_zero` (pow of nonzero).
- **Hypotheses**: none
- **Uses from project**: `Δ`, `Delta_eq_eta_pow`
- **Used by**: `CuspForm_div_Discriminant` (holo', line 230)
- **Visibility**: public
- **Lines**: 44–46, proof body ≈ 2 lines
- **Notes**: Externally used (`DimensionFormulas.lean:113,118`, `Eisenstein.lean:338`, `jfunction.lean:57,98`). mathlib `discriminant_ne_zero` (`Discriminant.lean:123`). Stale comment line 43 ("This should be easy from the definition and the Mulitpliable bit." — typo, and the proof is now a one-line mathlib call).

### `lemma Discriminant_T_invariant`
- **Type**: `(Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ`
- **What**: `Δ(z+1) = Δ(z)` as a slash identity.
- **How**: `rw [delta_eq_discriminant]; exact ModularForm.discriminant_T_invariant`.
- **Hypotheses**: none
- **Uses from project**: `Δ`, `delta_eq_discriminant`
- **Used by**: `Discriminant_SIF`
- **Visibility**: public
- **Lines**: 49–51, proof body ≈ 2 lines
- **Notes**: Wrapper of `ModularForm.discriminant_T_invariant` (`Discriminant.lean:127`). Stale comment line 48 ("This one is easy.").

### `lemma Discriminant_S_invariant`
- **Type**: `(Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ`
- **What**: `Δ(−1/z) = z¹² Δ(z)` as a slash identity.
- **How**: Wrapper of `ModularForm.discriminant_S_invariant`.
- **Hypotheses**: none
- **Uses from project**: `Δ`, `delta_eq_discriminant`
- **Used by**: `Discriminant_SIF`, `Δ_S_transform`
- **Visibility**: public
- **Lines**: 54–56, proof body ≈ 2 lines
- **Notes**: mathlib `Discriminant.lean:143`. Stale comment line 53 ("This is the hard one.") — it is now a one-liner; the "hard" content (`eta.lean`) is dead.

### `def Discriminant_SIF`
- **Type**: `SlashInvariantForm (CongruenceSubgroup.Gamma 1) 12`
- **What**: `Δ` bundled as a weight-12 slash-invariant form for `Γ(1)`.
- **How**: `slash_action_eq'` from the two generator identities via project `slashaction_generators_GL2R`.
- **Hypotheses**: none
- **Uses from project**: `Δ`, `Discriminant_S_invariant`, `Discriminant_T_invariant`, `slashaction_generators_GL2R` (SlashActionAuxil.lean:268)
- **Used by**: `Δ_periodic`, `Discriminant_zeroAtImInfty`, `Delta`
- **Visibility**: public
- **Lines**: 59–62, proof body ≈ 2 lines
- **Notes**: mathlib `CuspForm.discriminant : CuspForm 𝒮ℒ 12` (`Discriminant.lean:235`) contains this as its `toSlashInvariantForm`, using `slash_action_generators_SL2Z` (`LevelOne/Basic.lean:56`). Unused outside this file.

### `lemma Δ_periodic`
- **Type**: `(z : ℍ) : Δ ((1 : ℝ) +ᵥ z) = Δ z`
- **What**: 1-periodicity of `Δ`.
- **How**: `SlashInvariantForm.vAdd_width_periodic 1 12 1 Discriminant_SIF z`.
- **Hypotheses**: none
- **Uses from project**: `Δ`, `Discriminant_SIF`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 65–66, proof body ≈ 1 line
- **Notes**: Unused anywhere. `vAdd_width_periodic` is `Mathlib/NumberTheory/ModularForms/Identities.lean:37`.

### `lemma Δ_S_transform`
- **Type**: `(z : ℍ) : Δ (ModularGroup.S • z) = z ^ (12 : ℕ) * Δ z`
- **What**: Pointwise `S`-transformation of `Δ`.
- **How**: Evaluate `Discriminant_S_invariant` at `z`, `SL_slash_apply`, `ModularGroup.denom_S`, `zpow_neg`, `mul_inv_eq_iff_eq_mul₀`.
- **Hypotheses**: none
- **Uses from project**: `Δ`, `Discriminant_S_invariant`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 69–73, proof body ≈ 4 lines
- **Notes**: Unused anywhere. Same skeleton as `E₂_S_transform` (E2.lean:87), `E₄_S_transform`/`E₆_S_transform` (Eisenstein.lean:79/91).

### `lemma I_in_atImInfty`
- **Type**: `(A : ℝ) : { z : ℍ | A ≤ z.im} ∈ atImInfty`
- **What**: Half-planes `im ≥ A` are `atImInfty`-neighbourhoods.
- **How**: `atImInfty_mem` with witness `A`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `atImInfy_pnat_mono`
- **Visibility**: public
- **Lines**: 75–78, proof body ≈ 3 lines
- **Notes**: This is `(atImInfty_mem _).mpr ⟨A, fun _ h ↦ h⟩` (`Mathlib/Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean:42`). Unused outside this file.

### `instance natPosSMul`
- **Type**: `SMul ℕ+ ℍ`
- **What**: Scaling `z ↦ n·z` of ℍ by positive naturals.
- **How**: `UpperHalfPlane.mk (n * z)` with `im (n z) = n · im z > 0`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `natPosSMul_apply`, `pnat_smul_stable`, `atImInfy_pnat_mono`
- **Visibility**: public (global instance)
- **Lines**: 81–82, proof body ≈ 1 line
- **Notes**: No mathlib analogue (searched `SMul ℕ+ ℍ`, `instance.*SMul.*ℍ` in `Analysis/Complex/UpperHalfPlane/*`: only `SL(2,ℝ)`, `GL(2,ℝ)`, `PGL` actions). A global `SMul ℕ+ ℍ` instance is a diamond hazard (e.g. against `Nat.cast`-based scalar towers) and is unused anywhere in the project.

### `theorem natPosSMul_apply`
- **Type**: `(c : ℕ+) (z : ℍ) : ((c • z : ℍ) : ℂ) = (c : ℂ) * (z : ℂ)`
- **What**: Coercion of the scaled point.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: `natPosSMul`
- **Used by**: `atImInfy_pnat_mono`
- **Visibility**: public
- **Lines**: 84, proof body ≈ 0 lines
- **Notes**: Missing `@[simp]`.

### `def pnat_smul_stable`
- **Type**: `Set ℍ → Prop`
- **What**: A set closed under `n • ·` for all `n : ℕ+`.
- **How**: `∀ n s, s ∈ S → n • s ∈ S`.
- **Hypotheses**: none
- **Uses from project**: `natPosSMul`
- **Used by**: `atImInfy_pnat_mono`
- **Visibility**: public
- **Lines**: 86, proof body ≈ 0 lines
- **Notes**: Unused outside this file.

### `lemma atImInfy_pnat_mono`
- **Type**: `(S : Set ℍ) (hS : S ∈ atImInfty) (B : ℝ) : ∃ A : ℝ, pnat_smul_stable (S ∩ {z | max A B ≤ z.im}) ∧ S ∩ {z | max A B ≤ z.im} ∈ atImInfty`
- **What**: Any `atImInfty`-neighbourhood contains a smaller one that is stable under `ℕ+`-scaling.
- **How**: Take `A` from `atImInfty_mem`; scaling by `n ≥ 1` only increases `im` (`le_mul_iff_one_le_left`), so `S ∩ {im ≥ max A B}` is stable; membership by `inter_mem_iff` + `I_in_atImInfty`.
- **Hypotheses**: `S ∈ atImInfty`.
- **Uses from project**: `pnat_smul_stable`, `natPosSMul_apply`, `I_in_atImInfty`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 88–117, proof body ≈ 29 lines
- **Notes**: Unused anywhere (name typo `atImInfy`). Proof repeats the `hn : (1:ℝ) ≤ n; (le_mul_iff_one_le_left s.2).mpr hn` block twice (104–107, 109–112); `simp at *` at 101 and 114.

### `lemma cexp_two_pi_I_im_antimono`
- **Type**: `(a b : ℍ) (h : a.im ≤ b.im) (n : ℕ) : ‖cexp (2πi n b)‖ ≤ ‖cexp (2πi n a)‖`
- **What**: `|qⁿ|` is antitone in `im z`.
- **How**: `Complex.norm_exp`, `gcongr`.
- **Hypotheses**: `im a ≤ im b`.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 119–124, proof body ≈ 3 lines
- **Notes**: Unused anywhere.

### `theorem tendsto_neg_cexp_atImInfty`
- **Type**: `(k : ℕ) : Tendsto (fun x : ℍ ↦ -cexp (2πi (k+1) x)) atImInfty (𝓝 0)`
- **What**: `−q^{k+1} → 0` as `im z → ∞`.
- **How**: `tendsto_exp_nhds_zero_iff` reduces to `re → −∞`, i.e. `−2π(k+1)·im → −∞` via `Tendsto.const_mul_atTop` and `tendsto_iff_comap`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `log_one_neg_cexp_tendto_zero`
- **Visibility**: public
- **Lines**: 126–135, proof body ≈ 8 lines
- **Notes**: mathlib `UpperHalfPlane.qParam_tendsto_atImInfty (hh : 0 < h) : Tendsto (𝕢 h ·) atImInfty (𝓝 0)` (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:67`) composed with `(continuous_pow (k+1)).tendsto 0` and `.neg` gives this in one line (mathlib does exactly that at `Discriminant.lean:162`).

### `theorem log_one_neg_cexp_tendto_zero`
- **Type**: `(k : ℕ) : Tendsto (fun x : ℍ ↦ Complex.log ((1 - cexp (2πi (k+1) x)) ^ 24)) atImInfty (𝓝 0)`
- **What**: `log((1 − q^{k+1})²⁴) → 0` at `i∞`.
- **How**: `continuousAt_clog Complex.one_mem_slitPlane` composed with `tendsto_neg_cexp_atImInfty`.
- **Hypotheses**: none
- **Uses from project**: `tendsto_neg_cexp_atImInfty`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 137–141, proof body ≈ 2 lines
- **Notes**: Unused anywhere (residue of the pre-mathlib proof of `Delta_boundedfactor`). Typo `tendto`.

### `lemma Complex.cexp_tsum_eq_tprod_func`
- **Type**: `(f : ι → α → ℂ) (hfn : ∀ x n, f n x ≠ 0) (hf : ∀ x, Summable fun n => log (f n x)) : (cexp ∘ (fun a => ∑' n, log (f n a))) = fun a => ∏' n, f n a`
- **What**: Function-level `exp(Σ log fₙ) = ∏ fₙ`.
- **How**: `funext` + mathlib `Complex.cexp_tsum_eq_tprod`.
- **Hypotheses**: pointwise non-vanishing and summability of logs.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 145–149, proof body ≈ 2 lines
- **Notes**: Unused anywhere. One-line `funext` wrapper of `Complex.cexp_tsum_eq_tprod` (`Mathlib/Analysis/SpecialFunctions/Log/Summable.lean:39`). Declared in the `Complex` namespace from a project file. `variable {α ι : Type*}` at line 143 exists only for this.

### `theorem Delta_boundedfactor`
- **Type**: `Tendsto (fun x : ℍ ↦ ∏' (n : ℕ), (1 - cexp (2πi (n+1) x)) ^ 24) atImInfty (𝓝 1)`
- **What**: The product factor of `Δ` tends to 1 at `i∞`.
- **How**: `simpa [eta_q_eq_cexp] using ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 151–155, proof body ≈ 2 lines
- **Notes**: Externally used by `jFunction/jfunction.lean:102,165`. Wrapper of mathlib `tendsto_atImInfty_tprod_one_sub_eta_q_pow` (`Discriminant.lean:153`; deprecated alias `discriminant_bounded_factor`, line 173).

### `lemma Discriminant_zeroAtImInfty`
- **Type**: `∀ γ ∈ 𝒮ℒ, IsZeroAtImInfty (Discriminant_SIF ∣[(12 : ℤ)] (γ : GL (Fin 2) ℝ))`
- **What**: `Δ` vanishes at `i∞` after any `SL(2,ℤ)`-slash (needed for the cusp condition).
- **How**: Slash-invariance of `Discriminant_SIF` reduces to `IsZeroAtImInfty Δ`, which is mathlib `discriminant_isZeroAtImInfty`.
- **Hypotheses**: none
- **Uses from project**: `Discriminant_SIF`, `Δ`, `delta_eq_discriminant`
- **Used by**: `Delta`
- **Visibility**: public
- **Lines**: 159–168, proof body ≈ 8 lines
- **Notes**: mathlib `discriminant_isZeroAtImInfty` (`Discriminant.lean:175`). `open Real` at line 157 is mid-file. Unused outside this file.

### `def Delta`
- **Type**: `CuspForm (CongruenceSubgroup.Gamma 1) 12`
- **What**: The discriminant as a level-1 weight-12 cusp form.
- **How**: `toFun := Discriminant_SIF`; `holo'` via `mdifferentiable_iff` and `DifferentiableOn.pow` of mathlib `differentiableAt_eta_of_mem_upperHalfPlaneSet`, transported by `Delta_eq_eta_pow`; `zero_at_cusps'` via project `zero_at_cusps_of_zero_at_infty` + `Discriminant_zeroAtImInfty`.
- **Hypotheses**: none
- **Uses from project**: `Discriminant_SIF`, `Delta_eq_eta_pow`, `Discriminant_zeroAtImInfty`, `zero_at_cusps_of_zero_at_infty` (ForMathlib_Cusps.lean:9)
- **Used by**: `Delta_apply`, `Delta_isTheta_rexp`, `div_Delta_is_SIF`, `CuspForm_div_Discriminant`
- **Visibility**: public
- **Lines**: 170–189, proof body ≈ 18 lines
- **Notes**: Heavily used externally (`Eisensteinqexpansions`, `DimensionFormulas`, `Eisenstein`, `qExpansion_tactic/*`, `Tactic2/QExpSimpConditionTests`, `jFunction/*`, `Cox/LatticeJ`). mathlib `CuspForm.discriminant : CuspForm 𝒮ℒ 12` (`Discriminant.lean:235`, with `@[simp] coe_discriminant`, line 253) is the same object over `𝒮ℒ`; the `holo'` proof there is 3 lines vs 16 here. Group index `↑Γ(1)` vs `𝒮ℒ` is the only obstruction to `Delta := CuspForm.discriminant` (propositionally equal via `Gamma_one_coe_eq_SL`, `CongruenceSubgroups.lean:73`).

### `lemma Delta_apply`
- **Type**: `(z : ℍ) : Delta z = Δ z`
- **What**: Evaluation of the bundled cusp form.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: `Delta`, `Δ`
- **Used by**: `re_ResToImagAxis_Delta_eq_real_prod`
- **Visibility**: public
- **Lines**: 191, proof body ≈ 0 lines
- **Notes**: Externally used (`DimensionFormulas`, `Deltaqexpansions`, `jfunction`, `LatticeJ`). Missing `@[simp]` (mathlib's `coe_discriminant` is `@[simp]`).

### `lemma Delta_isTheta_rexp`
- **Type**: `Delta =Θ[atImInfty] (fun τ => Real.exp (-2 * π * τ.im))`
- **What**: `Δ` decays exactly like `e^{−2π im τ}` at `i∞`.
- **How**: `≤` direction from `CuspFormClass.exp_decay_atImInfty (h := 1)`; `≥` from mathlib `exp_isBigO_discriminant`.
- **Hypotheses**: none
- **Uses from project**: `Delta`, `Δ`, `delta_eq_discriminant`
- **Used by**: `CuspForm_div_Discriminant`
- **Visibility**: public
- **Lines**: 193–197, proof body ≈ 4 lines
- **Notes**: mathlib `exp_isBigO_discriminant` (`Discriminant.lean:181`), `CuspFormClass.exp_decay_atImInfty` (`QExpansion.lean:412`). Unused outside this file.

### `lemma CuspForm_apply`
- **Type**: `(k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k) (z : ℍ) : f.toFun z = f z`
- **What**: `toFun` agrees with the coercion.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 199–200, proof body ≈ 0 lines
- **Notes**: Unused anywhere; mathlib has `CuspForm.toFun_eq_coe`.

### `theorem div_Delta_is_SIF`
- **Type**: `(k : ℤ) (f : CuspForm (Gamma 1) k) (γ : GL (Fin 2) ℝ) (hγ : γ ∈ Subgroup.map (mapGL ℝ) (Gamma 1)) : (⇑f / ⇑Delta) ∣[k - 12] γ = ⇑f / ⇑Delta`
- **What**: `f/Δ` is slash-invariant of weight `k−12`.
- **How**: Pull `γ` back to `SL(2,ℤ)`, `div_slash_SL2`, then `congrArg₂` of the two slash-invariances.
- **Hypotheses**: `γ` in the image of `Γ(1)`.
- **Uses from project**: `Delta`, `div_slash_SL2` (SlashActionAuxil.lean)
- **Used by**: `CuspForm_div_Discriminant`
- **Visibility**: public
- **Lines**: 202–211, proof body ≈ 6 lines
- **Notes**: mathlib `CuspForm.divByDiscriminant_slash_eq (f : CuspForm 𝒮ℒ k) (γ : SL(2, ℤ))` (`LevelOne/DimensionFormula.lean:55`). Unused outside this file.

### `def CuspForm_div_Discriminant`
- **Type**: `(k : ℤ) (f : CuspForm (Gamma 1) k) : ModularForm (Gamma 1) (k - 12)`
- **What**: The modular form `f/Δ` of weight `k−12` (Δ is nowhere zero on ℍ and `f = O(Δ)` at `i∞`).
- **How**: `slash_action_eq'` from `div_Delta_is_SIF`; `holo'` via `mdifferentiable_iff`, `DifferentiableOn.div` and `Δ_ne_zero`; `bdd_at_cusps'` via `bounded_at_cusps_of_bounded_at_infty` then a 37-line manual unpacking of `CuspFormClass.exp_decay_atImInfty f` (`f = O(e^{−2π im})`) and `Delta_isTheta_rexp.2` (`e^{−2π im} = O(Δ)`) through `Asymptotics.isBigO_iff'`/`isBigO_iff''`, `eventually_iff_exists_mem`, and `div_le_div₀`.
- **Hypotheses**: none
- **Uses from project**: `Delta`, `div_Delta_is_SIF`, `Δ_ne_zero`, `Delta_isTheta_rexp`, `bounded_at_cusps_of_bounded_at_infty` (ForMathlib_Cusps.lean:16)
- **Used by**: `CuspForm_div_Discriminant_apply`, `CuspForm_div_Discriminant_Add`
- **Visibility**: public
- **Lines**: 213–270, proof body ≈ 56 lines
- **Notes**: Proof >30 lines. Externally used by `DimensionFormulas.lean:100` (as `toFun` of a linear map). mathlib `CuspForm.divDiscriminant (f : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ (k - 12)` and the linear equivalence `CuspForm.discriminantEquiv : CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12)` (`LevelOne/DimensionFormula.lean:95,63`) are the same construction. Hand-rolled asymptotics (234–270): `CuspForm.exp_decay_isBigO_discriminant f : f =O[atImInfty] Δ` (`Discriminant.lean:258`) plus `Asymptotics.isBigO_iff_div_isBoundedUnder` (`Analysis/Asymptotics/Lemmas.lean:517`) give `IsBoundedAtImInfty (f/Δ)` directly, avoiding the ε/`eventually` unpacking, the `e1/e2` trick (261–263) and `min A1 B2`.

### `lemma CuspForm_div_Discriminant_apply`
- **Type**: `(k : ℤ) (f : CuspForm (Gamma 1) k) (z : ℍ) : (CuspForm_div_Discriminant k f) z = f z / Δ z`
- **What**: Evaluation of `f/Δ`.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: `CuspForm_div_Discriminant`, `Δ`
- **Used by**: `CuspForm_div_Discriminant_Add`
- **Visibility**: public
- **Lines**: 272–273, proof body ≈ 0 lines
- **Notes**: Externally used (`DimensionFormulas.lean:105,112,117`). mathlib `divDiscriminant_apply` (`DimensionFormula.lean:99`). Missing `@[simp]`.

### `theorem CuspForm_div_Discriminant_Add`
- **Type**: `(k : ℤ) (x y : CuspForm (Gamma 1) k) : (fun f ↦ CuspForm_div_Discriminant k f) (x + y) = … x + … y`
- **What**: Additivity of `f ↦ f/Δ`.
- **How**: `ext z; simp [CuspForm_div_Discriminant_apply, add_apply]; ring` (i.e. `add_div`).
- **Hypotheses**: none
- **Uses from project**: `CuspForm_div_Discriminant`, `CuspForm_div_Discriminant_apply`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 275–280, proof body ≈ 3 lines
- **Notes**: Externally used as `map_add'` in `DimensionFormulas.lean:101`. Statement is written with η-expanded `(fun f ↦ …) (x + y)`; mathlib's `discriminantEquiv` already carries `map_add`. No matching `_smul` lemma here (DimensionFormulas re-proves it inline at line 105).

### `lemma cexp_aux1`
- **Type**: `(t : ℝ) : cexp (2 * π * I * (I * t)) = rexp (-2 * π * t)`
- **What**: `q` at `z = it` is the real number `e^{−2πt}`.
- **How**: `ring_nf` to `I*I` then `simp`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `re_ResToImagAxis_Delta_eq_real_prod`
- **Visibility**: public
- **Lines**: 282–285, proof body ≈ 3 lines
- **Notes**: Unused outside this file. Compare `exp_imag_axis_arg` (`Eisenstein.lean:461`) — same computation for `ℕ+`-multiples.

### `lemma cexp_aux2`
- **Type**: `(t : ℝ) (n : ℕ) : cexp (2 * π * I * (n + 1) * (I * t)) = rexp (-(2 * π * (n + 1) * t))`
- **What**: `q^{n+1}` at `z = it` is real.
- **How**: Same as `cexp_aux1`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `re_ResToImagAxis_Delta_eq_real_prod`
- **Visibility**: public
- **Lines**: 287–291, proof body ≈ 3 lines
- **Notes**: Unused outside this file. Unusual leading-colon layout (`(n : ℕ)\n    : cexp …`).

### `lemma cexp_aux3`
- **Type**: `(t : ℝ) (n : ℕ) (ht : 0 < t) : 0 < 1 - rexp (-(2 * π * (n + 1) * t))`
- **What**: `1 − e^{−2π(n+1)t} > 0` for `t > 0`.
- **How**: `Real.exp_lt_one_iff` + `positivity` + `linarith`.
- **Hypotheses**: `0 < t`.
- **Uses from project**: `[]`
- **Used by**: `tprod_pos_nat_im`
- **Visibility**: public
- **Lines**: 293–295, proof body ≈ 2 lines
- **Notes**: Unused outside this file.

### `lemma cexp_aux4`
- **Type**: `(t : ℝ) (n : ℕ) : (cexp (-2 * π * (n + 1) * t)).im = 0`
- **What**: `exp` of a real number has zero imaginary part.
- **How**: `Complex.exp_ofReal_im` after pushing casts.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `Delta_imag_axis_real`
- **Visibility**: public
- **Lines**: 297–298, proof body ≈ 1 line
- **Notes**: Instance of mathlib `Complex.exp_ofReal_im` (`Mathlib/Analysis/Complex/Exponential.lean:191`). Unused outside this file.

### `lemma cexp_aux5`
- **Type**: `(t : ℝ) : (cexp (-(2 * π * t))).im = 0`
- **What**: Same as `cexp_aux4` with `n+1` removed.
- **How**: `Complex.exp_ofReal_im`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `Delta_imag_axis_real`
- **Visibility**: public
- **Lines**: 300–301, proof body ≈ 1 line
- **Notes**: Unused outside this file.

### `lemma Complex.im_finset_prod_eq_zero_of_im_eq_zero`
- **Type**: `{ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, (f i).im = 0) : (∏ i ∈ s, f i).im = 0`
- **What**: A finite product of real complex numbers is real.
- **How**: `Finset.induction_on` with `Complex.mul_im`.
- **Hypotheses**: each factor real.
- **Uses from project**: `[]`
- **Used by**: `Complex.im_tprod_eq_zero_of_im_eq_zero`
- **Visibility**: public
- **Lines**: 304–310, proof body ≈ 4 lines
- **Notes**: No direct mathlib lemma (searched `im_prod`, `im_finset_prod`); the idiomatic route is `f i = ↑(f i).re` (`Complex.ext_iff`/`Complex.re_add_im`) and `Complex.ofReal_prod` (`Mathlib/Data/Complex/BigOperators.lean:25`) + `Complex.ofReal_im`. Declared in `Complex` namespace from a project file; comment 303 is `/- -/` not a docstring.

### `lemma Complex.im_pow_eq_zero_of_im_eq_zero`
- **Type**: `{z : ℂ} (hz : z.im = 0) (m : ℕ) : (z ^ m).im = 0`
- **What**: Powers of a real complex number are real.
- **How**: Write `z = ↑z.re` and use `Complex.ofReal_pow`.
- **Hypotheses**: `z.im = 0`.
- **Uses from project**: `[]`
- **Used by**: `Delta_imag_axis_real`
- **Visibility**: public
- **Lines**: 312–315, proof body ≈ 2 lines
- **Notes**: `Complex.ofReal_pow` is `Mathlib/Data/Complex/Basic.lean:636`. Unused outside this file.

### `lemma Complex.im_tprod_eq_zero_of_im_eq_zero`
- **Type**: `(f : ℕ → ℂ) (hf : Multipliable f) (him : ∀ n, (f n).im = 0) : (∏' n : ℕ, f n).im = 0`
- **What**: A convergent infinite product of real numbers is real.
- **How**: `im` is continuous, so `im (∏' f) = lim im (∏_{range n} f) = lim 0 = 0` via `hf.hasProd.tendsto_prod_nat` and `tendsto_nhds_unique`.
- **Hypotheses**: `Multipliable f`, factors real.
- **Uses from project**: `Complex.im_finset_prod_eq_zero_of_im_eq_zero`
- **Used by**: `Delta_imag_axis_real`
- **Visibility**: public
- **Lines**: 317–326, proof body ≈ 7 lines
- **Notes**: Hand-rolled "continuity + uniqueness of limits" argument; `Multipliable.map_tprod` (`Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:244`) with `Complex.ofRealHom` (as done in `re_ResToImagAxis_Delta_eq_real_prod` via `Function.LeftInverse.map_tprod`, line 274) would give `∏' f = ↑(∏' (f n).re)` and hence this for free. Unused outside this file.

### `lemma Delta_imag_axis_real`
- **Type**: `ResToImagAxis.Real Δ`
- **What**: `Δ(it)` is real for every `t > 0`.
- **How**: Each factor `(1 − e^{−2π(n+1)t})²⁴` is real (`cexp_aux4`, `im_pow_eq_zero_of_im_eq_zero`), the product is multipliable (`MultipliableEtaProductExpansion` + `Multipliable_pow`), so its imaginary part is zero (`im_tprod_eq_zero_of_im_eq_zero`); the prefactor is real by `cexp_aux5`; conclude by `Complex.mul_im`.
- **Hypotheses**: none
- **Uses from project**: `Δ`, `cexp_aux4`, `cexp_aux5`, `Complex.im_pow_eq_zero_of_im_eq_zero`, `Complex.im_tprod_eq_zero_of_im_eq_zero`, `Multipliable_pow` (multipliable_lems.lean:55), `MultipliableEtaProductExpansion` (multipliable_lems.lean:37), `ResToImagAxis.Real` (ResToImagAxis.lean:53)
- **Used by**: `Delta_imag_axis_pos`
- **Visibility**: public
- **Lines**: 329–355, proof body ≈ 26 lines
- **Notes**: Unused outside this file. `Multipliable_pow` is mathlib `Multipliable.pow` (`InfiniteSum/Basic.lean:334`); `MultipliableEtaProductExpansion` is mathlib `multipliableLocallyUniformlyOn_eta.multipliable z.2` (`DedekindEta.lean:106`) / `multipliable_one_sub_pow` (66). The `hArg` computation (333–338) duplicates `cexp_aux2`/`Eisenstein.lean:exp_imag_axis_arg`.

### `lemma re_ResToImagAxis_Delta_eq_real_prod`
- **Type**: `(t : ℝ) (ht : 0 < t) : (Δ.resToImagAxis t).re = Real.exp (-2 * π * t) * ∏' (n : ℕ), (1 - Real.exp (-(2 * π * (n + 1) * t))) ^ 24`
- **What**: Explicit real formula for `Δ(it)`.
- **How**: Rewrite each complex factor as a cast of a real one (`cexp_aux1`, `cexp_aux2`), pull the cast through `∏'` with `Function.LeftInverse.map_tprod` applied to `Complex.ofRealHom` (continuous, left-inverse `re`), then `Complex.ofReal_re`.
- **Hypotheses**: `0 < t`.
- **Uses from project**: `Δ`, `Delta_apply`, `cexp_aux1`, `cexp_aux2`, `resToImagAxis`/`ResToImagAxis` (ResToImagAxis.lean:32,38)
- **Used by**: `Delta_imag_axis_pos`
- **Visibility**: public
- **Lines**: 357–371, proof body ≈ 13 lines
- **Notes**: Unused outside this file. `Function.LeftInverse.map_tprod` is `InfiniteSum/Basic.lean:274`; mathlib has no `Complex.ofReal_tprod` (searched `ofReal_tprod`, `tprod_ofReal`), only `Complex.ofReal_tsum` (`Analysis/Complex/Basic.lean:600`) — a `Complex.ofReal_tprod` would be a natural small mathlib addition.

### `lemma tprod_pos_nat_im`
- **Type**: `(z : ℍ) : 0 < ∏' (n : ℕ), (1 - Real.exp (-(2 * π * (n + 1) * z.im))) ^ 24`
- **What**: The real Euler-type product is strictly positive.
- **How**: Each factor positive (`cexp_aux3`), logs summable via `Real.summable_log_one_add_of_summable` and `Real.summable_exp_nat_mul_iff` (shifted by `summable_nat_add_iff 1`), then `Real.rexp_tsum_eq_tprod` expresses the product as `exp` of a real number.
- **Hypotheses**: none (uses `z.im > 0`).
- **Uses from project**: `cexp_aux3`
- **Used by**: `Delta_imag_axis_pos`
- **Visibility**: public
- **Lines**: 373–395, proof body ≈ 21 lines
- **Notes**: Unused outside this file. mathlib: `Real.rexp_tsum_eq_tprod` (`Analysis/SpecialFunctions/Log/Summable.lean:81`), `Real.summable_log_one_add_of_summable` (86), `Real.summable_exp_nat_mul_iff` (`Analysis/SpecialFunctions/Exp.lean:420`). Stated with `z : ℍ` but only `z.im` is used (statement in terms of `t > 0` would match its single caller, which has to build `z` from `t` at 404–406).

### `lemma Delta_imag_axis_pos`
- **Type**: `ResToImagAxis.Pos Δ`
- **What**: `Δ(it)` is real and strictly positive for `t > 0`.
- **How**: `Delta_imag_axis_real` for reality; positivity from `re_ResToImagAxis_Delta_eq_real_prod` and `tprod_pos_nat_im` (with `Real.exp_pos`).
- **Hypotheses**: none
- **Uses from project**: `Δ`, `Delta_imag_axis_real`, `re_ResToImagAxis_Delta_eq_real_prod`, `tprod_pos_nat_im`, `ResToImagAxis.Pos` (ResToImagAxis.lean:60)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 398–408, proof body ≈ 9 lines
- **Notes**: Unused anywhere in the project (grep -w `Delta_imag_axis_pos`, `Delta_imag_axis_real`, and `imag_axis` outside this file and `Eisenstein.lean`: none). The `ResToImagAxis.lean` combinators (`Pos.mul`, `Pos.pow`, …) suggest this was intended for a positivity argument for `j` or `Δ`-quotients that has not been written.

## File Summary
- Total declarations: 42 (5 defs: `Δ`, `Discriminant_SIF`, `pnat_smul_stable`, `Delta`, `CuspForm_div_Discriminant`; 36 lemmas/theorems; 1 instance: `natPosSMul`; 0 other)
- Key API (used by 3+ others in the file): `Δ` (16), `Delta` (4), `Discriminant_SIF` (3), `delta_eq_discriminant` (4), `Delta_eq_eta_pow` (3), `natPosSMul` (3)
- Unused declarations (not used by anything in this file): `DiscriminantProductFormula`, `Δ_periodic`, `Δ_S_transform`, `atImInfy_pnat_mono`, `cexp_two_pi_I_im_antimono`, `log_one_neg_cexp_tendto_zero`, `Complex.cexp_tsum_eq_tprod_func`, `Delta_boundedfactor` (used externally by `jfunction.lean`), `CuspForm_apply`, `CuspForm_div_Discriminant_Add` (used externally by `DimensionFormulas.lean`), `Delta_imag_axis_pos`. Unused anywhere in the project: `DiscriminantProductFormula`, `Δ_periodic`, `Δ_S_transform`, `I_in_atImInfty`, `natPosSMul`, `natPosSMul_apply`, `pnat_smul_stable`, `atImInfy_pnat_mono`, `cexp_two_pi_I_im_antimono`, `tendsto_neg_cexp_atImInfty`, `log_one_neg_cexp_tendto_zero`, `Complex.cexp_tsum_eq_tprod_func`, `Discriminant_zeroAtImInfty` (only via `Delta`), `Delta_isTheta_rexp` (only via `CuspForm_div_Discriminant`), `CuspForm_apply`, `div_Delta_is_SIF` (only via `CuspForm_div_Discriminant`), `cexp_aux1`–`cexp_aux5`, the three `Complex.im_*` lemmas, `Delta_imag_axis_real`, `re_ResToImagAxis_Delta_eq_real_prod`, `tprod_pos_nat_im`, `Delta_imag_axis_pos`.
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `CuspForm_div_Discriminant` (56 lines; `bdd_at_cusps'` alone 37)

## Observations (evidence for the analysis phases)
### Mathlib API candidates
- `Δ` / `Delta_eq_eta_pow` / `Δ_ne_zero` / `Discriminant_T_invariant` / `Discriminant_S_invariant` / `Delta_boundedfactor` / `Discriminant_zeroAtImInfty` / `Delta_isTheta_rexp` ↔ `ModularForm.discriminant`, `discriminant_eq_q_prod`, `discriminant_ne_zero`, `discriminant_T_invariant`, `discriminant_S_invariant`, `tendsto_atImInfty_tprod_one_sub_eta_q_pow`, `discriminant_isZeroAtImInfty`, `exp_isBigO_discriminant` (`.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Discriminant.lean:50,115,123,127,143,153,175,181`). All project versions are already 1–3-line wrappers; the wrapper layer exists only because `Δ` is a separate `def`.
- `Discriminant_SIF` + `Delta` ↔ `CuspForm.discriminant : CuspForm 𝒮ℒ 12` (`Discriminant.lean:235`) with `@[simp] coe_discriminant` (253). Obstruction: group index `↑Γ(1)` vs `𝒮ℒ`; mathlib's own `ModularForm.E` handles the same mismatch with `.copy _ rfl Gamma_one_coe_eq_SL.symm` (`EisensteinSeries/Basic.lean:48`), so `Delta` could be defined as a copy of `CuspForm.discriminant` (or the project could migrate to `𝒮ℒ`, which `Discriminant_zeroAtImInfty` already quantifies over).
- `CuspForm_div_Discriminant` (+ `_apply`, `_Add`, `div_Delta_is_SIF`) ↔ `CuspForm.divDiscriminant`, `divDiscriminant_apply`, `discriminantEquiv` (a `≃ₗ[ℂ]`, so `map_add`/`map_smul` are free), `divByDiscriminant_slash_eq` (`LevelOne/DimensionFormula.lean:95,99,63,55`). `DimensionFormulas.lean:100–118` rebuilds exactly `discriminantEquiv` by hand from these.
- `Delta_isTheta_rexp.1` ↔ `CuspForm.exp_decay_isBigO_discriminant` (`Discriminant.lean:258`) is the more useful form (`f =O Δ` for every cusp form `f`).
- `cexp_aux4`, `cexp_aux5` = `Complex.exp_ofReal_im` (`Analysis/Complex/Exponential.lean:191`); `Complex.cexp_tsum_eq_tprod_func` = `funext` of `Complex.cexp_tsum_eq_tprod` (`Analysis/SpecialFunctions/Log/Summable.lean:39`); `tendsto_neg_cexp_atImInfty` = `(qParam_tendsto_atImInfty one_pos).pow.neg` (`QExpansion.lean:67`); `I_in_atImInfty` = `(atImInfty_mem _).mpr ⟨A, fun _ h ↦ h⟩` (`UpperHalfPlane/FunctionsBoundedAtInfty.lean:42`).
- `Multipliable_pow` (used at 349) = `Multipliable.pow` (`InfiniteSum/Basic.lean:334`); `MultipliableEtaProductExpansion` = `ModularForm.multipliable_one_sub_pow` (`DedekindEta.lean:66`).
- `natPosSMul`, `pnat_smul_stable`, `atImInfy_pnat_mono`, `cexp_two_pi_I_im_antimono`: no mathlib analogue found (searched `SMul ℕ+ ℍ`, `pnat_smul`, `im_antitone` in `UpperHalfPlane/`); all dead.
- Hand-rolled asymptotics in `CuspForm_div_Discriminant.bdd_at_cusps'` (234–270): two `IsBigO`s unpacked to `∃ c, ∀ᶠ` and recombined with `div_le_div₀`; `Asymptotics.isBigO_iff_div_isBoundedUnder` (`Analysis/Asymptotics/Lemmas.lean:517`) + `CuspForm.exp_decay_isBigO_discriminant` does it in ~3 lines.
- Hand-rolled limit argument in `Complex.im_tprod_eq_zero_of_im_eq_zero` (317–326): replaceable by `Multipliable.map_tprod` with `Complex.ofRealHom` (`InfiniteSum/Basic.lean:244`), as `re_ResToImagAxis_Delta_eq_real_prod` already does with `LeftInverse.map_tprod`.
- Hand-rolled summability in `tprod_pos_nat_im` (378–390): `Real.summable_exp_nat_mul_iff` + `summable_nat_add_iff` re-derives the summability of `e^{−2π(n+1)t}`, which is also `(summable_geometric_of_lt_one …)` and is available in mathlib as `ModularForm.summable_eta_q` (`DedekindEta.lean:102`, norm form).
### Missing API / repeated patterns
- `have heq : (Delta : ℍ → ℂ) = ModularForm.discriminant := funext Delta_eq_eta_pow` is re-proved at `Eisenstein.lean:333, 375` and `DimensionFormulas.lean:122` because `delta_eq_discriminant` (40) is `private`. Make it public: `lemma Delta_coe_eq_discriminant : ⇑Delta = ModularForm.discriminant`.
- `Δ_S_transform` (69–73) shares its skeleton with `E₂_S_transform` (E2.lean:87), `E₄_S_transform`/`E₆_S_transform` (Eisenstein.lean:79/91): a general `SlashInvariantForm.S_smul_eq (f : SlashInvariantForm ↑Γ(1) k) (z) : f (S • z) = z ^ k * f z` is missing.
- `let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩` + `simp [ResToImagAxis, ht]` at 330–331, 345, 404–405 and `Eisenstein.lean:474–476, 542–544`: a lemma `ResToImagAxis.Real_iff / ResToImagAxis.resToImagAxis_of_pos (ht) : F.resToImagAxis t = F ⟨I*t, _⟩` (belongs in `ResToImagAxis.lean`) would remove all five.
- `cexp_aux1`/`cexp_aux2`/`hArg` (333–338) and `Eisenstein.lean:exp_imag_axis_arg` (461) are four spellings of `2πi·n·(it) = −2πnt`; one lemma `two_pi_I_mul_I_mul (n t : ℝ) : 2 * π * I * (n * (I * t)) = ↑(-(2 * π * n * t))` suffices.
- `Delta_apply`, `CuspForm_div_Discriminant_apply`, `natPosSMul_apply` lack `@[simp]`; no `CuspForm_div_Discriminant_smul` (DimensionFormulas re-proves it at 105).
### Junk candidates
- Dead block 75–149 (`I_in_atImInfty` … `Complex.cexp_tsum_eq_tprod_func`): 9 declarations, 75 lines, unused anywhere, including a global `SMul ℕ+ ℍ` instance.
- Dead imaginary-axis block 282–408 (`cexp_aux1` … `Delta_imag_axis_pos`): 13 declarations, 127 lines, unused anywhere (may be wanted later for `j`-positivity; if kept, it belongs in `ResToImagAxis.lean` or a `Delta/ImagAxis.lean`).
- One-line wrappers: `Discriminant_T_invariant`, `Discriminant_S_invariant`, `Delta_boundedfactor`, `Complex.cexp_tsum_eq_tprod_func`, `cexp_aux4`, `cexp_aux5`, `CuspForm_apply`, `I_in_atImInfty`.
- Stale comments: 43 ("should be easy … Mulitpliable bit"), 48 ("This one is easy."), 53 ("This is the hard one."); non-doc `/- -/` comments at 25, 303, 328, 397 that should be docstrings.
- Unused opens: `MeasureTheory intervalIntegral Metric` (16–17), `open scoped Interval NNReal ENNReal` (19). `open Real` at 157 mid-file. `variable {α ι : Type*}` (143) serves one dead lemma.
- Imports: `XYin.PhD.Modularforms.eta` (line 5) is imported but nothing from it is used (the file's content is dead); `clog_arg_lems`, `NormNumI` imports are not visibly used in this file.
- Typos in names: `atImInfy_pnat_mono`, `log_one_neg_cexp_tendto_zero`.
### Moral duplicates within this batch
- `Δ_periodic`/`Δ_S_transform` vs `E₄_periodic`/`E₄_S_transform`, `E₆_*`, `E₂_*` (same proofs, different form).
- `cexp_aux4`/`cexp_aux5`/`hArg` (Delta) vs `exp_imag_axis_arg` (Eisenstein 461): same real-exponent computation.
- `Delta_imag_axis_real` (329) vs `E_even_imag_axis_real` (Eisenstein 471) vs `E₂_imag_axis_real` (Eisenstein 540): identical "each term real ⇒ summable/multipliable ⇒ `im` of `tsum`/`tprod` is zero" skeleton; differ only in `tsum` vs `tprod`.
- `Delta_isTheta_rexp.1` re-derives `CuspFormClass.exp_decay_atImInfty` which `CuspForm_div_Discriminant` then calls again directly (line 237).
### Generalization notes
- `Complex.im_finset_prod_eq_zero_of_im_eq_zero`, `im_pow_eq_zero_of_im_eq_zero`, `im_tprod_eq_zero_of_im_eq_zero`: the natural general statement is "the image of `Complex.ofRealHom` (a closed subring) is closed under finite/infinite products", i.e. `∏' f ∈ Set.range ofReal`; over any `RCLike 𝕜` the same holds with `RCLike.ofReal`.
- `tprod_pos_nat_im` only uses `0 < z.im`; state it for `t : ℝ` with `0 < t` (matches its only use at 402–406).
- `atImInfy_pnat_mono` and `natPosSMul` are stated for `ℕ+` but the proof uses only `1 ≤ n` (works for any real `c ≥ 1`).
