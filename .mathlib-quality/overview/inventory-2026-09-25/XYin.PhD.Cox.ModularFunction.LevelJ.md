# Inventory: XYin/PhD/Cox/ModularFunction/LevelJ.lean  (329 lines)

Constructs `levelJModularFunction N : ModularFunction (Gamma0 N)`, the bundled `τ ↦ j(Nτ)`. The only real work is cusp meromorphy: for each `γ ∈ SL₂(ℤ)` a hand-rolled left `SL₂(ℤ)`-triangularization of `!![N γ₀₀, N γ₀₁; γ₁₀, γ₁₁]` (gcd of the first column via `IsCoprime.exists_SL2_col`) writes `j(N γτ)` as `j((r + gτ)/s)`, whose width-`gs` cusp function is `cuspFunction 1 j` precomposed with the analytic map `q ↦ ζ q^{g²}`.

## Declarations

### `def Cox.levelJ`
- **Type**: `(N : ℕ+) : ℍ → ℂ := @jN (N : ℕ) ⟨PNat.ne_zero N⟩`
- **What**: The project's `τ ↦ j(Nτ)`, with the `NeZero` instance packaged by `ℕ+`.
- **How**: wrapper around `jN` (jLevelN.lean:37).
- **Hypotheses**: none.
- **Uses from project**: `jN`
- **Used by**: `levelJ_comp_eq_affine_of_normalization`, `levelJ_meromorphicAt_cusp`, `levelJ_mdifferentiable`, `levelJModularFunction`, `coe_levelJModularFunction`, `levelJ_cuspData`
- **Visibility**: public
- **Lines**: 25–26
- **Notes**: Load-bearing name (30+ external sites: Arithmetic.lean:47–284, CoxMatrices/Basic.lean:637, 724, 785, AnalyticSupport.lean:29, Construction.lean:363, Interpolation.lean:323–490, ModularFunctionField.lean:29–163). Every `levelJ` lemma is a `jN` lemma with `N : ℕ+` — a second name for the same function; `jN_slash_invariant`, `jN_differentiableAt` are consumed through it. No `levelJ_apply` simp lemma (`levelJ N τ = j ⟨N * τ, _⟩`); consumers use `change` (line 269–270, CoxMatrices/Basic.lean:730).

### `private def Cox.natScaleUpperHalfPlane`
- **Type**: `(N : ℕ+) (τ : ℍ) : ℍ := ⟨(N : ℂ) * τ, _⟩`
- **What**: The point `Nτ ∈ ℍ`.
- **How**: `Complex.mul_im` and `mul_pos`.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: `coe_natScaleUpperHalfPlane`, `coe_inv_smul_natScale_smul`, `inv_smul_natScale_smul_eq_affine`, `levelJ_comp_eq_affine_of_normalization` (via `change`)
- **Visibility**: private
- **Lines**: 29–33
- **Notes**: Re-inlined verbatim as `zN` at CoxMatrices/Basic.lean:725–728 and as the anonymous `⟨(N : ℂ) * z, natCast_mul_im_pos_aux N z.2⟩` inside `jN` (jLevelN.lean:38). Mathlib already has `UpperHalfPlane.posRealAction : MulAction {x : ℝ // 0 < x} ℍ` (`Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean:197`, with `coe_pos_real_smul` at :205), which this file itself uses in `affineUpperHalfPlane` (line 43); `natScaleUpperHalfPlane N τ = (⟨N, _⟩ : {x : ℝ // 0 < x}) • τ`.

### `@[simp] private lemma Cox.coe_natScaleUpperHalfPlane`
- **Type**: `(N : ℕ+) (τ : ℍ) : ((natScaleUpperHalfPlane N τ : ℍ) : ℂ) = (N : ℂ) * (τ : ℂ)`
- **What**: Coercion of `Nτ`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `natScaleUpperHalfPlane`
- **Used by**: `coe_inv_smul_natScale_smul`
- **Visibility**: private
- **Lines**: 36–38
- **Notes**: —

### `private def Cox.affineUpperHalfPlane`
- **Type**: `(g s : ℕ) (hg : 0 < g) (hs : 0 < s) (r : ℤ) (τ : ℍ) : ℍ := (r/s : ℝ) +ᵥ (⟨g/s, _⟩ : {x : ℝ // 0 < x}) • τ`
- **What**: The affine transform `τ ↦ (gτ + r)/s` of ℍ, for positive `g, s`.
- **How**: composed from mathlib's `+ᵥ` (real translation) and positive-real scaling actions on ℍ.
- **Hypotheses**: `g, s > 0`.
- **Uses from project**: `[]`
- **Used by**: `coe_affineUpperHalfPlane`, `qParam_affineUpperHalfPlane`, `inv_smul_natScale_smul_eq_affine`, `cuspFunction_affine_j_eq`, `levelJ_comp_eq_affine_of_normalization`, `affine_j_cuspFunction_meromorphicAt`
- **Visibility**: private
- **Lines**: 40–44
- **Notes**: This is also `σ.act τ` for the Cox matrix `σ = !![g, r; 0, s]` (CoxMatrix.act, CyclicSublattice/Classification.lean:178ff; `CoxMatrix.coe_act` used at CoxMatrices/Basic.lean:757) — two encodings of the same affine map, without the `0 ≤ r < s` reduction here.

### `@[simp] private lemma Cox.coe_affineUpperHalfPlane`
- **Type**: `… : ((affineUpperHalfPlane g s hg hs r τ : ℍ) : ℂ) = ((r : ℝ) / s : ℂ) + ((g : ℝ) / s : ℂ) * (τ : ℂ)`
- **What**: Coercion of the affine transform.
- **How**: `simp [affineUpperHalfPlane]` (mathlib `coe_vadd`, `coe_pos_real_smul`).
- **Hypotheses**: `g, s > 0`.
- **Uses from project**: `affineUpperHalfPlane`
- **Used by**: `qParam_affineUpperHalfPlane`, `inv_smul_natScale_smul_eq_affine`
- **Visibility**: private
- **Lines**: 47–51
- **Notes**: —

### `private lemma Cox.qParam_affineUpperHalfPlane`
- **Type**: `… : Periodic.qParam 1 (affineUpperHalfPlane g s hg hs r τ) = exp (2πi · r/s) * Periodic.qParam ((g*s : ℕ) : ℝ) τ ^ (g*g)`
- **What**: The width-1 `q`-parameter of `(gτ + r)/s` is a root of unity times the `(g*s)`-th-root parameter of `τ` raised to `g²`.
- **How**: Unfold `Periodic.qParam`, split the exponent with `Complex.exp_add` and `Complex.exp_nat_mul`, `field_simp` with `g, s ≠ 0`.
- **Hypotheses**: `g, s > 0`.
- **Uses from project**: `affineUpperHalfPlane`, `coe_affineUpperHalfPlane`
- **Used by**: `cuspFunction_affine_j_eq`
- **Visibility**: private
- **Lines**: 53–70, proof body ≈ 13 lines
- **Notes**: No mathlib analogue found (searched `qParam_add`, `qParam_smul`, `qParam_vadd` in `Mathlib/Analysis/Complex/Periodic.lean`). Companion lemmas `Periodic.qParam_vadd`/`qParam_pos_real_smul` would make this two rewrites.

### `private lemma Cox.complex_mobius_scale_eq_affine`
- **Type**: `{n p q u v a b c d g r s z : ℂ} (hD : c*z + d ≠ 0) (hs : s ≠ 0) (h00 : p*(n*a) + q*c = g) (h01 : p*(n*b) + q*d = r) (h10 : u*(n*a) + v*c = 0) (h11 : u*(n*b) + v*d = s) : (p*(n*((a*z+b)/(c*z+d))) + q) / (u*(n*((a*z+b)/(c*z+d))) + v) = r/s + g/s * z`
- **What**: Pure field identity: if `!![p,q;u,v] * (n·!![a,b;c,d]) = !![g,r;0,s]` entrywise then the composed Möbius map is the affine map `z ↦ (gz + r)/s`.
- **How**: Compute numerator and denominator separately with `field_simp` + `linear_combination z * h00 + h01` / `z * h10 + h11`, then `field_simp; ring`.
- **Hypotheses**: denominators nonzero and the four matrix-entry equations.
- **Uses from project**: `[]`
- **Used by**: `inv_smul_natScale_smul_eq_affine`
- **Visibility**: private
- **Lines**: 72–90, proof body ≈ 12 lines
- **Notes**: **Verbatim duplicate** (identical name, statement, and proof) of the private `complex_mobius_scale_eq_affine` at CoxMatrices/Basic.lean:699–717. CoxMatrices/Basic imports this file, so making this one public removes the copy.

### `private lemma Cox.coe_inv_smul_natScale_smul`
- **Type**: `(N : ℕ+) (γ δ : SL(2, ℤ)) (τ : ℍ) : ((δ⁻¹ • natScaleUpperHalfPlane N (γ • τ) : ℍ) : ℂ) = (δ⁻¹₀₀ * (N * ((γ₀₀ τ + γ₀₁)/(γ₁₀ τ + γ₁₁))) + δ⁻¹₀₁) / (δ⁻¹₁₀ * (…) + δ⁻¹₁₁)`
- **What**: Explicit formula for `δ⁻¹ · N · γ · τ` as a complex number.
- **How**: `UpperHalfPlane.coe_specialLinearGroup_apply` twice and `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `natScaleUpperHalfPlane`, `coe_natScaleUpperHalfPlane`
- **Used by**: `inv_smul_natScale_smul_eq_affine`
- **Visibility**: private
- **Lines**: 92–106, proof body ≈ 3 lines
- **Notes**: Statement is 12 lines of casts for a 3-line proof; same expansion appears inline at CoxMatrices/Basic.lean:733–747 (`hγcoe` + `change`).

### `private lemma Cox.inv_smul_natScale_smul_eq_affine`
- **Type**: `(N : ℕ+) (γ δ : SL(2,ℤ)) (g s : ℕ) (hg) (hs) (r : ℤ) (hmat : (δ⁻¹).1 * !![N*γ₀₀, N*γ₀₁; γ₁₀, γ₁₁] = !![g, r; 0, s]) (τ : ℍ) : δ⁻¹ • natScaleUpperHalfPlane N (γ • τ) = affineUpperHalfPlane g s hg hs r τ`
- **What**: If `δ⁻¹` triangularizes `N·γ` to `!![g, r; 0, s]` then `δ⁻¹ N γ τ = (gτ + r)/s` in ℍ.
- **How**: Extract the four entry equations from `hmat` by `congrFun` + `Matrix.mul_apply, Fin.sum_univ_two`, cast to ℂ, get `γ₁₀τ + γ₁₁ ≠ 0` from `UpperHalfPlane.denom_ne_zero`, then `UpperHalfPlane.ext` with `coe_inv_smul_natScale_smul`, `coe_affineUpperHalfPlane`, `complex_mobius_scale_eq_affine`.
- **Hypotheses**: `g, s > 0`, the matrix identity.
- **Uses from project**: `natScaleUpperHalfPlane`, `affineUpperHalfPlane`, `coe_inv_smul_natScale_smul`, `coe_affineUpperHalfPlane`, `complex_mobius_scale_eq_affine`
- **Used by**: `levelJ_comp_eq_affine_of_normalization`
- **Visibility**: private
- **Lines**: 108–129, proof body ≈ 14 lines
- **Notes**: Same argument as `levelJ_smul_eq_j_act_of_normalization` (CoxMatrices/Basic.lean:719–760) with `!![g,r;0,s]` in place of `σ.mobiusMatrix`.

### `private lemma Cox.cuspFunction_affine_j_eq`
- **Type**: `(g s : ℕ) (hg) (hs) (r : ℤ) {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) : cuspFunction ((g*s : ℕ) : ℝ) (fun τ ↦ j (affineUpperHalfPlane g s hg hs r τ)) q = cuspFunction 1 j (exp(2πi r/s) * q ^ (g*g))`
- **What**: For `0 < |q| < 1`, the width-`gs` cusp function of `j((gτ+r)/s)` at `q` equals the width-1 cusp function of `j` at `ζ q^{g²}`.
- **How**: Take `τ := invQParam (gs) q ∈ ℍ` (`Periodic.im_invQParam_pos_of_norm_lt_one`), evaluate the LHS by `Periodic.cuspFunction_eq_of_nonzero` and `ofComplex_apply_of_im_pos`, rewrite the argument by `qParam_affineUpperHalfPlane` and `Periodic.qParam_right_inv`, and close with `eq_cuspFunction … ModularFunction.j_periodic`.
- **Hypotheses**: `g, s > 0`, `0 < ‖q‖ < 1`.
- **Uses from project**: `affineUpperHalfPlane`, `qParam_affineUpperHalfPlane`, `j`, `ModularFunction.j_periodic`
- **Used by**: `affine_j_cuspFunction_meromorphicAt`
- **Visibility**: private
- **Lines**: 131–157, proof body ≈ 21 lines
- **Notes**: —

### `private lemma Cox.first_column_ne_zero_of_det_ne_zero_aux`
- **Type**: `{M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det ≠ 0) : M 0 0 ≠ 0 ∨ M 1 0 ≠ 0`
- **What**: A nonsingular 2×2 matrix has a nonzero first column.
- **How**: `by_contra`, `Matrix.det_fin_two`, `ring`.
- **Hypotheses**: `det M ≠ 0`.
- **Uses from project**: `[]`
- **Used by**: `exists_positive_upper_triangularization_aux`
- **Visibility**: private
- **Lines**: 159–166, proof body ≈ 6 lines
- **Notes**: —

### `private lemma Cox.exists_sl2_inv_mul_first_column_gcd_aux`
- **Type**: `(M : Matrix (Fin 2) (Fin 2) ℤ) (hG : (Int.gcd (M 0 0) (M 1 0) : ℤ) ≠ 0) : ∃ δ : SL(2,ℤ), ((δ⁻¹).1 * M) 0 0 = Int.gcd (M 0 0) (M 1 0) ∧ ((δ⁻¹).1 * M) 1 0 = 0`
- **What**: Row-reduction step: some `δ ∈ SL₂(ℤ)` sends the first column of `M` to `(gcd, 0)ᵀ`.
- **How**: `u = A/G, v = C/G` are coprime (`isCoprime_div_gcd_div_gcd_of_gcd_ne_zero`), so `IsCoprime.exists_SL2_col` gives `δ` with first column `(u, v)`; compute `δ⁻¹ M` entries via `Matrix.SpecialLinearGroup.SL2_inv_expl` and `linear_combination` with the determinant relation.
- **Hypotheses**: first column of `M` not both zero.
- **Uses from project**: `[]`
- **Used by**: `exists_positive_upper_triangularization_aux`
- **Visibility**: private
- **Lines**: 168–201, proof body ≈ 28 lines
- **Notes**: Rides on mathlib `IsCoprime.exists_SL2_col` (`Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean:429`) and `isCoprime_div_gcd_div_gcd_of_gcd_ne_zero` (`Mathlib/RingTheory/EuclideanDomain.lean:60`). This is the row (left-multiplication) form of the gcd step that `HermiteNormalForm.lean:123 exists_hnf_transform` performs on columns (right-multiplication).

### `private lemma Cox.matrix_eq_upper_triangular_aux`
- **Type**: `(B : Matrix (Fin 2) (Fin 2) ℤ) (G : ℤ) (h00 : B 0 0 = G) (h10 : B 1 0 = 0) : B = !![G, B 0 1; 0, B 1 1]`
- **What**: A 2×2 matrix with prescribed first column is the displayed literal.
- **How**: `ext; fin_cases`.
- **Hypotheses**: two entry equations.
- **Uses from project**: `[]`
- **Used by**: `exists_positive_upper_triangularization_aux`
- **Visibility**: private
- **Lines**: 203–210, proof body ≈ 6 lines
- **Notes**: Exactly `Matrix.eta_fin_two B` (`Mathlib/LinearAlgebra/Matrix/Notation.lean:464`) followed by `rw [h00, h10]`; junk wrapper.

### `private lemma Cox.exists_positive_upper_triangularization_aux`
- **Type**: `(N : ℕ+) (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = N) : ∃ (δ : SL(2,ℤ)) (g s : ℕ), 0 < g ∧ 0 < s ∧ g * s = N ∧ ∃ r : ℤ, (δ⁻¹).1 * M = !![g, r; 0, s]`
- **What**: Left `SL₂(ℤ)`-reduction of an integer matrix of determinant `N` to upper-triangular form with positive diagonal `(g, s)`, `gs = N`.
- **How**: `first_column_ne_zero_of_det_ne_zero_aux` gives `G = gcd > 0`; `exists_sl2_inv_mul_first_column_gcd_aux` gives `δ`; `Matrix.det_mul`, `SpecialLinearGroup.det_coe` give `G * S = N`, hence `S > 0` (`Int.pos_of_mul_pos_right`); conclude with `natAbs` and `matrix_eq_upper_triangular_aux`.
- **Hypotheses**: `det M = N > 0`.
- **Uses from project**: `first_column_ne_zero_of_det_ne_zero_aux`, `exists_sl2_inv_mul_first_column_gcd_aux`, `matrix_eq_upper_triangular_aux`
- **Used by**: `exists_levelJ_cusp_normalization`
- **Visibility**: private
- **Lines**: 212–241, proof body ≈ 26 lines
- **Notes**: This is the (non-reduced) row Hermite normal form for `Fin 2`. The project already proves the column version publicly (`Matrix.exists_right_mul_isColumnHermiteNormalForm`, HermiteNormalForm.lean:173, with `0 ≤ r < s` reduction) and CoxMatrices/Basic.lean:452 `coxRepresentative_normalization` proves the *identical* left normalization `(δ⁻¹).1 * !![N γ₀₀, N γ₀₁; γ₁₀, γ₁₁] = σ.mobiusMatrix` for a `CoxMatrix σ` (which is `!![a, b; 0, d]`, `ad = N`) by transposing the HNF (`matrixStar`). Lines 159–257 (≈100 lines) re-derive this. Mathlib has no `Fin 2` HNF (searched `Hermite`, `HermiteNormal`, `upper triangular … SpecialLinearGroup`: only number-field Hermite theorems).

### `private lemma Cox.exists_levelJ_cusp_normalization`
- **Type**: `(N : ℕ+) (γ : SL(2,ℤ)) : ∃ (δ : SL(2,ℤ)) (g s : ℕ), 0 < g ∧ 0 < s ∧ g * s = N ∧ ∃ r : ℤ, (δ⁻¹).1 * !![N*γ₀₀, N*γ₀₁; γ₁₀, γ₁₁] = !![g, r; 0, s]`
- **What**: Specialization of the triangularization to `M = N·γ` (row-scaled), whose determinant is `N`.
- **How**: `Matrix.det_fin_two_of` and `linear_combination N * hγ` for the determinant, then the previous lemma.
- **Hypotheses**: none.
- **Uses from project**: `exists_positive_upper_triangularization_aux`
- **Used by**: `levelJ_meromorphicAt_cusp`
- **Visibility**: private
- **Lines**: 243–257, proof body ≈ 9 lines
- **Notes**: Same conclusion shape as `coxRepresentative_normalization` (CoxMatrices/Basic.lean:452).

### `private lemma Cox.levelJ_comp_eq_affine_of_normalization`
- **Type**: `… (hmat : (δ⁻¹).1 * !![N*γ₀₀, N*γ₀₁; γ₁₀, γ₁₁] = !![g, r; 0, s]) : (fun τ ↦ levelJ N (γ • τ)) = fun τ ↦ j (affineUpperHalfPlane g s hg hs r τ)`
- **What**: `j(N γ τ) = j((gτ + r)/s)` as functions, given the triangularization.
- **How**: `j` is `δ⁻¹`-invariant (`j_modularGroup_smul`), then `inv_smul_natScale_smul_eq_affine`.
- **Hypotheses**: the matrix identity.
- **Uses from project**: `levelJ`, `natScaleUpperHalfPlane`, `affineUpperHalfPlane`, `j`, `j_modularGroup_smul`, `inv_smul_natScale_smul_eq_affine`
- **Used by**: `levelJ_meromorphicAt_cusp`
- **Visibility**: private
- **Lines**: 259–273, proof body ≈ 6 lines
- **Notes**: Parallel to `levelJ_smul_eq_j_act_of_normalization` (CoxMatrices/Basic.lean:719).

### `private lemma Cox.affine_j_cuspFunction_meromorphicAt`
- **Type**: `(g s : ℕ) (hg) (hs) (r : ℤ) : MeromorphicAt (cuspFunction ((g*s : ℕ) : ℝ) (fun τ ↦ j (affineUpperHalfPlane g s hg hs r τ))) 0`
- **What**: The width-`gs` cusp function of `j((gτ + r)/s)` is meromorphic at 0.
- **How**: It agrees on `0 < ‖q‖ < 1` with `(cuspFunction 1 j) ∘ φ`, `φ q = ζ q^{g²}` analytic with `φ 0 = 0`; `MeromorphicAt.comp_analyticAt` on `j_cuspFunction_meromorphicAt`, then `MeromorphicAt.congr` with `cuspFunction_affine_j_eq` on the punctured unit ball.
- **Hypotheses**: `g, s > 0`.
- **Uses from project**: `affineUpperHalfPlane`, `j`, `j_cuspFunction_meromorphicAt`, `cuspFunction_affine_j_eq`
- **Used by**: `levelJ_meromorphicAt_cusp`
- **Visibility**: private
- **Lines**: 275–297, proof body ≈ 18 lines
- **Notes**: Rides on mathlib `MeromorphicAt.comp_analyticAt` (`Mathlib/Analysis/Meromorphic/Basic.lean`).

### `private lemma Cox.levelJ_meromorphicAt_cusp`
- **Type**: `(N : ℕ+) (γ : SL(2, ℤ)) : MeromorphicAt (cuspFunction (N : ℝ) (fun τ ↦ levelJ N (γ • τ))) 0`
- **What**: Every `SL₂(ℤ)`-transform of `j(Nτ)` has meromorphic width-`N` cusp expansion.
- **How**: Triangularize (`exists_levelJ_cusp_normalization`), rewrite the function (`levelJ_comp_eq_affine_of_normalization`) and `N = g*s`, apply `affine_j_cuspFunction_meromorphicAt`.
- **Hypotheses**: none.
- **Uses from project**: `levelJ`, `exists_levelJ_cusp_normalization`, `levelJ_comp_eq_affine_of_normalization`, `affine_j_cuspFunction_meromorphicAt`
- **Used by**: `levelJModularFunction`
- **Visibility**: private
- **Lines**: 299–305, proof body ≈ 4 lines
- **Notes**: —

### `theorem Cox.levelJ_mdifferentiable`
- **Type**: `(N : ℕ+) : MDiff (levelJ N)`
- **What**: `j(Nτ)` is holomorphic on ℍ.
- **How**: `mdifferentiable_iff` and `jN_differentiableAt`.
- **Hypotheses**: none.
- **Uses from project**: `levelJ`, `jN_differentiableAt`
- **Used by**: `levelJModularFunction`
- **Visibility**: public
- **Lines**: 308–310, proof body ≈ 2 lines
- **Notes**: External: Construction.lean:217, UpperHalfPlaneFunctionField.lean:225, ModularFunctionField.lean:29. The migration doc names this as the single shared holomorphy theorem.

### `def Cox.levelJModularFunction`
- **Type**: `(N : ℕ+) : ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ))`
- **What**: The bundled level-`N` modular function `j(Nτ)`.
- **How**: `ModularFunction.ofGamma0CuspData N (levelJ N)` with normal form from `MeromorphicField.ofHolomorphic`/`toFun_ofHolomorphic` (`meromorphicNFOn_iff_exists`), invariance `jN_slash_invariant`, and `levelJ_meromorphicAt_cusp`.
- **Hypotheses**: none.
- **Uses from project**: `levelJ`, `ModularFunction.ofGamma0CuspData`, `MeromorphicField.meromorphicNFOn_iff_exists`, `MeromorphicField.ofHolomorphic`, `MeromorphicField.toFun_ofHolomorphic`, `levelJ_mdifferentiable`, `jN_slash_invariant`, `levelJ_meromorphicAt_cusp`
- **Used by**: `coe_levelJModularFunction`, `levelJ_cuspData`
- **Visibility**: public
- **Lines**: 313–319
- **Notes**: External: ModularFunctionField.lean:162–163, 184 only. The `meromorphic'` witness pattern `(meromorphicNFOn_iff_exists _).mpr ⟨ofHolomorphic _ h, toFun_ofHolomorphic _ h⟩` also appears at JInvariant.lean:46–47 — a missing constructor `ModularFunction.ofGamma0Holomorphic (hf : MDiff f) …` (or `MeromorphicField.meromorphicNFOn_of_mdifferentiable`) would remove the 3-line witness.

### `@[simp] theorem Cox.coe_levelJModularFunction`
- **Type**: `(N : ℕ+) : (levelJModularFunction N : ℍ → ℂ) = levelJ N`
- **What**: The underlying function of the bundle is `levelJ N`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `levelJModularFunction`, `levelJ`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 322–323
- **Notes**: Unused anywhere (ModularFunctionField.lean:166 uses `change … ; rfl` instead). Expected `coe` companion; keep, but the consumer should use it.

### `theorem Cox.levelJ_cuspData`
- **Type**: `(N : ℕ+) : CuspData N (levelJ N)`
- **What**: Raw cusp data for `j(Nτ)`.
- **How**: `CuspData.of_modularFunction N (levelJModularFunction N)`.
- **Hypotheses**: none.
- **Uses from project**: `CuspData`, `levelJ`, `CuspData.of_modularFunction`, `levelJModularFunction`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 326–327, proof body ≈ 1 line
- **Notes**: External: CoxMatrices/Basic.lean:633 (`rightCosetEval` definition), :697, AnalyticSupport.lean:30. Load-bearing.

## File Summary
- Total declarations: 22 (5 defs, 17 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `levelJ` (6), `affineUpperHalfPlane` (6), `natScaleUpperHalfPlane` (4)
- Unused declarations (not used by anything in this file): `coe_levelJModularFunction` (unused everywhere), `levelJ_cuspData` (external only)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: `exists_sl2_inv_mul_first_column_gcd_aux` 28, `exists_positive_upper_triangularization_aux` 26, `cuspFunction_affine_j_eq` 21)

## Observations

### Mathlib API candidates
- `matrix_eq_upper_triangular_aux` (203–210) = `Matrix.eta_fin_two` (`Mathlib/LinearAlgebra/Matrix/Notation.lean:464`) + two rewrites.
- `natScaleUpperHalfPlane` (29–33) = mathlib `UpperHalfPlane.posRealAction` (`Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean:197`) applied to `⟨N, _⟩`; the file already uses this action at line 43.
- `exists_sl2_inv_mul_first_column_gcd_aux` / `exists_positive_upper_triangularization_aux` (168–241): mathlib has only the primitive `IsCoprime.exists_SL2_col` (`Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean:429`); no `Fin 2` Hermite normal form (searched `Hermite`, `HermiteNormal`, `exists_SL2`, `upper triangular`). The *project* has it (HermiteNormalForm.lean:173 `Matrix.exists_right_mul_isColumnHermiteNormalForm`, column form) — see Moral duplicates.
- `affine_j_cuspFunction_meromorphicAt` already rides on `MeromorphicAt.comp_analyticAt` (`Mathlib/Analysis/Meromorphic/Basic.lean`); `cuspFunction_affine_j_eq` on `Periodic.im_invQParam_pos_of_norm_lt_one` (`Mathlib/Analysis/Complex/UpperHalfPlane/Exp.lean`), `Periodic.qParam_right_inv`, `Periodic.cuspFunction_eq_of_nonzero` (`Mathlib/Analysis/Complex/Periodic.lean`).
- `qParam_affineUpperHalfPlane`: no analogue found (searched `qParam_add`, `qParam_vadd`, `qParam_smul` in `Mathlib/Analysis/Complex/Periodic.lean`).
- `levelJModularFunction`: rides on the project's `ModularFunction.ofGamma0CuspData` (Congruence.lean:115); no mathlib "modular function" exists.

### Missing API / repeated patterns
- **Left `SL₂(ℤ)`-triangularization** is proved three times in the project: here (159–257, ≈100 lines, gcd by hand), HermiteNormalForm.lean:123–180 (column form, with reduction), and CoxMatrices/Basic.lean:343–460 (`exists_sl_right_mul_isColumnHermiteNormalForm_aux`, `coxRepresentative_normalization`, via `matrixStar` transposition of the HNF). A public `Matrix.exists_SL2_inv_mul_eq_upperTriangular (M) (hdet : M.det = N) : ∃ δ : SL(2,ℤ), ∃ g s r, 0 < g ∧ 0 < s ∧ g*s = N ∧ (δ⁻¹).1 * M = !![g, r; 0, s]` in HermiteNormalForm.lean would let this file import HNF and delete lines 159–257, and would replace `exists_sl_right_mul_isColumnHermiteNormalForm_aux`-to-left bridging in CoxMatrices.
- **Möbius-to-affine computation**: `complex_mobius_scale_eq_affine` (72–90) is verbatim at CoxMatrices/Basic.lean:699–717; `coe_inv_smul_natScale_smul` + `inv_smul_natScale_smul_eq_affine` (92–129) is re-done inline at CoxMatrices/Basic.lean:719–760. Missing public `levelJ_smul_eq_j_affine_of_mat` (this file's `levelJ_comp_eq_affine_of_normalization` made public with `σ.act`-compatible form) would serve `rightCosetEval_equiv`.
- `levelJ` lacks `levelJ_apply`/`coe_levelJ` (`levelJ N τ = j ⟨N * τ, _⟩`); consumers use `change`.
- `ModularFunction` lacks a holomorphic constructor (`ofGamma0Holomorphic`), see `levelJModularFunction` Notes.

### Junk candidates
- `matrix_eq_upper_triangular_aux` (203–210): `Matrix.eta_fin_two` wrapper.
- `coe_levelJModularFunction` (322–323): unused anywhere; keep as `simp` API but its one natural consumer (ModularFunctionField.lean:166) bypasses it.
- `coe_inv_smul_natScale_smul` (92–106): a 12-line statement whose proof is `rw [..]; rfl`; would vanish with a `levelJ_apply`/`coe_smul` simp set.
- Blank double lines at 27–28 (style).

### Moral duplicates within this batch
- `complex_mobius_scale_eq_affine` (72) ≡ CoxMatrices/Basic.lean:699 (exact copy).
- `exists_levelJ_cusp_normalization` (243) ≈ `coxRepresentative_normalization` (CoxMatrices/Basic.lean:452): same normalization, one produces `!![g,r;0,s]`, the other `σ.mobiusMatrix` (which is `!![a,b;0,d]` with `0 ≤ b < d`).
- `levelJ_comp_eq_affine_of_normalization` (259) ≈ `levelJ_smul_eq_j_act_of_normalization` (CoxMatrices/Basic.lean:719).
- `natScaleUpperHalfPlane` (29) ≈ `zN` (CoxMatrices/Basic.lean:725) ≈ the anonymous point in `jN` (jLevelN.lean:38).
- `affineUpperHalfPlane g s r` (40) ≈ `CoxMatrix.act` for `!![g, r; 0, s]`.

### Generalization notes
- `exists_positive_upper_triangularization_aux` (212–241): nothing uses `N : ℕ+` beyond `det M > 0`; the natural statement is for any `M` with `M.det ≠ 0` (giving `g s = |det M|`), matching `Matrix.exists_right_mul_isColumnHermiteNormalForm`'s hypothesis `A.det ≠ 0`.
- `complex_mobius_scale_eq_affine` (72–90): holds in any field (`field_simp`, `linear_combination`, `ring` only); ℂ is incidental.
- `cuspFunction_affine_j_eq`/`affine_j_cuspFunction_meromorphicAt` (131–157, 275–297): `j` enters only through `ModularFunction.j_periodic` and `j_cuspFunction_meromorphicAt`; the argument is "any 1-periodic `f` with meromorphic width-1 cusp function has meromorphic width-`gs` cusp function after `τ ↦ (gτ+r)/s`", a general lemma that would also serve `rightCosetTranslate_cuspMeromorphicAt_aux` (Interpolation.lean:211).
