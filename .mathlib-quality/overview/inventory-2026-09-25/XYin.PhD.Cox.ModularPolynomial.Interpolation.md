# Inventory: XYin/PhD/Cox/ModularPolynomial/Interpolation.lean  (498 lines)

Cox's interpolation argument for Theorem 11.9(ii): for a level-`m` modular function `f` (given as `CuspData m f`), the un-normalized Lagrange sum `interpolationAt m hf τ = Σ_σ f|σ(τ) · ∏_{σ'≠σ} (X - j(σ'·τ))` (Cox (11.16)) has level-one coefficients (Exercise 11.11), the recovery formula `f(τ) = interpolationAt(j(mτ)) / ∂_X Φ_m(j(mτ), j(τ))` holds off the branch locus (Cox (11.17)), and hence every `f ∈ A₀(Γ₀(N))` is rational in `j(τ)` and `j(Nτ)` (`theorem_11_9_ii_pointwise`).

## Declarations

### `def Cox.interpolationAt`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : CuspData m f) (τ : ℍ) : Polynomial ℂ := ∑ σ : CoxMatrix m, Polynomial.C (rightCosetTranslate m hf (coxMatrixEquivRightCosets m σ) τ) * ∏ σ' ∈ Finset.univ.erase σ, (Polynomial.X - Polynomial.C (j (σ'.act τ)))`
- **What**: Cox (11.16): the numerator of the Lagrange interpolant of the values `f(γ_σ·τ)` at the nodes `j(σ·τ)`, without dividing by the node differences (so it is defined even when nodes collide).
- **How**: Sum over `C(m)` of the coset translate of `f` times the nodal polynomial of the other roots.
- **Hypotheses**: `f` has level-`m` cusp data (needed only for `rightCosetTranslate` to be well defined on cosets).
- **Uses from project**: `CuspData`, `CoxMatrix`, `CoxMatrix.act`, `rightCosetTranslate`, `coxMatrixEquivRightCosets`, `j`
- **Used by**: `interpolationAt_eq_cosets_aux`, `interpolationAt_smul_aux`, `interpolationFunction_map_eval_aux`, `interpolationFunction_coeff_apply_aux`, `interpolation_coeff_eq_function_coeff_aux`, `interpolation_coeff_meromorphicOnH_aux`, `interpolation_coeff_widthM_cuspMeromorphicAt_aux`, `interpolation_coeff_slashInvariant_aux`, `interpolation_coeff_widthOne_cuspMeromorphicAt_aux`, `interpolation_coeff_cuspData`, `recoveryFormula`, `interpolationAt_natDegree_lt`, `rationalInTwo_of_interpolation_coeff_rational`
- **Visibility**: public
- **Lines**: 23–30, proof body ≈ 0 lines
- **Notes**: Redundant `noncomputable`. Equals `∑ σ, C (a σ) * Lagrange.nodal (univ.erase σ) r`; differs from mathlib `Lagrange.interpolate` (Lagrange.lean:299), which divides each basis polynomial by `∏ (r σ - r σ')` (`basisDivisor`, :147) and therefore needs distinct nodes. No external users.

### `private def Cox.interpolationAtCosetsAux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : CuspData m f) (τ : ℍ) : Polynomial ℂ` (same sum indexed by `Gamma0RightCosets m` with `rightCosetEval`)
- **What**: The interpolant re-indexed by right cosets `Γ₀(m)\SL₂(ℤ)`.
- **How**: `∑ c, C (rightCosetTranslate m hf c τ) * ∏ d ∈ univ.erase c, (X - C (rightCosetEval m d τ))`.
- **Hypotheses**: as above.
- **Uses from project**: `CuspData`, `Gamma0RightCosets`, `rightCosetTranslate`, `rightCosetEval`
- **Used by**: `interpolationAt_eq_cosets_aux`, `interpolationAtCosets_smul_aux`, `interpolationAt_smul_aux`
- **Visibility**: private
- **Lines**: 32–38, proof body ≈ 0 lines
- **Notes**: Defined by `by classical; exact` (tactic-mode definition) — should be a term with `open Classical in` or a `DecidableEq` instance argument.

### `private theorem Cox.interpolationAt_eq_cosets_aux`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) (τ : ℍ) : interpolationAt m hf τ = interpolationAtCosetsAux m hf τ`
- **What**: The `C(m)`-indexed and coset-indexed interpolants agree.
- **How**: `Finset.sum_equiv`/`Finset.prod_equiv` along `coxMatrixEquivRightCosets m`, with `rightCosetEval_equiv` identifying nodes.
- **Hypotheses**: as above.
- **Uses from project**: `interpolationAt`, `interpolationAtCosetsAux`, `coxMatrixEquivRightCosets`, `rightCosetEval_equiv`, `CuspData`
- **Used by**: `interpolationAt_smul_aux`
- **Visibility**: private
- **Lines**: 40–52, proof body ≈ 9 lines
- **Notes**: Twin of `Construction.coxPhiAtJ_eq_rightCosetProduct` (Construction.lean:183–190).

### `private theorem Cox.interpolationAtCosets_smul_aux`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) (δ : SL(2, ℤ)) (τ : ℍ) : interpolationAtCosetsAux m hf (δ • τ) = interpolationAtCosetsAux m hf τ`
- **What**: The coset-indexed interpolant is `SL₂(ℤ)`-invariant in `τ`.
- **How**: Reindex the sum and the inner product by the coset permutation `rightCosetMul m δ`, using `rightCosetTranslate_smul` and `rightCosetEval_smul`.
- **Hypotheses**: as above.
- **Uses from project**: `interpolationAtCosetsAux`, `rightCosetMul`, `rightCosetTranslate_smul`, `rightCosetEval_smul`, `CuspData`
- **Used by**: `interpolationAt_smul_aux`
- **Visibility**: private
- **Lines**: 54–67, proof body ≈ 10 lines
- **Notes**: Twin of `Construction.coxPhiAtJ_sl2_smul` (Construction.lean:193–198).

### `private theorem Cox.interpolationAt_smul_aux`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) (δ : SL(2, ℤ)) (τ : ℍ) : interpolationAt m hf (δ • τ) = interpolationAt m hf τ`
- **What**: `SL₂(ℤ)`-invariance of the interpolant.
- **How**: Rewrite to the coset form twice and apply `interpolationAtCosets_smul_aux`.
- **Hypotheses**: as above.
- **Uses from project**: `interpolationAt`, `interpolationAt_eq_cosets_aux`, `interpolationAtCosets_smul_aux`, `CuspData`
- **Used by**: `interpolation_coeff_slashInvariant_aux`
- **Visibility**: private
- **Lines**: 69–73, proof body ≈ 2 lines
- **Notes**: —

### `private theorem Cox.rightCosetTranslate_meromorphicOnH_aux`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) (c : Gamma0RightCosets m) : ∀ z : ℂ, 0 < z.im → MeromorphicAt ((rightCosetTranslate m hf c) ∘ UpperHalfPlane.ofComplex) z`
- **What**: The coset translate `τ ↦ f(γ·τ)` is meromorphic on the upper half-plane.
- **How**: `Quotient.inductionOn`; `τ ↦ γ·τ` is holomorphic (`UpperHalfPlane.mdifferentiable_smul`, `mdifferentiable_coe`) hence analytic at `z` (`UpperHalfPlane.mdifferentiable_iff` + `DifferentiableOn.analyticAt` on the open set `upperHalfPlaneSet`), and `MeromorphicAt.comp_analyticAt` with the meromorphy of `f` (`hf.1`).
- **Hypotheses**: `f` meromorphic on `ℍ` (first component of `CuspData`).
- **Uses from project**: `CuspData`, `rightCosetTranslate`, `Gamma0RightCosets`
- **Used by**: `interpolation_coeff_meromorphicOnH_aux`
- **Visibility**: private
- **Lines**: 75–94, proof body ≈ 16 lines
- **Notes**: Only `hf.1` is used; a general lemma `MeromorphicOn.comp_sl2` for any `f` meromorphic on `ℍ` would be reusable (the analytic-`ofComplex` composition trick recurs at L207–209).

### `private def Cox.interpolationFunctionAux`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) : Polynomial (ℍ → ℂ)` (the interpolant with function-valued coefficients)
- **What**: The interpolant before evaluating `τ`, as a polynomial over `ℍ → ℂ`.
- **How**: `∑ σ, C (rightCosetTranslate m hf (equiv σ)) * ∏ σ' ∈ univ.erase σ, (X - C (fun τ ↦ j (σ'.act τ)))`.
- **Hypotheses**: as above.
- **Uses from project**: `CuspData`, `CoxMatrix`, `CoxMatrix.act`, `rightCosetTranslate`, `coxMatrixEquivRightCosets`, `j`
- **Used by**: `interpolationFunction_map_eval_aux`, `interpolationFunction_coeff_apply_aux`, `interpolationFunction_coeff_aux`, `interpolation_coeff_eq_function_coeff_aux`
- **Visibility**: private
- **Lines**: 96–103, proof body ≈ 0 lines
- **Notes**: Tactic-mode definition (`by classical; exact`). Twin of `Construction.coxPhiFunction` (Construction.lean:63–65).

### `private theorem Cox.interpolationFunction_map_eval_aux`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) (τ : ℍ) : (interpolationFunctionAux m hf).map (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ) = interpolationAt m hf τ`
- **What**: Evaluating the function coefficients at `τ` gives the pointwise interpolant.
- **How**: `simp` with `Polynomial.map_sum`, `Polynomial.map_prod`.
- **Hypotheses**: as above.
- **Uses from project**: `interpolationFunctionAux`, `interpolationAt`, `CuspData`
- **Used by**: `interpolationFunction_coeff_apply_aux`
- **Visibility**: private
- **Lines**: 105–112, proof body ≈ 3 lines
- **Notes**: Twin of `Construction.coxPhiFunction_map_eval` (Construction.lean:171–174).

### `private theorem Cox.interpolationFunction_coeff_apply_aux`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) (n : ℕ) (τ : ℍ) : (interpolationFunctionAux m hf).coeff n τ = (interpolationAt m hf τ).coeff n`
- **What**: Coefficientwise version of the previous lemma.
- **How**: `congrArg (coeff n)` + `Polynomial.coeff_map`.
- **Hypotheses**: as above.
- **Uses from project**: `interpolationFunctionAux`, `interpolationAt`, `interpolationFunction_map_eval_aux`, `CuspData`
- **Used by**: `interpolation_coeff_eq_function_coeff_aux`
- **Visibility**: private
- **Lines**: 114–119, proof body ≈ 2 lines
- **Notes**: Twin of `Construction.coxPhiFunction_coeff_apply` (Construction.lean:178–180).

### `private def Cox.interpolationRootProductAux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : Polynomial (ℍ → ℂ) := ∏ σ' ∈ Finset.univ.erase σ, (Polynomial.X - Polynomial.C (fun τ ↦ j (σ'.act τ)))`
- **What**: The function-valued nodal polynomial of all Cox roots except `σ`.
- **How**: Finite product of linear factors.
- **Hypotheses**: none.
- **Uses from project**: `CoxMatrix`, `CoxMatrix.act`, `j`
- **Used by**: `interpolationFunction_coeff_aux`, `interpolationRootProduct_coeff_mdifferentiable_aux`, `interpolationRootProduct_coeff_cuspMeromorphicAt_aux`, `interpolation_coeff_meromorphicOnH_aux`, `interpolation_coeff_widthM_cuspMeromorphicAt_aux`
- **Visibility**: private
- **Lines**: 121–124, proof body ≈ 0 lines
- **Notes**: Definitionally `Lagrange.nodal (univ.erase σ) (fun σ' τ ↦ j (σ'.act τ))`.

### `private theorem Cox.interpolationFunction_coeff_aux`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) (n : ℕ) : (interpolationFunctionAux m hf).coeff n = ∑ σ : CoxMatrix m, rightCosetTranslate m hf (coxMatrixEquivRightCosets m σ) * (interpolationRootProductAux m σ).coeff n`
- **What**: The `n`-th coefficient of the function-valued interpolant is the corresponding linear combination of the root-product coefficients.
- **How**: `simp` (`Polynomial.finset_sum_coeff`, `coeff_C_mul`).
- **Hypotheses**: as above.
- **Uses from project**: `interpolationFunctionAux`, `interpolationRootProductAux`, `rightCosetTranslate`, `coxMatrixEquivRightCosets`, `CuspData`, `CoxMatrix`
- **Used by**: `interpolation_coeff_meromorphicOnH_aux`, `interpolation_coeff_widthM_cuspMeromorphicAt_aux`
- **Visibility**: private
- **Lines**: 126–133, proof body ≈ 2 lines
- **Notes**: —

### `private theorem Cox.coxRoot_mdifferentiable_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : MDiff (fun τ : ℍ ↦ j (σ.act τ))`
- **What**: Each Cox root `j(σ·τ)` is holomorphic on `ℍ`.
- **How**: `rightCosetEval_equiv` and the holomorphy carried by `UpperHalfPlaneFunctionField.rightCosetFunction` (a `HolomorphicFunction` subtype element).
- **Hypotheses**: none.
- **Uses from project**: `CoxMatrix`, `CoxMatrix.act`, `j`, `rightCosetEval_equiv`, `UpperHalfPlaneFunctionField.rightCosetFunction`, `coxMatrixEquivRightCosets`
- **Used by**: `coxLinearFactor_coeff_mdifferentiable_aux`
- **Visibility**: private
- **Lines**: 135–139, proof body ≈ 2 lines
- **Notes**: Same fact as `hroot` inside `Construction.coxPhiFunction_coeff_mdifferentiable` (Construction.lean:219–221) and the private `UpperHalfPlaneFunctionField.rightCosetEval_mdifferentiable` (UpperHalfPlaneFunctionField.lean:221); should be one public lemma in CoxMatrices/Basic.lean or AnalyticSupport.lean.

### `private theorem Cox.coxLinearFactor_coeff_mdifferentiable_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) (n : ℕ) : MDiff ((Polynomial.X - Polynomial.C (fun τ : ℍ ↦ j (σ.act τ)) : Polynomial (ℍ → ℂ)).coeff n)`
- **What**: Every coefficient of the linear factor `X - j∘σ` is holomorphic.
- **How**: Case split `n = 0 / 1 / ≥ 2` exactly as in AnalyticSupport.lean:46–58, with `mdifferentiable_const` and `.neg`.
- **Hypotheses**: none.
- **Uses from project**: `CoxMatrix`, `CoxMatrix.act`, `j`, `coxRoot_mdifferentiable_aux`
- **Used by**: `interpolationRootProduct_coeff_mdifferentiable_aux`
- **Visibility**: private
- **Lines**: 141–154, proof body ≈ 10 lines
- **Notes**: Verbatim twin of `AnalyticSupport.coxLinearFactor_coeff_cuspMeromorphicAt` (AnalyticSupport.lean:40–58).

### `private theorem Cox.polynomial_prod_coeff_mdifferentiable_aux`
- **Type**: `{ι : Type*} (P : ι → Polynomial (ℍ → ℂ)) : ∀ s : Finset ι, (∀ i ∈ s, ∀ n, MDiff ((P i).coeff n)) → ∀ n, MDiff ((s.prod P).coeff n)`
- **What**: Coefficients of a finite product of polynomials with holomorphic coefficients are holomorphic.
- **How**: `Finset.induction_on`, `Polynomial.coeff_mul`, `MDifferentiable.sum` and `MDifferentiable.mul`.
- **Hypotheses**: coefficientwise holomorphy of each factor.
- **Uses from project**: `[]` (mathlib `MDifferentiable.sum`, `mdifferentiable_const`)
- **Used by**: `interpolationRootProduct_coeff_mdifferentiable_aux`
- **Visibility**: private
- **Lines**: 156–173, proof body ≈ 13 lines
- **Notes**: `classical`. Verbatim twin of `AnalyticSupport.polynomial_prod_coeff_cuspMeromorphicAt` (AnalyticSupport.lean:61–80). Is `Subring.prod_mem` in `Polynomial.liftsRing holomorphicFunctions.subtype` (Lifts.lean:209) + `lifts_iff_coeff_lifts` (:72).

### `private theorem Cox.interpolationRootProduct_coeff_mdifferentiable_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) (n : ℕ) : MDiff ((interpolationRootProductAux m σ).coeff n)`
- **What**: Coefficients of the root product are holomorphic.
- **How**: `polynomial_prod_coeff_mdifferentiable_aux` + `coxLinearFactor_coeff_mdifferentiable_aux`.
- **Hypotheses**: none.
- **Uses from project**: `interpolationRootProductAux`, `polynomial_prod_coeff_mdifferentiable_aux`, `coxLinearFactor_coeff_mdifferentiable_aux`, `CoxMatrix`, `j`
- **Used by**: `interpolation_coeff_meromorphicOnH_aux`
- **Visibility**: private
- **Lines**: 175–184, proof body ≈ 5 lines
- **Notes**: `classical`.

### `private theorem Cox.interpolation_coeff_eq_function_coeff_aux`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) (n : ℕ) : (fun τ ↦ (interpolationAt m hf τ).coeff n) = (interpolationFunctionAux m hf).coeff n`
- **What**: The pointwise coefficient function equals the function-valued coefficient.
- **How**: `funext` + `interpolationFunction_coeff_apply_aux`.
- **Hypotheses**: as above.
- **Uses from project**: `interpolationAt`, `interpolationFunctionAux`, `interpolationFunction_coeff_apply_aux`, `CuspData`
- **Used by**: `interpolation_coeff_meromorphicOnH_aux`, `interpolation_coeff_widthM_cuspMeromorphicAt_aux`
- **Visibility**: private
- **Lines**: 186–191, proof body ≈ 2 lines
- **Notes**: —

### `private theorem Cox.interpolation_coeff_meromorphicOnH_aux`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) (n : ℕ) : ∀ z : ℂ, 0 < z.im → MeromorphicAt ((fun τ ↦ (interpolationAt m hf τ).coeff n) ∘ UpperHalfPlane.ofComplex) z`
- **What**: Each coefficient of the interpolant is meromorphic on `ℍ`.
- **How**: Expand by `interpolationFunction_coeff_aux`; `MeromorphicAt.fun_sum` over `σ`; each term is (meromorphic coset translate, `rightCosetTranslate_meromorphicOnH_aux`) × (analytic root-product coefficient via `UpperHalfPlane.mdifferentiable_iff` + `DifferentiableOn.analyticAt`) using `MeromorphicAt.mul`.
- **Hypotheses**: `f` meromorphic on `ℍ`.
- **Uses from project**: `interpolationAt`, `interpolation_coeff_eq_function_coeff_aux`, `interpolationFunction_coeff_aux`, `rightCosetTranslate_meromorphicOnH_aux`, `coxMatrixEquivRightCosets`, `interpolationRootProduct_coeff_mdifferentiable_aux`, `CuspData`
- **Used by**: `interpolation_coeff_cuspData`
- **Visibility**: private
- **Lines**: 193–209, proof body ≈ 11 lines
- **Notes**: —

### `private theorem Cox.rightCosetTranslate_cuspMeromorphicAt_aux`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) (c : Gamma0RightCosets m) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (rightCosetTranslate m hf c)) 0`
- **What**: The coset translate of `f` is width-`m` cusp-meromorphic.
- **How**: `Quotient.inductionOn` and the third component `hf.2.2 γ` of the cusp data.
- **Hypotheses**: width-`m` cusp meromorphy of all `SL₂(ℤ)`-translates of `f`.
- **Uses from project**: `CuspData`, `rightCosetTranslate`, `Gamma0RightCosets`
- **Used by**: `interpolation_coeff_widthM_cuspMeromorphicAt_aux`
- **Visibility**: private
- **Lines**: 211–220, proof body ≈ 5 lines
- **Notes**: Generalizes `AnalyticSupport.rightCosetEval_cuspMeromorphicAt` (AnalyticSupport.lean:23–30), which is this lemma at `hf := levelJ_cuspData m`; the general version should be public and live in AnalyticSupport.lean.

### `private theorem Cox.interpolationRootProduct_coeff_cuspMeromorphicAt_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) (n : ℕ) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) ((interpolationRootProductAux m σ).coeff n)) 0`
- **What**: Coefficients of the root product are width-`m` cusp-meromorphic.
- **How**: `polynomial_prod_coeff_cuspMeromorphicAt` + `coxLinearFactor_coeff_cuspMeromorphicAt` over `univ.erase σ`.
- **Hypotheses**: none.
- **Uses from project**: `interpolationRootProductAux`, `polynomial_prod_coeff_cuspMeromorphicAt`, `coxLinearFactor_coeff_cuspMeromorphicAt`, `CoxMatrix`, `j`
- **Used by**: `interpolation_coeff_widthM_cuspMeromorphicAt_aux`
- **Visibility**: private
- **Lines**: 222–233, proof body ≈ 6 lines
- **Notes**: `classical`. Twin of `Construction.coxPhiFunction_coeff_widthM_cuspMeromorphicAt` (Construction.lean:239–247).

### `private theorem Cox.interpolation_coeff_widthM_cuspMeromorphicAt_aux`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) (n : ℕ) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (fun τ ↦ (interpolationAt m hf τ).coeff n)) 0`
- **What**: Each interpolant coefficient is width-`m` cusp-meromorphic.
- **How**: Expand by `interpolationFunction_coeff_aux`; `meromorphicAt_cuspFunction_finset_sum` with each summand `meromorphicAt_cuspFunction_mul` of the two previous lemmas.
- **Hypotheses**: as for `CuspData`.
- **Uses from project**: `interpolationAt`, `interpolation_coeff_eq_function_coeff_aux`, `interpolationFunction_coeff_aux`, `meromorphicAt_cuspFunction_finset_sum`, `meromorphicAt_cuspFunction_mul`, `rightCosetTranslate_cuspMeromorphicAt_aux`, `interpolationRootProduct_coeff_cuspMeromorphicAt_aux`, `rightCosetTranslate`, `coxMatrixEquivRightCosets`, `interpolationRootProductAux`, `CuspData`, `CoxMatrix`
- **Used by**: `interpolation_coeff_widthOne_cuspMeromorphicAt_aux`
- **Visibility**: private
- **Lines**: 235–250, proof body ≈ 11 lines
- **Notes**: —

### `private theorem Cox.interpolation_coeff_slashInvariant_aux`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) (n : ℕ) (δ : SL(2, ℤ)) : (fun τ ↦ (interpolationAt m hf τ).coeff n) ∣[(0 : ℤ)] δ = fun τ ↦ (interpolationAt m hf τ).coeff n`
- **What**: Each interpolant coefficient is weight-0 `SL₂(ℤ)`-invariant.
- **How**: `ModularForm.SL_slash_apply` at weight 0 and `interpolationAt_smul_aux`.
- **Hypotheses**: as above.
- **Uses from project**: `interpolationAt`, `interpolationAt_smul_aux`, `CuspData`
- **Used by**: `interpolation_coeff_widthOne_cuspMeromorphicAt_aux`, `interpolation_coeff_cuspData`
- **Visibility**: private
- **Lines**: 252–260, proof body ≈ 4 lines
- **Notes**: Twin of `Construction.coxPhiFunction_coeff_slashInvariant` (Construction.lean:201–207).

### `private theorem Cox.interpolation_coeff_widthOne_cuspMeromorphicAt_aux`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) (n : ℕ) : MeromorphicAt (cuspFunction 1 (fun τ ↦ (interpolationAt m hf τ).coeff n)) 0`
- **What**: Each interpolant coefficient is width-1 cusp-meromorphic.
- **How**: `meromorphicAt_cuspFunction_of_nat_mul` from width `m` plus 1-periodicity (`periodic_comp_of_slashInvariant_one`).
- **Hypotheses**: as above.
- **Uses from project**: `interpolationAt`, `meromorphicAt_cuspFunction_of_nat_mul`, `interpolation_coeff_widthM_cuspMeromorphicAt_aux`, `periodic_comp_of_slashInvariant_one`, `interpolation_coeff_slashInvariant_aux`, `CuspData`
- **Used by**: `interpolation_coeff_cuspData`
- **Visibility**: private
- **Lines**: 262–270, proof body ≈ 5 lines
- **Notes**: Verbatim twin of `Construction.coxPhiFunction_coeff_widthOne_cuspMeromorphicAt` (Construction.lean:251–257).

### `theorem Cox.interpolation_coeff_cuspData`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : CuspData m f) (n : ℕ) : LevelOneCuspData (fun τ ↦ (interpolationAt m hf τ).coeff n)`
- **What**: Cox Exercise 11.11: every coefficient of the interpolant is a level-one function in the analytic sense (meromorphic on `ℍ`, `SL₂(ℤ)`-invariant, meromorphic at the cusp).
- **How**: Assemble the three components from `interpolation_coeff_meromorphicOnH_aux`, `interpolation_coeff_slashInvariant_aux` and `interpolation_coeff_widthOne_cuspMeromorphicAt_aux`; the third needs the rewrite `(fun τ ↦ g (γ • τ)) = g` obtained from slash invariance (L283–288).
- **Hypotheses**: `f` has level-`m` cusp data.
- **Uses from project**: `CuspData`, `LevelOneCuspData`, `interpolationAt`, `interpolation_coeff_slashInvariant_aux`, `interpolation_coeff_meromorphicOnH_aux`, `interpolation_coeff_widthOne_cuspMeromorphicAt_aux`
- **Used by**: `theorem_11_9_ii_pointwise`
- **Visibility**: public
- **Lines**: 272–289, proof body ≈ 13 lines
- **Notes**: The `hfun` rewrite (L283–288) is exactly the packaging step that a `LevelOneCuspData.of_widthM` lemma would absorb (see Observations). No external users.

### `private theorem Cox.eval_derivative_prod_X_sub_C_at`
- **Type**: `{R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] (r : ι → R) (i : ι) : (Polynomial.derivative (∏ k : ι, (Polynomial.X - Polynomial.C (r k)))).eval (r i) = ∏ k ∈ Finset.univ.erase i, (r i - r k)`
- **What**: The derivative of the nodal polynomial at the node `r i` is the product of the differences to the other nodes.
- **How**: `simpa [Lagrange.nodal, Polynomial.eval_prod] using Lagrange.eval_nodal_derivative_eval_node_eq`.
- **Hypotheses**: `R` a commutative ring, finite index type.
- **Uses from project**: `[]`
- **Used by**: `recoveryFormula`, `modularDerivativeHolomorphic_apply`
- **Visibility**: private
- **Lines**: 291–299, proof body ≈ 3 lines
- **Notes**: STILL EXISTS (flagged in July). It is mathlib `Lagrange.eval_nodal_derivative_eval_node_eq` (Mathlib/LinearAlgebra/Lagrange.lean:605) + `Lagrange.eval_nodal` (:571); since `∏ k, (X - C (r k))` is definitionally `Lagrange.nodal univ r` (:543), both call sites can use mathlib directly.

### `private theorem Cox.eval_interpolation_sum_at`
- **Type**: `{R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] (a r : ι → R) (i : ι) : (∑ k : ι, Polynomial.C (a k) * ∏ l ∈ Finset.univ.erase k, (Polynomial.X - Polynomial.C (r l))).eval (r i) = a i * ∏ l ∈ Finset.univ.erase i, (r i - r l)`
- **What**: Evaluating the un-normalized Lagrange sum at the node `r i` leaves only the `i`-th term.
- **How**: `Polynomial.eval_finsetSum/eval_prod`, then `Finset.sum_eq_single i`: every other term contains the vanishing factor `r i - r i` (`Finset.prod_eq_zero`).
- **Hypotheses**: `R` a commutative ring; NO injectivity of `r` required.
- **Uses from project**: `[]`
- **Used by**: `recoveryFormula`
- **Visibility**: private
- **Lines**: 301–314, proof body ≈ 6 lines
- **Notes**: No mathlib analogue (searched Lagrange.lean: `eval_interpolate_at_node` :319 requires `Set.InjOn v s` and the normalized `Lagrange.basis`). General and PR-able as `Lagrange.eval_sum_C_mul_nodal_erase_at_node (hi : i ∈ s) : (∑ k ∈ s, C (a k) * nodal (s.erase k) r).eval (r i) = a i * (nodal (s.erase i) r).eval (r i)`.

### `theorem Cox.recoveryFormula`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : CuspData m f) (τ : ℍ) (hderiv : ((modularPolynomialC m).specializeY (j τ)).derivative.eval (levelJ m τ) ≠ 0) : f τ = (interpolationAt m hf τ).eval (levelJ m τ) / ((modularPolynomialC m).specializeY (j τ)).derivative.eval (levelJ m τ)`
- **What**: Cox (11.17): away from the branch locus, `f(τ)` is recovered as the interpolant at `j(mτ)` divided by `∂_X Φ_m(j(mτ), j(τ))`.
- **How**: Replace `j(mτ)` by `j(σ₀·τ)` (`j_act_sigmaZero`), the specialization by `coxPhiAtJ` (`modularPolynomialC_specializeY`), the derivative at the node by `eval_derivative_prod_X_sub_C_at`, the interpolant at the node by `eval_interpolation_sum_at`, `rightCosetTranslate_sigmaZero` for the `σ₀` value, then `mul_div_cancel_right₀`.
- **Hypotheses**: the node `j(mτ)` is simple, i.e. `∏_{σ≠σ₀} (j(σ₀τ) - j(στ)) ≠ 0` (fails at CM points, see docstring).
- **Uses from project**: `CuspData`, `modularPolynomialC`, `specializeY`, `j`, `levelJ`, `interpolationAt`, `j_act_sigmaZero`, `modularPolynomialC_specializeY`, `coxPhiAtJ`, `eval_derivative_prod_X_sub_C_at`, `sigmaZero`, `eval_interpolation_sum_at`, `rightCosetTranslate`, `coxMatrixEquivRightCosets`, `rightCosetTranslate_sigmaZero`, `CoxMatrix`
- **Used by**: `rationalInTwo_of_interpolation_coeff_rational`
- **Visibility**: public
- **Lines**: 316–333, proof body ≈ 8 lines
- **Notes**: `classical`. No external users.

### `private theorem Cox.interpolationAt_natDegree_lt`
- **Type**: `(m : ℕ+) {f} (hf : CuspData m f) (τ : ℍ) : (interpolationAt m hf τ).natDegree < Fintype.card (CoxMatrix m)`
- **What**: The interpolant has degree `< |C(m)|`.
- **How**: `Polynomial.natDegree_sum_le_of_forall_le` (BigOperators.lean) with each term of degree `≤ |C(m)| - 1` (`natDegree_C_mul_le`, degree of the erased product), and `|C(m)| > 0` from `sigmaZero`.
- **Hypotheses**: as above.
- **Uses from project**: `interpolationAt`, `CoxMatrix`, `sigmaZero`, `CuspData`
- **Used by**: `rationalInTwo_of_interpolation_coeff_rational`
- **Visibility**: private
- **Lines**: 339–349, proof body ≈ 8 lines
- **Notes**: `classical`. Section `Theorem119` (L335–496) with `open UpperHalfPlaneFunctionField`.

### `private theorem Cox.exists_commonDenominator_polynomialEval_of_natDegree_lt`
- **Type**: `{A : ℍ → Polynomial ℂ} {g h : ℍ → ℂ} (d : ℕ) (hdegree : ∀ τ, (A τ).natDegree < d) (hcoeff : ∀ n, RationalIn (fun τ ↦ (A τ).coeff n) g) : ∃ numerator : ℂ[X][Y], ∃ commonDenom : Polynomial ℂ, commonDenom ≠ 0 ∧ ∀ τ, commonDenom.eval (g τ) ≠ 0 → (A τ).eval (h τ) = numerator.evalEval (g τ) (h τ) / commonDenom.eval (g τ)`
- **What**: If a `τ`-family of polynomials of bounded degree has coefficients rational in `g`, then its value at `h(τ)` is a bivariate polynomial in `(g(τ), h(τ))` over a common denominator in `g(τ)`.
- **How**: `choose` numerators `p n` / denominators `q n`; `commonDenom := ∏_{n<d} q n`, `numerator := Σ_n C(p n · ∏_{k≠n} q k) X^n`; expand `(A τ).eval (h τ)` by `Polynomial.eval_eq_sum_range'` (Eval/Degree.lean:67), push `evalEval` through with `Polynomial.evalEval_finsetSum/_mul/_C/_pow/_X` (Bivariate.lean), `Finset.mul_prod_erase`, and `field_simp`.
- **Hypotheses**: uniform degree bound `d`; each coefficient function rational in `g`.
- **Uses from project**: `RationalIn`
- **Used by**: `rationalInTwo_of_interpolation_coeff_rational`
- **Visibility**: private
- **Lines**: 351–395, proof body ≈ 36 lines
- **Notes**: PROOF >30 LINES. `classical`. Uses raw `ℂ[X][Y]`/`evalEval` (mathlib convention, inner = `g τ`, outer = `h τ`) rather than `BivariatePolynomial.eval`. Nothing about `ℍ` or `ℂ` is used: generalizes verbatim to `{ι K : Type*} [Field K] {A : ι → K[X]} {g h : ι → K}`.

### `private theorem Cox.modularPolynomialC_derivative_evalEval`
- **Type**: `(m : ℕ+) (τ : ℍ) : ((modularPolynomialC m).derivative).evalEval (j τ) (levelJ m τ) = ((modularPolynomialC m).specializeY (j τ)).derivative.eval (levelJ m τ)`
- **What**: The `X`-derivative of `Φ_m` evaluated at `(j(mτ), j(τ))` equals the derivative of the specialization at `j(mτ)`.
- **How**: `Polynomial.derivative_map` (derivative commutes with coefficient maps) and `Polynomial.map_evalRingHom_eval`.
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialC`, `specializeY`, `j`, `levelJ`
- **Used by**: `interpolationDenominator_eval`
- **Visibility**: private
- **Lines**: 397–402, proof body ≈ 2 lines
- **Notes**: This is the sole bridge between the `evalEval` convention and the `specializeY` convention in the batch.

### `private def Cox.modularDerivativeHolomorphic`
- **Type**: `(m : ℕ+) : HolomorphicFunction := ∏ c ∈ Finset.univ.erase (baseRightCoset m), (rightCosetFunction m (baseRightCoset m) - rightCosetFunction m c)`
- **What**: The holomorphic function `τ ↦ ∏_{c ≠ base} (j(mτ) - j_c(τ))`, i.e. `∂_X Φ_m(j(mτ), j(τ))` as an element of the ring of holomorphic functions.
- **How**: Finite product in the subring `HolomorphicFunction`.
- **Hypotheses**: none.
- **Uses from project**: `HolomorphicFunction`, `baseRightCoset`, `rightCosetFunction`, `Gamma0RightCosets`
- **Used by**: `modularDerivativeHolomorphic_apply`, `modularDerivativeHolomorphic_ne_zero`, `interpolationDenominator_onCurve_ne_zero`
- **Visibility**: private
- **Lines**: 404–407, proof body ≈ 0 lines
- **Notes**: Tactic-mode definition (`by classical; exact`).

### `private theorem Cox.modularDerivativeHolomorphic_apply`
- **Type**: `(m : ℕ+) (τ : ℍ) : (modularDerivativeHolomorphic m).1 τ = ((modularPolynomialC m).specializeY (j τ)).derivative.eval (levelJ m τ)`
- **What**: Pointwise, the holomorphic product is the derivative of the specialized modular polynomial at `j(mτ)`.
- **How**: `modularPolynomialC_rightCosetProduct`, `rightCosetEval m (baseRightCoset m) τ = levelJ m τ` (by `simp [baseRightCoset]`), and `eval_derivative_prod_X_sub_C_at` at the base coset.
- **Hypotheses**: none.
- **Uses from project**: `modularDerivativeHolomorphic`, `modularPolynomialC`, `specializeY`, `j`, `levelJ`, `rightCosetEval`, `baseRightCoset`, `modularPolynomialC_rightCosetProduct`, `eval_derivative_prod_X_sub_C_at`, `rightCosetFunction`
- **Used by**: `interpolationDenominator_onCurve_ne_zero`
- **Visibility**: private
- **Lines**: 409–418, proof body ≈ 6 lines
- **Notes**: `classical`.

### `private theorem Cox.modularDerivativeHolomorphic_ne_zero`
- **Type**: `(m : ℕ+) : modularDerivativeHolomorphic m ≠ 0`
- **What**: The derivative function is not identically zero on `ℍ`.
- **How**: `Finset.prod_ne_zero_iff` in the integral domain `HolomorphicFunction`; each factor is nonzero because distinct cosets give distinct holomorphic conjugates (`rightCosetFunction_injective`).
- **Hypotheses**: none.
- **Uses from project**: `modularDerivativeHolomorphic`, `baseRightCoset`, `rightCosetFunction_injective`, `rightCosetFunction`
- **Used by**: `interpolationDenominator_onCurve_ne_zero`
- **Visibility**: private
- **Lines**: 420–429, proof body ≈ 7 lines
- **Notes**: `classical`. This is the separability of `Φ_m(X, j)` over the function field, in disguise.

### `private def Cox.interpolationDenominator`
- **Type**: `(m : ℕ+) (D : Polynomial ℂ) : ℂ[X][Y] := Polynomial.C D * (modularPolynomialC m).derivative`
- **What**: The bivariate denominator `D(Y) · ∂_X Φ_m(X, Y)` used in the rational representation.
- **How**: Product of the constant-in-`X` polynomial `C D` with the `X`-derivative of `Φ_m`.
- **Hypotheses**: none.
- **Uses from project**: `modularPolynomialC`
- **Used by**: `interpolationDenominator_eval`, `interpolationDenominator_onCurve_ne_zero`, `rationalInTwo_of_interpolation_coeff_rational`
- **Visibility**: private
- **Lines**: 431–432, proof body ≈ 0 lines
- **Notes**: Uses `ℂ[X][Y]` notation (= `BivariatePolynomial ℂ`).

### `private theorem Cox.interpolationDenominator_eval`
- **Type**: `(m : ℕ+) (D : Polynomial ℂ) (τ : ℍ) : (interpolationDenominator m D).evalEval (j τ) (levelJ m τ) = D.eval (j τ) * ((modularPolynomialC m).specializeY (j τ)).derivative.eval (levelJ m τ)`
- **What**: Evaluation of the denominator along the curve `(j(τ), j(mτ))`.
- **How**: `Polynomial.evalEval_mul`, `evalEval_C`, `modularPolynomialC_derivative_evalEval`.
- **Hypotheses**: none.
- **Uses from project**: `interpolationDenominator`, `modularPolynomialC`, `specializeY`, `j`, `levelJ`, `modularPolynomialC_derivative_evalEval`
- **Used by**: `interpolationDenominator_onCurve_ne_zero`, `rationalInTwo_of_interpolation_coeff_rational`
- **Visibility**: private
- **Lines**: 434–441, proof body ≈ 2 lines
- **Notes**: —

### `private theorem Cox.interpolationDenominator_onCurve_ne_zero`
- **Type**: `(m : ℕ+) {D : Polynomial ℂ} (hD : D ≠ 0) : (fun τ : ℍ ↦ (interpolationDenominator m D).evalEval (j τ) (levelJ m τ)) ≠ 0`
- **What**: For nonzero `D`, the denominator does not vanish identically along the modular curve.
- **How**: `evalJ D ≠ 0` by `evalJ_injective`; `modularDerivativeHolomorphic m ≠ 0`; their product is nonzero in the domain `HolomorphicFunction`; compare pointwise via `Subtype.ext`/`funext`, `evalJ_apply`, `modularDerivativeHolomorphic_apply`, `interpolationDenominator_eval`.
- **Hypotheses**: `D ≠ 0`.
- **Uses from project**: `interpolationDenominator`, `j`, `levelJ`, `evalJ`, `evalJ_injective`, `evalJ_apply`, `modularDerivativeHolomorphic`, `modularDerivativeHolomorphic_ne_zero`, `modularDerivativeHolomorphic_apply`, `interpolationDenominator_eval`
- **Used by**: `rationalInTwo_of_interpolation_coeff_rational`
- **Visibility**: private
- **Lines**: 443–462, proof body ≈ 15 lines
- **Notes**: —

### `private theorem Cox.rationalInTwo_of_interpolation_coeff_rational`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : CuspData m f) (hcoeff : ∀ n, RationalIn (fun τ ↦ (interpolationAt m hf τ).coeff n) j) : RationalInTwo f j (levelJ m)`
- **What**: If all interpolant coefficients are rational in `j`, then `f` is rational in `(j, j(m·))`.
- **How**: Common denominator lemma with `d := |C(m)|` and `interpolationAt_natDegree_lt`; denominator `interpolationDenominator m D`, nonvanishing from `interpolationDenominator_onCurve_ne_zero`; pointwise identity from `recoveryFormula` and `div_div`.
- **Hypotheses**: as stated.
- **Uses from project**: `CuspData`, `RationalIn`, `RationalInTwo`, `interpolationAt`, `j`, `levelJ`, `exists_commonDenominator_polynomialEval_of_natDegree_lt`, `CoxMatrix`, `interpolationAt_natDegree_lt`, `interpolationDenominator`, `interpolationDenominator_onCurve_ne_zero`, `interpolationDenominator_eval`, `recoveryFormula`
- **Used by**: `theorem_11_9_ii_pointwise`
- **Visibility**: private
- **Lines**: 464–483, proof body ≈ 13 lines
- **Notes**: —

### `theorem Cox.theorem_11_9_ii_pointwise`
- **Type**: `(N : ℕ+) (f : ModularFunction (CongruenceSubgroup.Gamma0 (N : ℕ))) : RationalInTwo f j (levelJ N)`
- **What**: Cox Theorem 11.9(ii): every modular function for `Γ₀(N)` is a rational function of `j(τ)` and `j(Nτ)` (pointwise, away from a nonzero denominator).
- **How**: `CuspData.of_modularFunction`, then `interpolation_coeff_cuspData` gives level-one coefficients, `CuspData.rationalInJ` (Theorem 11.9(i)) makes them rational in `j`, and `rationalInTwo_of_interpolation_coeff_rational`.
- **Hypotheses**: none.
- **Uses from project**: `ModularFunction`, `RationalInTwo`, `j`, `levelJ`, `CuspData.of_modularFunction`, `rationalInTwo_of_interpolation_coeff_rational`, `interpolation_coeff_cuspData`, `CuspData.rationalInJ`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 485–494, proof body ≈ 4 lines
- **Notes**: External user: ModularFunctionField.lean (1).

## File Summary
- Total declarations: 37 (6 defs, 31 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `interpolationAt` (13), `interpolationRootProductAux` (5), `interpolationFunctionAux` (4), `interpolationDenominator` (3), `modularDerivativeHolomorphic` (3), `interpolationAtCosetsAux` (3)
- Unused declarations (not used by anything in this file): `theorem_11_9_ii_pointwise` (used by ModularFunctionField.lean)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `exists_commonDenominator_polynomialEval_of_natDegree_lt` (36 lines)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `eval_derivative_prod_X_sub_C_at` (L291–299) still exists and is exactly `Lagrange.eval_nodal_derivative_eval_node_eq` (`Mathlib/LinearAlgebra/Lagrange.lean:605`) + `Lagrange.eval_nodal` (:571); `∏ k, (X - C (r k))` is definitionally `Lagrange.nodal univ r` (:543, `nodal_eq := rfl`). Its two callers (L328, L417) can call mathlib directly.
- `interpolationAt` (L24–30) is the un-normalized form of `Lagrange.interpolate` (Lagrange.lean:299, `∑ C (r i) * Lagrange.basis s v i` with `basis` normalized by `basisDivisor`, :147/:199). Not a duplicate: normalization needs distinct nodes, which fail at CM points (docstring L316–319). `eval_interpolation_sum_at` (L301–314) is the corresponding node-evaluation lemma without injectivity; no mathlib analogue (`Lagrange.eval_interpolate_at_node` :319 needs `Set.InjOn`). PR candidate in `Lagrange` namespace.
- `interpolationRootProductAux m σ` (L121–124) is `Lagrange.nodal (univ.erase σ) _`; `Lagrange.nodal_eq_mul_nodal_erase` (:583) and `derivative_nodal` (:595) are the relevant API.
- `exists_commonDenominator_polynomialEval_of_natDegree_lt` (L351–395) uses mathlib's `evalEval_*` simp set (Bivariate.lean:84,124,49,142,72) directly; it is the only place in the batch that manipulates `evalEval` algebraically. No mathlib analogue for the common-denominator statement (searched: `RatFunc`, `IsLocalization`, `common denominator`, `exists_common_denom`); it is a `Localization`/`IsFractionRing.exists_reduced_fraction`-flavoured fact, but stated pointwise it is genuinely new.
- `modularDerivativeHolomorphic_ne_zero` (L420–429) + `rightCosetFunction_injective` is the statement that `Φ_m(X, j)` is separable over the function field; over `FunctionField` this is `Polynomial.Separable` of `∏ (X - C (rightCosetRoot m c))` via `Polynomial.separable_prod_X_sub_C_iff'` (`Mathlib/FieldTheory/Separable.lean:324`) — Irreducibility.lean already has the product form (`modularPolynomialFunctionField_eq_product`, Irreducibility.lean:62–69).
### Missing API / repeated patterns
- Level-one descent pipeline (A15): L96–119 (function-valued polynomial, map/coeff evaluation), L135–184 (holomorphy of roots, linear factors, products), L211–233 (cusp meromorphy), L252–270 (slash invariance, width-1 descent) re-prove for `interpolationAt` what Construction.lean:62–65,170–180,215–257 and AnalyticSupport.lean:22–80 prove for `coxPhiFunction`. Collapsing lemmas: (1) `LevelOneCuspData.of_widthM {m} {f} (hH : ∀ z, 0 < z.im → MeromorphicAt (f ∘ ofComplex) z) (hslash : ∀ δ : SL(2,ℤ), f ∣[0] δ = f) (hcusp : MeromorphicAt (cuspFunction m f) 0) : LevelOneCuspData f` — absorbs L262–289 and Construction.lean:250–277; (2) a coefficient-closure lemma via `Polynomial.liftsRing S.subtype` (Lifts.lean:209) for `S := holomorphicFunctions` (FieldAction.lean:26) and a new `cuspMeromorphicSubring m` — absorbs L141–184 and AnalyticSupport.lean:40–80; (3) make `rightCosetTranslate_cuspMeromorphicAt_aux` (L211–220) public in AnalyticSupport.lean and derive `rightCosetEval_cuspMeromorphicAt` from it.
- Tactic-mode definitions `by classical; exact …` at L32–38, L96–103, L404–407: prefer `open Classical in` or explicit `[DecidableEq]`.
- The analytic-composition idiom `(UpperHalfPlane.mdifferentiable_iff.mp h).analyticAt (isOpen_upperHalfPlaneSet.mem_nhds hz)` appears at L87–88 and L207–209; a lemma `MDiff.analyticAt_ofComplex (hf : MDiff f) (hz : 0 < z.im) : AnalyticAt ℂ (f ∘ ofComplex) z` would serve both (and `rightCosetTranslate_meromorphicOnH_aux` L75–94 shrinks to 3 lines).
### Junk candidates
- `interpolationAtCosetsAux` + `interpolationAt_eq_cosets_aux` (L32–52): scaffolding used only for the `smul` lemma; acceptable but mirrors Construction.lean:183–198, so a shared "coset-indexed sum/product is `SL₂(ℤ)`-invariant" lemma would delete both copies.
- No dead code, `#check`s, or commented blocks.
### Moral duplicates within this batch
- `rightCosetTranslate_cuspMeromorphicAt_aux` (L211–220) ⊇ `AnalyticSupport.rightCosetEval_cuspMeromorphicAt` (AnalyticSupport.lean:23–30).
- `coxLinearFactor_coeff_mdifferentiable_aux` (L141–154) ≡ `AnalyticSupport.coxLinearFactor_coeff_cuspMeromorphicAt` (AnalyticSupport.lean:40–58).
- `polynomial_prod_coeff_mdifferentiable_aux` (L156–173) ≡ `AnalyticSupport.polynomial_prod_coeff_cuspMeromorphicAt` (AnalyticSupport.lean:61–80).
- `coxRoot_mdifferentiable_aux` (L135–139) ≡ `hroot` in Construction.lean:219–221 ≡ `UpperHalfPlaneFunctionField.rightCosetEval_mdifferentiable` (UpperHalfPlaneFunctionField.lean:221, private).
- `interpolationFunction_map_eval_aux`/`_coeff_apply_aux` (L105–119) ≡ `Construction.coxPhiFunction_map_eval`/`_coeff_apply` (Construction.lean:171–180).
- `interpolation_coeff_slashInvariant_aux` (L252–260) ≡ `Construction.coxPhiFunction_coeff_slashInvariant` (Construction.lean:201–207); `interpolation_coeff_widthOne_cuspMeromorphicAt_aux` (L262–270) ≡ `Construction.coxPhiFunction_coeff_widthOne_cuspMeromorphicAt` (Construction.lean:251–257).
### Generalization notes
- `eval_derivative_prod_X_sub_C_at`, `eval_interpolation_sum_at` (L291–314): already `CommRing`-general; the latter generalizes from `Finset.univ` to any `s` with `i ∈ s`.
- `exists_commonDenominator_polynomialEval_of_natDegree_lt` (L351–395): only `field_simp`/`eq_div_iff` use the field structure of `ℂ`; holds for any field `K` and any index type in place of `ℍ`.
- `rightCosetTranslate_meromorphicOnH_aux` (L75–94): only uses `hf.1` (meromorphy on `ℍ`), not the modular hypotheses.
- `interpolationAt` needs `hf` only for `rightCosetTranslate` well-definedness (the `Γ₀(m)`-invariance `hf.2.1`); the analytic parts of `CuspData` are irrelevant to the definition.
