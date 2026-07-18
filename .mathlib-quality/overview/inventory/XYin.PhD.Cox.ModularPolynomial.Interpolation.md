# Source: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/ModularPolynomial/Interpolation.lean
Project-internal imports: `XYin.PhD.Cox.ModularPolynomial.Construction`, `XYin.PhD.Cox.UpperHalfPlaneFunctionField`

All declarations live in `namespace Cox` inside a `noncomputable section`; the last block sits in `section Theorem119` which additionally opens `UpperHalfPlaneFunctionField`.

### `def interpolationAt`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (τ : ℍ) : Polynomial ℂ`
- **What**: Cox equation (11.16): the Lagrange-style interpolation polynomial Σ_σ f(γ_σ τ) · ∏_{σ'≠σ} (X − j(σ'τ)), whose value at j(στ) recovers f(γ_σ τ) times the separability denominator. Indexed by Cox matrices σ, with weights the coset translates of f.
- **How**: Finite sum over `CoxMatrix m` of constant-times-product of linear factors `X − C (j (σ'.act τ))`, weights given by `rightCosetTranslate` at the coset of σ.
- **Hypotheses**: f is a Γ₀(m)-modular function (meromorphic on ℍ, Γ₀(m)-invariant, meromorphic at the cusps).
- **Uses from project**: [`IsGamma0ModularFunction`, `CoxMatrix`, `CoxMatrix.act`, `rightCosetTranslate`, `coxMatrixEquivRightCosets`, `j`]
- **Used by**: `interpolationAt_eq_cosets_aux`, `interpolationAt_smul_aux`, `interpolationFunction_map_eval_aux`, `interpolationFunction_coeff_apply_aux`, `interpolation_coeff_eq_function_coeff_aux`, `interpolation_coeff_meromorphicOnH_aux`, `interpolation_coeff_widthM_cuspMeromorphicAt_aux`, `interpolation_coeff_slashInvariant_aux`, `interpolation_coeff_widthOne_cuspMeromorphicAt_aux`, `interpolation_coeff_isLevelOne`, `recoveryFormula`, `interpolationAt_natDegree_lt`, `rationalInTwo_of_interpolation_coeff_rational`
- **Visibility**: public
- **Lines**: 22–29 (definition 6 lines)
- **Notes**: explicitly `noncomputable`; has docstring

### `def interpolationAtCosetsAux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (τ : ℍ) : Polynomial ℂ`
- **What**: The same interpolation polynomial re-indexed over the abstract right cosets `Gamma0RightCosets m` instead of Cox matrix representatives — the form on which SL(2,ℤ)-equivariance is transparent.
- **How**: Sum over cosets c of `C (rightCosetTranslate m hf c τ) * ∏_{d≠c} (X − C (rightCosetEval m d τ))`.
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`IsGamma0ModularFunction`, `Gamma0RightCosets`, `rightCosetTranslate`, `rightCosetEval`]
- **Used by**: `interpolationAt_eq_cosets_aux`, `interpolationAtCosets_smul_aux`, `interpolationAt_smul_aux`
- **Visibility**: private
- **Lines**: 31–37 (definition ~5 lines)
- **Notes**: none

### `theorem interpolationAt_eq_cosets_aux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (τ : ℍ) : interpolationAt m hf τ = interpolationAtCosetsAux m hf τ`
- **What**: The Cox-matrix-indexed and coset-indexed interpolation polynomials coincide.
- **How**: Reindexes the sum and each erased product along the bijection `coxMatrixEquivRightCosets` using `Equiv.sum_comp` and `Finset.prod_equiv`, matching factors via `rightCosetEval_equiv` (j(σ'τ) equals the coset evaluation).
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`interpolationAt`, `interpolationAtCosetsAux`, `coxMatrixEquivRightCosets`, `rightCosetEval_equiv`, `rightCosetTranslate`, `rightCosetEval`, `j`, `CoxMatrix`]
- **Used by**: `interpolationAt_smul_aux`
- **Visibility**: private
- **Lines**: 39–65 (proof ~24 lines)
- **Notes**: none

### `theorem interpolationAtCosets_smul_aux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (δ : SL(2, ℤ)) (τ : ℍ) : interpolationAtCosetsAux m hf (δ • τ) = interpolationAtCosetsAux m hf τ`
- **What**: The coset-indexed interpolation polynomial is invariant under the full SL(2,ℤ)-action on τ — the source of level-one modularity of its coefficients.
- **How**: The action of δ permutes the right cosets via the project permutation `rightCosetMul m δ`; each summand transforms as term c (δ•τ) = term (e c) τ by the equivariance lemmas `rightCosetTranslate_smul` and `rightCosetEval_smul`, and `Equiv.sum_comp` reassembles the sum.
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`interpolationAtCosetsAux`, `Gamma0RightCosets`, `rightCosetMul`, `rightCosetTranslate`, `rightCosetEval`, `rightCosetTranslate_smul`, `rightCosetEval_smul`]
- **Used by**: `interpolationAt_smul_aux`
- **Visibility**: private
- **Lines**: 67–97 (proof ~28 lines)
- **Notes**: none

### `theorem interpolationAt_smul_aux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (δ : SL(2, ℤ)) (τ : ℍ) : interpolationAt m hf (δ • τ) = interpolationAt m hf τ`
- **What**: SL(2,ℤ)-invariance of the interpolation polynomial itself (Cox-matrix form).
- **How**: Transfers invariance from the coset form: rewrite both sides with `interpolationAt_eq_cosets_aux`, then apply `interpolationAtCosets_smul_aux`.
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`interpolationAt`, `interpolationAt_eq_cosets_aux`, `interpolationAtCosets_smul_aux`]
- **Used by**: `interpolation_coeff_slashInvariant_aux`
- **Visibility**: private
- **Lines**: 99–103 (proof 2 lines)
- **Notes**: none

### `theorem rightCosetTranslate_meromorphicOnH_aux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (c : Gamma0RightCosets m) : ∀ z : ℂ, 0 < z.im → MeromorphicAt ((rightCosetTranslate m hf c) ∘ UpperHalfPlane.ofComplex) z`
- **What**: Each coset translate τ ↦ f(γτ) of a Γ₀(m)-modular function is meromorphic at every point of the upper half-plane.
- **How**: By `Quotient.inductionOn` on the coset; the Möbius map w ↦ γ•w is holomorphic (`UpperHalfPlane.mdifferentiable_smul` composed with `mdifferentiable_coe`, turned into `AnalyticAt` via `mdifferentiable_iff` and the openness of the half-plane), so meromorphy of f transports along it by `MeromorphicAt.comp_analyticAt`.
- **Hypotheses**: f is a Γ₀(m)-modular function (only its meromorphy on ℍ, `hf.1`, is used).
- **Uses from project**: [`IsGamma0ModularFunction`, `Gamma0RightCosets`, `rightCosetTranslate`]
- **Used by**: `interpolation_coeff_meromorphicOnH_aux`
- **Visibility**: private
- **Lines**: 105–124 (proof ~17 lines)
- **Notes**: none

### `def interpolationFunctionAux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) : Polynomial (ℍ → ℂ)`
- **What**: The function-valued (τ-uniform) version of the interpolation polynomial: same formula as `interpolationAt` but as a polynomial over the ring of functions ℍ → ℂ, so that coefficients are honest functions of τ.
- **How**: Same Lagrange sum with `Polynomial.C` applied to whole functions rather than values.
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`IsGamma0ModularFunction`, `CoxMatrix`, `CoxMatrix.act`, `rightCosetTranslate`, `coxMatrixEquivRightCosets`, `j`]
- **Used by**: `interpolationFunction_map_eval_aux`, `interpolationFunction_coeff_aux`, `interpolation_coeff_eq_function_coeff_aux`
- **Visibility**: private
- **Lines**: 126–133 (definition ~6 lines)
- **Notes**: none

### `theorem interpolationFunction_map_eval_aux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (τ : ℍ) : (interpolationFunctionAux m hf).map (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ) = interpolationAt m hf τ`
- **What**: Evaluating the function-valued interpolation polynomial coefficientwise at τ gives the pointwise interpolation polynomial `interpolationAt`.
- **How**: `Polynomial.map` distributes over the defining sum and products (`Polynomial.map_sum`, `Polynomial.map_prod`), and the evaluation ring hom sends each constant function to its value.
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`interpolationFunctionAux`, `interpolationAt`]
- **Used by**: `interpolationFunction_coeff_apply_aux`
- **Visibility**: private
- **Lines**: 135–142 (proof 3 lines)
- **Notes**: none

### `theorem interpolationFunction_coeff_apply_aux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (n : ℕ) (τ : ℍ) : (interpolationFunctionAux m hf).coeff n τ = (interpolationAt m hf τ).coeff n`
- **What**: The n-th coefficient of the function-valued polynomial, evaluated at τ, is the n-th coefficient of the pointwise polynomial at τ.
- **How**: Takes the n-th coefficient of the map-evaluation identity `interpolationFunction_map_eval_aux` via `congrArg`.
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`interpolationFunctionAux`, `interpolationAt`, `interpolationFunction_map_eval_aux`]
- **Used by**: `interpolation_coeff_eq_function_coeff_aux`
- **Visibility**: private
- **Lines**: 144–149 (proof 2 lines)
- **Notes**: none

### `def interpolationRootProductAux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : Polynomial (ℍ → ℂ)`
- **What**: The function-valued product ∏_{σ'≠σ} (X − (τ ↦ j(σ'τ))) — the σ-th Lagrange basis numerator, isolated so its coefficients can be analyzed.
- **How**: Finite product of linear factors over `Finset.univ.erase σ`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix`, `CoxMatrix.act`, `j`]
- **Used by**: `interpolationFunction_coeff_aux`, `interpolationRootProduct_coeff_mdifferentiable_aux`, `interpolation_coeff_meromorphicOnH_aux`, `interpolationRootProduct_coeff_cuspMeromorphicAt_aux`, `interpolation_coeff_widthM_cuspMeromorphicAt_aux`
- **Visibility**: private
- **Lines**: 151–154 (definition 3 lines)
- **Notes**: none

### `theorem interpolationFunction_coeff_aux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (n : ℕ) : (interpolationFunctionAux m hf).coeff n = ∑ σ, rightCosetTranslate m hf (coxMatrixEquivRightCosets m σ) * (interpolationRootProductAux m σ).coeff n`
- **What**: The n-th coefficient function of the interpolation polynomial is the weighted sum of the n-th coefficients of the Lagrange basis products, with the coset translates of f as weights.
- **How**: Unfolds both definitions; `Polynomial.coeff` of a sum of `C * product` distributes (simp with `finset_sum_coeff`, `coeff_C_mul`).
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`interpolationFunctionAux`, `interpolationRootProductAux`, `rightCosetTranslate`, `coxMatrixEquivRightCosets`, `CoxMatrix`]
- **Used by**: `interpolation_coeff_meromorphicOnH_aux`, `interpolation_coeff_widthM_cuspMeromorphicAt_aux`
- **Visibility**: private
- **Lines**: 156–163 (proof 2 lines)
- **Notes**: none

### `theorem coxRoot_mdifferentiable_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : MDiff (fun τ : ℍ ↦ j (σ.act τ))`
- **What**: Each Cox root τ ↦ j(στ) is holomorphic (MDifferentiable) on the upper half-plane.
- **How**: Identifies the root with the coset evaluation via `rightCosetEval_equiv` and reads holomorphy from the subring element `UpperHalfPlaneFunctionField.rightCosetFunction`, whose membership proof carries MDifferentiability.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix`, `CoxMatrix.act`, `j`, `rightCosetEval_equiv`, `UpperHalfPlaneFunctionField.rightCosetFunction`, `coxMatrixEquivRightCosets`]
- **Used by**: `coxLinearFactor_coeff_mdifferentiable_aux`
- **Visibility**: private
- **Lines**: 165–169 (proof 3 lines)
- **Notes**: none

### `theorem coxLinearFactor_coeff_mdifferentiable_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) (n : ℕ) : MDiff ((Polynomial.X - Polynomial.C (fun τ : ℍ ↦ j (σ.act τ)) : Polynomial (ℍ → ℂ)).coeff n)`
- **What**: Every coefficient of a linear factor X − (j∘σ) (namely −j(στ), 1, or 0) is holomorphic on ℍ.
- **How**: Case split on n = 0, 1, ≥2: the constant term is holomorphic by `coxRoot_mdifferentiable_aux` and negation; the others are constants (`mdifferentiable_const`).
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix`, `CoxMatrix.act`, `j`, `coxRoot_mdifferentiable_aux`]
- **Used by**: `interpolationRootProduct_coeff_mdifferentiable_aux`
- **Visibility**: private
- **Lines**: 171–184 (proof ~12 lines)
- **Notes**: none

### `theorem polynomial_prod_coeff_mdifferentiable_aux`
- **Type**: `{ι : Type*} (P : ι → Polynomial (ℍ → ℂ)) : ∀ s : Finset ι, (∀ i ∈ s, ∀ n, MDiff ((P i).coeff n)) → ∀ n, MDiff ((s.prod P).coeff n)`
- **What**: If every coefficient of every polynomial in a finite family is holomorphic, then every coefficient of the product is holomorphic (holomorphy analogue of the cusp-meromorphy lemma from AnalyticSupport).
- **How**: Induction on the finset (`Finset.induction_on`); the insert step expands the product coefficient by `Polynomial.coeff_mul` into a finite antidiagonal sum of products, closed under `MDifferentiable.sum` and `MDifferentiable.mul`.
- **Hypotheses**: all coefficients of each factor indexed by s are MDifferentiable.
- **Uses from project**: []
- **Used by**: `interpolationRootProduct_coeff_mdifferentiable_aux`
- **Visibility**: private
- **Lines**: 186–207 (proof ~20 lines)
- **Notes**: parallel to project lemma `polynomial_prod_coeff_cuspMeromorphicAt` (AnalyticSupport.lean) — candidate for consolidation

### `theorem interpolationRootProduct_coeff_mdifferentiable_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) (n : ℕ) : MDiff ((interpolationRootProductAux m σ).coeff n)`
- **What**: Every coefficient of the Lagrange basis product ∏_{σ'≠σ}(X − j(σ'·)) is holomorphic on ℍ.
- **How**: Instantiates `polynomial_prod_coeff_mdifferentiable_aux` with the linear factors, whose coefficient holomorphy is `coxLinearFactor_coeff_mdifferentiable_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`interpolationRootProductAux`, `polynomial_prod_coeff_mdifferentiable_aux`, `coxLinearFactor_coeff_mdifferentiable_aux`, `CoxMatrix`, `j`]
- **Used by**: `interpolation_coeff_meromorphicOnH_aux`
- **Visibility**: private
- **Lines**: 209–218 (proof ~8 lines)
- **Notes**: none

### `theorem interpolation_coeff_eq_function_coeff_aux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (n : ℕ) : (fun τ ↦ (interpolationAt m hf τ).coeff n) = (interpolationFunctionAux m hf).coeff n`
- **What**: The τ-dependent coefficient of the pointwise interpolation polynomial, as a function, equals the coefficient of the function-valued polynomial.
- **How**: Function extensionality plus `interpolationFunction_coeff_apply_aux` pointwise.
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`interpolationAt`, `interpolationFunctionAux`, `interpolationFunction_coeff_apply_aux`]
- **Used by**: `interpolation_coeff_meromorphicOnH_aux`, `interpolation_coeff_widthM_cuspMeromorphicAt_aux`
- **Visibility**: private
- **Lines**: 220–225 (proof 2 lines)
- **Notes**: none

### `theorem interpolation_coeff_meromorphicOnH_aux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (n : ℕ) : ∀ z : ℂ, 0 < z.im → MeromorphicAt ((fun τ ↦ (interpolationAt m hf τ).coeff n) ∘ UpperHalfPlane.ofComplex) z`
- **What**: Each coefficient of the interpolation polynomial is meromorphic at every point of the upper half-plane — first of the three conditions for being a level-one modular function.
- **How**: Uses the decomposition `interpolationFunction_coeff_aux` into weight × basis-coefficient; the weights are meromorphic by `rightCosetTranslate_meromorphicOnH_aux`, the basis coefficients are holomorphic hence meromorphic (`interpolationRootProduct_coeff_mdifferentiable_aux` + `AnalyticAt.meromorphicAt`), and the finite sum is closed under `MeromorphicAt.fun_sum` and `MeromorphicAt.mul`.
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`interpolationAt`, `interpolation_coeff_eq_function_coeff_aux`, `interpolationFunction_coeff_aux`, `interpolationRootProductAux`, `rightCosetTranslate`, `rightCosetTranslate_meromorphicOnH_aux`, `coxMatrixEquivRightCosets`, `interpolationRootProduct_coeff_mdifferentiable_aux`, `CoxMatrix`]
- **Used by**: `interpolation_coeff_isLevelOne`
- **Visibility**: private
- **Lines**: 227–256 (proof ~27 lines)
- **Notes**: none

### `theorem rightCosetTranslate_cuspMeromorphicAt_aux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (c : Gamma0RightCosets m) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (rightCosetTranslate m hf c)) 0`
- **What**: The width-m cusp function of every coset translate f(γ·) is meromorphic at q = 0.
- **How**: `Quotient.inductionOn` reduces to a representative γ, where the statement is exactly the third defining condition `hf.2.2 γ` of `IsGamma0ModularFunction`.
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`IsGamma0ModularFunction`, `Gamma0RightCosets`, `rightCosetTranslate`]
- **Used by**: `interpolation_coeff_widthM_cuspMeromorphicAt_aux`
- **Visibility**: private
- **Lines**: 258–267 (proof ~5 lines)
- **Notes**: none

### `theorem interpolationRootProduct_coeff_cuspMeromorphicAt_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) (n : ℕ) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) ((interpolationRootProductAux m σ).coeff n)) 0`
- **What**: Every coefficient of the Lagrange basis product has a width-m cusp function meromorphic at q = 0.
- **How**: Instantiates the project lemma `polynomial_prod_coeff_cuspMeromorphicAt` (AnalyticSupport) with the linear factors, whose coefficient cusp-meromorphy is `coxLinearFactor_coeff_cuspMeromorphicAt`.
- **Hypotheses**: none.
- **Uses from project**: [`interpolationRootProductAux`, `polynomial_prod_coeff_cuspMeromorphicAt`, `coxLinearFactor_coeff_cuspMeromorphicAt`, `CoxMatrix`, `j`]
- **Used by**: `interpolation_coeff_widthM_cuspMeromorphicAt_aux`
- **Visibility**: private
- **Lines**: 269–280 (proof ~7 lines)
- **Notes**: none

### `theorem interpolation_coeff_widthM_cuspMeromorphicAt_aux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (n : ℕ) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (fun τ ↦ (interpolationAt m hf τ).coeff n)) 0`
- **What**: Each interpolation coefficient is meromorphic at the cusp with respect to the width-m local parameter q_m.
- **How**: Decomposes via `interpolationFunction_coeff_aux` and closes the finite sum of products under `meromorphicAt_cuspFunction_finset_sum` and `meromorphicAt_cuspFunction_mul`, feeding in `rightCosetTranslate_cuspMeromorphicAt_aux` and `interpolationRootProduct_coeff_cuspMeromorphicAt_aux`.
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`interpolationAt`, `interpolation_coeff_eq_function_coeff_aux`, `interpolationFunction_coeff_aux`, `meromorphicAt_cuspFunction_finset_sum`, `meromorphicAt_cuspFunction_mul`, `rightCosetTranslate_cuspMeromorphicAt_aux`, `interpolationRootProduct_coeff_cuspMeromorphicAt_aux`, `interpolationRootProductAux`, `rightCosetTranslate`, `coxMatrixEquivRightCosets`, `CoxMatrix`]
- **Used by**: `interpolation_coeff_widthOne_cuspMeromorphicAt_aux`
- **Visibility**: private
- **Lines**: 282–297 (proof ~13 lines)
- **Notes**: none

### `theorem interpolation_coeff_slashInvariant_aux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (n : ℕ) (δ : SL(2, ℤ)) : (fun τ ↦ (interpolationAt m hf τ).coeff n) ∣[(0 : ℤ)] δ = fun τ ↦ (interpolationAt m hf τ).coeff n`
- **What**: Each interpolation coefficient is invariant under the weight-0 slash action of all of SL(2,ℤ) — the modularity condition at level one.
- **How**: Weight-0 slash is just precomposition with δ (after `ModularForm.SL_slash_apply` and `zpow_zero`), so this is the coefficientwise consequence of `interpolationAt_smul_aux`.
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`interpolationAt`, `interpolationAt_smul_aux`]
- **Used by**: `interpolation_coeff_widthOne_cuspMeromorphicAt_aux`, `interpolation_coeff_isLevelOne`
- **Visibility**: private
- **Lines**: 299–307 (proof ~5 lines)
- **Notes**: none

### `theorem interpolation_coeff_widthOne_cuspMeromorphicAt_aux`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (n : ℕ) : MeromorphicAt (cuspFunction 1 (fun τ ↦ (interpolationAt m hf τ).coeff n)) 0`
- **What**: Width upgrade: since the coefficient is 1-periodic (being SL(2,ℤ)-invariant), its width-m cusp meromorphy implies width-1 cusp meromorphy.
- **How**: Applies the project rescaling lemma `meromorphicAt_cuspFunction_of_nat_mul` with the periodicity supplied by `periodic_comp_of_slashInvariant_one` applied to `interpolation_coeff_slashInvariant_aux`.
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`interpolationAt`, `meromorphicAt_cuspFunction_of_nat_mul`, `interpolation_coeff_widthM_cuspMeromorphicAt_aux`, `periodic_comp_of_slashInvariant_one`, `interpolation_coeff_slashInvariant_aux`]
- **Used by**: `interpolation_coeff_isLevelOne`
- **Visibility**: private
- **Lines**: 309–317 (proof ~5 lines)
- **Notes**: none

### `theorem interpolation_coeff_isLevelOne`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (n : ℕ) : IsLevelOneModularFunction (fun τ ↦ (interpolationAt m hf τ).coeff n)`
- **What**: Cox Exercise 11.11: every coefficient of the interpolation polynomial (11.16) is a level-one modular function of τ.
- **How**: Assembles the three defining conditions: meromorphy on ℍ (`interpolation_coeff_meromorphicOnH_aux`), SL(2,ℤ)-slash-invariance (`interpolation_coeff_slashInvariant_aux`), and cusp meromorphy of each translate — which by full modular invariance reduces to the width-1 statement `interpolation_coeff_widthOne_cuspMeromorphicAt_aux`.
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`IsLevelOneModularFunction`, `interpolationAt`, `interpolation_coeff_meromorphicOnH_aux`, `interpolation_coeff_slashInvariant_aux`, `interpolation_coeff_widthOne_cuspMeromorphicAt_aux`]
- **Used by**: `theorem_11_9_ii_pointwise`
- **Visibility**: public
- **Lines**: 319–336 (proof ~15 lines)
- **Notes**: has docstring

### `theorem eval_derivative_prod_X_sub_C_at`
- **Type**: `{R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] (r : ι → R) (i : ι) : (Polynomial.derivative (∏ k, (X - C (r k)))).eval (r i) = ∏ k ∈ univ.erase i, (r i - r k)`
- **What**: Purely algebraic Lagrange fact: the derivative of ∏(X − r_k) evaluated at the root r_i equals the product of the differences r_i − r_k over k ≠ i.
- **How**: Leibniz rule for finite products (`Polynomial.derivative_prod_finset`) gives a sum over k; every summand with k ≠ i vanishes at r_i because its erased product contains the factor (X − r_i) (killed by `Finset.prod_eq_zero`), isolated via `Finset.sum_eq_single`.
- **Hypotheses**: R a commutative ring, ι finite with decidable equality.
- **Uses from project**: []
- **Used by**: `recoveryFormula`
- **Visibility**: private
- **Lines**: 338–365 (proof ~25 lines)
- **Notes**: fully generic algebra — candidate for mathlib

### `theorem eval_interpolation_sum_at`
- **Type**: `{R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] (a r : ι → R) (i : ι) : (∑ k, C (a k) * ∏ l ∈ univ.erase k, (X - C (r l))).eval (r i) = a i * ∏ l ∈ univ.erase i, (r i - r l)`
- **What**: Purely algebraic: evaluating a Lagrange-type sum at the node r_i kills all terms except the i-th, leaving a_i times the separability product.
- **How**: `Finset.sum_eq_single` — each k ≠ i term evaluates to 0 since its product contains the factor (r_i − r_i) (via `Finset.prod_eq_zero`), and the surviving term evaluates by `Polynomial.eval_prod`.
- **Hypotheses**: R a commutative ring, ι finite with decidable equality.
- **Uses from project**: []
- **Used by**: `recoveryFormula`
- **Visibility**: private
- **Lines**: 367–393 (proof ~24 lines)
- **Notes**: fully generic algebra — candidate for mathlib

### `theorem recoveryFormula`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (τ : ℍ) (hderiv : ((modularPolynomialC m).specializeY (j τ)).derivative.eval (levelJ m τ) ≠ 0) : f τ = (interpolationAt m hf τ).eval (levelJ m τ) / ((modularPolynomialC m).specializeY (j τ)).derivative.eval (levelJ m τ)`
- **What**: Cox equation (11.17): at points where ∂_X Φ_m(j(mτ), j(τ)) ≠ 0, the modular function f is recovered from the interpolation polynomial evaluated at j(mτ) divided by that derivative. The nonvanishing guard is essential since specialized roots can collide at CM points.
- **How**: Both numerator and denominator localize at the distinguished root j(σ₀τ) = j(mτ) (`j_act_sigmaZero`): the denominator becomes ∏_{σ≠σ₀}(j(σ₀τ) − j(στ)) by `eval_derivative_prod_X_sub_C_at` applied through `modularPolynomialC_specializeY`/`coxPhiAtJ`, the numerator becomes f(τ)·(same product) by `eval_interpolation_sum_at` and `rightCosetTranslate_sigmaZero`, and the quotient cancels by `mul_div_cancel_right₀` using the guard.
- **Hypotheses**: f is a Γ₀(m)-modular function; the derivative of the specialized modular polynomial does not vanish at (j(τ), j(mτ)).
- **Uses from project**: [`IsGamma0ModularFunction`, `interpolationAt`, `modularPolynomialC`, `BivariatePolynomial.specializeY`, `levelJ`, `j`, `sigmaZero`, `j_act_sigmaZero`, `coxPhiAtJ`, `modularPolynomialC_specializeY`, `rightCosetTranslate_sigmaZero`, `rightCosetTranslate`, `coxMatrixEquivRightCosets`, `CoxMatrix`, `eval_derivative_prod_X_sub_C_at`, `eval_interpolation_sum_at`]
- **Used by**: `rationalInTwo_of_interpolation_coeff_rational`
- **Visibility**: public
- **Lines**: 395–433 (proof ~29 lines)
- **Notes**: has substantive docstring documenting the CM-collision guard

### `theorem interpolationAt_natDegree_lt`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (τ : ℍ) : (interpolationAt m hf τ).natDegree < Fintype.card (CoxMatrix m)`
- **What**: The interpolation polynomial has degree strictly less than the number of Cox matrices (each summand has degree |CoxMatrix m| − 1), so it is determined by its first |CoxMatrix m| coefficients.
- **How**: Bounds each summand by `Polynomial.natDegree_mul_le` and `Polynomial.natDegree_prod_le`, counts the erased product's linear factors (`Polynomial.natDegree_X_sub_C`, `Finset.card_erase_of_mem`), and closes the sum with `Polynomial.natDegree_sum_le_of_forall_le`; positivity of the card comes from the inhabitant `sigmaZero m`.
- **Hypotheses**: f is a Γ₀(m)-modular function.
- **Uses from project**: [`interpolationAt`, `CoxMatrix`, `sigmaZero`, `rightCosetTranslate`, `coxMatrixEquivRightCosets`, `j`]
- **Used by**: `rationalInTwo_of_interpolation_coeff_rational`
- **Visibility**: private
- **Lines**: 439–473 (proof ~32 lines)
- **Notes**: proof >30 lines; inside `section Theorem119`

### `theorem exists_commonDenominator_polynomialEval_of_natDegree_lt`
- **Type**: `{A : ℍ → Polynomial ℂ} {g h : ℍ → ℂ} (d : ℕ) (hdegree : ∀ τ, (A τ).natDegree < d) (hcoeff : ∀ n, RationalIn (fun τ ↦ (A τ).coeff n) g) : ∃ numerator : ℂ[X][Y], ∃ commonDenom : Polynomial ℂ, commonDenom ≠ 0 ∧ ∀ τ, commonDenom.eval (g τ) ≠ 0 → (A τ).eval (h τ) = numerator.evalEval (g τ) (h τ) / commonDenom.eval (g τ)`
- **What**: Common-denominator packaging: if a τ-family of polynomials of bounded degree d has each coefficient a rational function of g, then its evaluation at h(τ) is a single bivariate polynomial in (g, h) divided by one nonzero polynomial in g, wherever that denominator does not vanish.
- **How**: Chooses numerator/denominator pairs (p_n, q_n) per coefficient from `RationalIn`, sets the common denominator ∏_{n<d} q_n and numerator Σ_n C(p_n·∏_{k≠n} q_k)·X^n; the evaluation identity is checked termwise using `Polynomial.eval_eq_sum_range'` (justified by the degree bound), `Polynomial.evalEval_mul`/`evalEval_C`/`evalEval_pow`, `Finset.mul_prod_erase`, and a closing `field_simp`.
- **Hypotheses**: uniform degree bound deg A(τ) < d; each coefficient function is rational in g (project predicate `RationalIn`).
- **Uses from project**: [`RationalIn`]
- **Used by**: `rationalInTwo_of_interpolation_coeff_rational`
- **Visibility**: private
- **Lines**: 475–519 (proof ~36 lines)
- **Notes**: proof >30 lines

### `theorem modularPolynomialC_derivative_evalEval`
- **Type**: `(m : ℕ+) (τ : ℍ) : ((modularPolynomialC m).derivative).evalEval (j τ) (levelJ m τ) = ((modularPolynomialC m).specializeY (j τ)).derivative.eval (levelJ m τ)`
- **What**: Commutation of X-derivative with Y-specialization: differentiating the bivariate modular polynomial and then evaluating at (j(τ), j(mτ)) equals specializing Y = j(τ) first and differentiating in X.
- **How**: `Polynomial.derivative_map` (derivative commutes with coefficient maps) plus `Polynomial.map_evalRingHom_eval`, after unfolding `BivariatePolynomial.specializeY`.
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialC`, `BivariatePolynomial.specializeY`, `levelJ`, `j`]
- **Used by**: `interpolationDenominator_eval`
- **Visibility**: private
- **Lines**: 521–527 (proof 3 lines)
- **Notes**: none

### `def modularDerivativeHolomorphic`
- **Type**: `(m : ℕ+) : HolomorphicFunction`
- **What**: The derivative-denominator ∂_X Φ_m(j(mτ), j(τ)) packaged as an element of the subring of holomorphic functions on ℍ, expressed as ∏_{c ≠ base} (j(mτ·) − j_c(·)) over non-base right cosets.
- **How**: Finite product of differences of the subring elements `rightCosetFunction m (baseRightCoset m)` and `rightCosetFunction m c` in the ring `HolomorphicFunction`.
- **Hypotheses**: none.
- **Uses from project**: [`HolomorphicFunction`, `UpperHalfPlaneFunctionField.rightCosetFunction`, `baseRightCoset`]
- **Used by**: `modularDerivativeHolomorphic_apply`, `modularDerivativeHolomorphic_ne_zero`, `interpolationDenominator_onCurve_ne_zero`
- **Visibility**: private
- **Lines**: 528–531 (definition 3 lines)
- **Notes**: none

### `theorem modularDerivativeHolomorphic_apply`
- **Type**: `(m : ℕ+) (τ : ℍ) : (modularDerivativeHolomorphic m).1 τ = ((modularPolynomialC m).specializeY (j τ)).derivative.eval (levelJ m τ)`
- **What**: Pointwise identification: the holomorphic product element evaluates to the derivative of the specialized modular polynomial at j(mτ).
- **How**: Differentiates the coset-product factorization `modularPolynomialC_rightCosetProduct` with `Polynomial.derivative_mul` after peeling off the base-coset factor by `Finset.mul_prod_erase`; the surviving term at X = j(mτ) is exactly the erased product of root differences (the peeled factor vanishes at its own root).
- **Hypotheses**: none.
- **Uses from project**: [`modularDerivativeHolomorphic`, `modularPolynomialC`, `BivariatePolynomial.specializeY`, `levelJ`, `j`, `baseRightCoset`, `modularPolynomialC_rightCosetProduct`, `UpperHalfPlaneFunctionField.rightCosetFunction`, `rightCosetEval`]
- **Used by**: `interpolationDenominator_onCurve_ne_zero`
- **Visibility**: private
- **Lines**: 533–559 (proof ~24 lines)
- **Notes**: none

### `theorem modularDerivativeHolomorphic_ne_zero`
- **Type**: `(m : ℕ+) : modularDerivativeHolomorphic m ≠ 0`
- **What**: The derivative-denominator is nonzero as a holomorphic function on ℍ, i.e. Φ_m(X, j) is separable along the modular curve: the coset functions are pairwise distinct.
- **How**: A product in the integral domain `HolomorphicFunction` is nonzero when each factor is (`Finset.prod_ne_zero_iff`); each difference is nonzero by injectivity of the coset-function assignment, `rightCosetFunction_injective`.
- **Hypotheses**: none.
- **Uses from project**: [`modularDerivativeHolomorphic`, `UpperHalfPlaneFunctionField.rightCosetFunction`, `baseRightCoset`, `rightCosetFunction_injective`]
- **Used by**: `interpolationDenominator_onCurve_ne_zero`
- **Visibility**: private
- **Lines**: 561–570 (proof ~8 lines)
- **Notes**: none

### `def interpolationDenominator`
- **Type**: `(m : ℕ+) (D : Polynomial ℂ) : ℂ[X][Y]`
- **What**: The total denominator for the rational representation of f: the common denominator D (in the j-variable) times the X-derivative of the bivariate modular polynomial.
- **How**: Product `Polynomial.C D * (modularPolynomialC m).derivative` in ℂ[X][Y].
- **Hypotheses**: none.
- **Uses from project**: [`modularPolynomialC`]
- **Used by**: `interpolationDenominator_eval`, `interpolationDenominator_onCurve_ne_zero`, `rationalInTwo_of_interpolation_coeff_rational`
- **Visibility**: private
- **Lines**: 572–573 (1 line)
- **Notes**: none

### `theorem interpolationDenominator_eval`
- **Type**: `(m : ℕ+) (D : Polynomial ℂ) (τ : ℍ) : (interpolationDenominator m D).evalEval (j τ) (levelJ m τ) = D.eval (j τ) * ((modularPolynomialC m).specializeY (j τ)).derivative.eval (levelJ m τ)`
- **What**: The bivariate denominator evaluates on the modular curve point (j(τ), j(mτ)) to the product of D(j(τ)) with the specialized derivative.
- **How**: `Polynomial.evalEval_mul`/`evalEval_C` plus the derivative-specialization exchange `modularPolynomialC_derivative_evalEval`.
- **Hypotheses**: none.
- **Uses from project**: [`interpolationDenominator`, `modularPolynomialC_derivative_evalEval`, `modularPolynomialC`, `BivariatePolynomial.specializeY`, `levelJ`, `j`]
- **Used by**: `interpolationDenominator_onCurve_ne_zero`, `rationalInTwo_of_interpolation_coeff_rational`
- **Visibility**: private
- **Lines**: 575–582 (proof 2 lines)
- **Notes**: none

### `theorem interpolationDenominator_onCurve_ne_zero`
- **Type**: `(m : ℕ+) {D : Polynomial ℂ} (hD : D ≠ 0) : (fun τ : ℍ ↦ (interpolationDenominator m D).evalEval (j τ) (levelJ m τ)) ≠ 0`
- **What**: For nonzero D, the denominator does not vanish identically along the modular curve τ ↦ (j(τ), j(mτ)) — the nondegeneracy needed for `RationalInTwo`.
- **How**: In the integral domain `HolomorphicFunction`, the function equals `evalJ D * modularDerivativeHolomorphic m` (via `evalJ_apply` and `modularDerivativeHolomorphic_apply`); the first factor is nonzero by injectivity `evalJ_injective` (j is transcendental-like: polynomial evaluation at j is injective) and the second by `modularDerivativeHolomorphic_ne_zero`, so the product is nonzero by `mul_ne_zero`.
- **Hypotheses**: D is a nonzero polynomial.
- **Uses from project**: [`interpolationDenominator`, `interpolationDenominator_eval`, `evalJ`, `evalJ_injective`, `evalJ_apply`, `modularDerivativeHolomorphic`, `modularDerivativeHolomorphic_ne_zero`, `modularDerivativeHolomorphic_apply`, `levelJ`, `j`]
- **Used by**: `rationalInTwo_of_interpolation_coeff_rational`
- **Visibility**: private
- **Lines**: 584–603 (proof ~18 lines)
- **Notes**: none

### `theorem rationalInTwo_of_interpolation_coeff_rational`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (hcoeff : ∀ n, RationalIn (fun τ ↦ (interpolationAt m hf τ).coeff n) j) : RationalInTwo f j (levelJ m)`
- **What**: The synthesis step: if every interpolation coefficient is a rational function of j, then f itself is a rational function of the pair (j(τ), j(mτ)) with a denominator not identically zero on the curve.
- **How**: Packages the coefficients into one numerator/denominator pair by `exists_commonDenominator_polynomialEval_of_natDegree_lt` (degree bound from `interpolationAt_natDegree_lt`), takes `interpolationDenominator m D` as the global denominator (nonvanishing on the curve by `interpolationDenominator_onCurve_ne_zero`), and chains the recovery formula `recoveryFormula` with `div_div` at every point where the denominator is nonzero.
- **Hypotheses**: f is a Γ₀(m)-modular function; each coefficient of its interpolation polynomial is rational in j.
- **Uses from project**: [`IsGamma0ModularFunction`, `RationalIn`, `RationalInTwo`, `interpolationAt`, `j`, `levelJ`, `CoxMatrix`, `exists_commonDenominator_polynomialEval_of_natDegree_lt`, `interpolationAt_natDegree_lt`, `interpolationDenominator`, `interpolationDenominator_onCurve_ne_zero`, `interpolationDenominator_eval`, `recoveryFormula`, `modularPolynomialC`, `BivariatePolynomial.specializeY`]
- **Used by**: `theorem_11_9_ii_pointwise`
- **Visibility**: private
- **Lines**: 605–634 (proof ~25 lines)
- **Notes**: none

### `theorem theorem_11_9_ii_pointwise`
- **Type**: `(N : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction N f) : RationalInTwo f j (levelJ N)`
- **What**: Cox Theorem 11.9(ii) in pointwise form: every Γ₀(N)-modular function is a rational function of j(τ) and j(Nτ), with denominator nonzero as a function along the modular curve (though possibly vanishing at individual branch points).
- **How**: Each interpolation coefficient is a level-one modular function (`interpolation_coeff_isLevelOne`, Exercise 11.11), hence rational in j by the project's Theorem 11.9(i) (`theorem_11_9_i`); `rationalInTwo_of_interpolation_coeff_rational` concludes.
- **Hypotheses**: f is a Γ₀(N)-modular function.
- **Uses from project**: [`IsGamma0ModularFunction`, `RationalInTwo`, `j`, `levelJ`, `rationalInTwo_of_interpolation_coeff_rational`, `theorem_11_9_i`, `interpolation_coeff_isLevelOne`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 636–645 (proof 4 lines)
- **Notes**: has substantive docstring; capstone theorem of the file

### File Summary
- Total declarations: 37 (6 defs, 31 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): [`interpolationAt` (13), `interpolationRootProductAux` (5), `interpolationAtCosetsAux` (3), `interpolationFunctionAux` (3), `modularDerivativeHolomorphic` (3), `interpolationDenominator` (3)]
- Unused declarations (not used by anything in this file): [`theorem_11_9_ii_pointwise`] (the file's capstone; public API for downstream files)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [`exists_commonDenominator_polynomialEval_of_natDegree_lt` (~36), `interpolationAt_natDegree_lt` (~32)]
