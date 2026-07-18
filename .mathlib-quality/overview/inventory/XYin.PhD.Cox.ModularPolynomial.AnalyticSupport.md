# XYin/PhD/Cox/ModularPolynomial/AnalyticSupport.lean
Project-internal imports: `XYin.PhD.Cox.CoxMatrices.Basic`

All declarations live in `namespace Cox`.

### `theorem rightCosetEval_cuspMeromorphicAt`
- **Type**: `(m : ℕ+) (c : Gamma0RightCosets m) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (rightCosetEval m c)) 0`
- **What**: The function `τ ↦ j_m(γ•τ)` attached to a right coset `Γ₀(m)γ` of `Γ₀(m)` in `SL₂(ℤ)` has a meromorphic q-expansion at the cusp with respect to the width-`m` parameter `q = e^{2πiτ/m}`.
- **How**: Lifts the coset to a representative `γ` via `Quotient.inductionOn`, rewrites the coset evaluation as `levelJ m (γ • τ)`, and invokes the cusp-meromorphy component (`.2.2`) of `levelJ_isGamma0ModularFunction`, which asserts exactly this for every `γ`.
- **Hypotheses**: `m` a positive natural, `c` any right coset of `Γ₀(m)` in `SL₂(ℤ)`.
- **Uses from project**: [`Gamma0RightCosets`, `rightCosetEval`, `levelJ`, `levelJ_isGamma0ModularFunction`]
- **Used by**: `coxRoot_cuspMeromorphicAt`
- **Visibility**: public
- **Lines**: 22-30, proof 5 lines
- **Notes**: none

### `theorem coxRoot_cuspMeromorphicAt`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ))) 0`
- **What**: For each Cox matrix `σ = (a b; 0 d)` in `C(m)`, the root function `τ ↦ j(σ·τ) = j((aτ+b)/d)` of the modular polynomial has a meromorphic width-`m` cusp expansion.
- **How**: Rewrites `j(σ·τ)` as the evaluation of the right coset corresponding to `σ` under the bijection `C(m) ≃ Γ₀(m)\SL₂(ℤ)` (`rightCosetEval_equiv`), then applies `rightCosetEval_cuspMeromorphicAt`.
- **Hypotheses**: `σ` a primitive upper-triangular determinant-`m` matrix (a `CoxMatrix m`).
- **Uses from project**: [`CoxMatrix`, `CoxMatrix.act`, `j`, `rightCosetEval_equiv`, `coxMatrixEquivRightCosets`, `rightCosetEval_cuspMeromorphicAt`]
- **Used by**: `coxLinearFactor_coeff_cuspMeromorphicAt`
- **Visibility**: public
- **Lines**: 32-37, proof 2 lines
- **Notes**: none

### `theorem coxLinearFactor_coeff_cuspMeromorphicAt`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) (n : ℕ) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) ((Polynomial.X - Polynomial.C (fun τ : ℍ ↦ j (σ.act τ)) : Polynomial (ℍ → ℂ)).coeff n)) 0`
- **What**: Every coefficient of the linear factor `X − j(σ·τ)` (a polynomial over the ring of functions `ℍ → ℂ`) has a meromorphic width-`m` cusp expansion: the constant coefficient is `−j(σ·τ)`, the linear coefficient is `1`, and all higher coefficients vanish.
- **How**: Case split on `n`. For `n = 0` the coefficient is `−j(σ·τ)`; since `cuspFunction` of a product is not definitionally a product, the proof multiplies the constant `−1` by `coxRoot_cuspMeromorphicAt` and matches the two cusp functions on the punctured neighbourhood using `Periodic.cuspFunction_eq_of_nonzero` (mathlib) inside a `filter_upwards`/`MeromorphicAt.congr` argument. For `n = 1` and `n ≥ 2` the coefficient is the constant `1` resp. `0`, handled by `meromorphicAt_cuspFunction_const`.
- **Hypotheses**: `σ ∈ C(m)`, `n` any natural.
- **Uses from project**: [`CoxMatrix`, `CoxMatrix.act`, `j`, `coxRoot_cuspMeromorphicAt`, `meromorphicAt_cuspFunction_const`]
- **Used by**: unused in file (consumed by `coxPhiFunction_coeff_widthM_cuspMeromorphicAt` in Construction.lean)
- **Visibility**: public
- **Lines**: 39-66, proof 21 lines
- **Notes**: none

### `theorem polynomial_prod_coeff_cuspMeromorphicAt`
- **Type**: `{ι : Type*} (h : ℝ) (P : ι → Polynomial (ℍ → ℂ)) : ∀ s : Finset ι, (∀ i ∈ s, ∀ n, MeromorphicAt (cuspFunction h ((P i).coeff n)) 0) → ∀ n, MeromorphicAt (cuspFunction h ((s.prod P).coeff n)) 0`
- **What**: If every coefficient of each polynomial in a finite family of function-coefficient polynomials has a meromorphic cusp expansion of width `h`, then so does every coefficient of the product of the family.
- **How**: Induction on the finite set (`Finset.induction_on`). The empty product is `1`, whose coefficients are the constants `1` and `0` (`meromorphicAt_cuspFunction_const`). The insertion step expands `Polynomial.coeff_mul` as a convolution sum over antidiagonal pairs and closes with the project's sum and product stability lemmas `meromorphicAt_cuspFunction_finset_sum` and `meromorphicAt_cuspFunction_mul`.
- **Hypotheses**: Each coefficient of each `P i` for `i ∈ s` is cusp-meromorphic of width `h`.
- **Uses from project**: [`meromorphicAt_cuspFunction_const`, `meromorphicAt_cuspFunction_finset_sum`, `meromorphicAt_cuspFunction_mul`]
- **Used by**: unused in file (consumed by `coxPhiFunction_coeff_widthM_cuspMeromorphicAt` in Construction.lean)
- **Visibility**: public
- **Lines**: 68-90, proof 17 lines
- **Notes**: none

### `theorem periodic_comp_of_slashInvariant_one`
- **Type**: `{f : ℍ → ℂ} (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) : Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ)`
- **What**: A function on `ℍ` invariant under the weight-0 slash action of all of `SL₂(ℤ)` extends (via `ofComplex`) to a 1-periodic function on `ℂ`. This packages `τ ↦ τ+1` invariance for cusp-expansion arguments.
- **How**: Bundles `f` into a `SlashInvariantForm (Gamma 1) 0` (checking the slash condition by pulling each element of `Γ(1)` back to `SL₂(ℤ)` through `Subgroup.mem_map`), then applies mathlib's `SlashInvariantFormClass.periodic_comp_ofComplex`.
- **Hypotheses**: `f` is invariant under `∣[0] γ` for every `γ ∈ SL₂(ℤ)`.
- **Uses from project**: []
- **Used by**: unused in file (consumed by `coxPhiFunction_coeff_widthOne_cuspMeromorphicAt` in Construction.lean)
- **Visibility**: public
- **Lines**: 92-104, proof 12 lines
- **Notes**: none

### File Summary
- Total declarations: 5 (0 defs, 5 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): none within this file (all five are support lemmas; three are exported for Construction.lean)
- Unused declarations (not used by anything in this file): [`coxLinearFactor_coeff_cuspMeromorphicAt`, `polynomial_prod_coeff_cuspMeromorphicAt`, `periodic_comp_of_slashInvariant_one`] — all three are used by Construction.lean
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: []
