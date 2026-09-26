# Inventory: XYin/PhD/Cox/ModularPolynomial/AnalyticSupport.lean  (96 lines)

Shared analytic lemmas for the modular-polynomial files: width-`m` cusp meromorphy of the Cox roots `τ ↦ j(σ·τ)`, of the coefficients of the linear factors `X - C(j∘σ)`, of coefficients of finite products of function-valued polynomials, and the period-one extension of an `SL₂(ℤ)`-invariant function. Imported by `Construction.lean` (hence reachable from the umbrella `ModularPolynomial.lean` even though the umbrella does not import it directly).

## Declarations

### `theorem Cox.rightCosetEval_cuspMeromorphicAt`
- **Type**: `(m : ℕ+) (c : Gamma0RightCosets m) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (rightCosetEval m c)) 0`
- **What**: The function `τ ↦ j_m(γ·τ)` attached to a right coset `Γ₀(m)γ` has a meromorphic expansion in the width-`m` cusp parameter `q^{1/m}`.
- **How**: `Quotient.inductionOn` on the coset, then the third component of `levelJ_cuspData m` (cusp data of `j(mτ)`), which is exactly this statement for a representative `γ`.
- **Hypotheses**: none beyond `m ≥ 1`.
- **Uses from project**: `Gamma0RightCosets`, `rightCosetEval`, `levelJ`, `levelJ_cuspData` (mathlib: `UpperHalfPlane.cuspFunction`).
- **Used by**: `coxRoot_cuspMeromorphicAt`
- **Visibility**: public
- **Lines**: 22–30, proof body ≈ 5 lines
- **Notes**: Specialization of `Interpolation.rightCosetTranslate_cuspMeromorphicAt_aux` (Interpolation.lean:211–220) to `hf := levelJ_cuspData m`, since `rightCosetEval m c = rightCosetTranslate m (levelJ_cuspData m) c` by definition (CoxMatrices/Basic.lean:632). Identical proof skeleton.

### `theorem Cox.coxRoot_cuspMeromorphicAt`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) (fun τ : ℍ ↦ j (σ.act τ))) 0`
- **What**: Each Cox root `j(σ·τ)`, `σ ∈ C(m)`, is meromorphic in `q^{1/m}` at the cusp.
- **How**: Rewrite `j(σ·τ)` as `rightCosetEval m (coxMatrixEquivRightCosets m σ) τ` via `rightCosetEval_equiv`, then apply `rightCosetEval_cuspMeromorphicAt`.
- **Hypotheses**: none.
- **Uses from project**: `CoxMatrix`, `CoxMatrix.act`, `j`, `rightCosetEval_equiv`, `coxMatrixEquivRightCosets`, `rightCosetEval_cuspMeromorphicAt`
- **Used by**: `coxLinearFactor_coeff_cuspMeromorphicAt`
- **Visibility**: public
- **Lines**: 32–37, proof body ≈ 2 lines
- **Notes**: Also used externally by IntegralDescent.lean:183,190.

### `theorem Cox.coxLinearFactor_coeff_cuspMeromorphicAt`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) (n : ℕ) : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) ((Polynomial.X - Polynomial.C (fun τ : ℍ ↦ j (σ.act τ)) : Polynomial (ℍ → ℂ)).coeff n)) 0`
- **What**: Every coefficient of the function-valued linear factor `X - j(σ·τ)` (namely `-j∘σ`, `1`, or `0`) is width-`m` cusp-meromorphic.
- **How**: Three-way case split on `n`: `n = 0` gives `-j∘σ` handled by `meromorphicAt_cuspFunction_mul` with the constant `-1` and `coxRoot_cuspMeromorphicAt`; `n = 1` and `n ≥ 2` are constants (`meromorphicAt_cuspFunction_const`) after `Polynomial.coeff_sub/coeff_X/coeff_C_succ`.
- **Hypotheses**: none.
- **Uses from project**: `CoxMatrix`, `CoxMatrix.act`, `j`, `meromorphicAt_cuspFunction_mul`, `meromorphicAt_cuspFunction_const`, `coxRoot_cuspMeromorphicAt`
- **Used by**: unused in file (used by Construction.lean:247 and Interpolation.lean:233)
- **Visibility**: public
- **Lines**: 39–58, proof body ≈ 13 lines
- **Notes**: Verbatim twin of `Interpolation.coxLinearFactor_coeff_mdifferentiable_aux` (Interpolation.lean:141–154) with `MDiff` in place of cusp meromorphy. A `meromorphicAt_cuspFunction_neg` lemma is missing from LaurentQExpansion.lean (the `mul (const (-1))` trick recurs at IntegralDescent.lean:180–183).

### `theorem Cox.polynomial_prod_coeff_cuspMeromorphicAt`
- **Type**: `{ι : Type*} (h : ℝ) (P : ι → Polynomial (ℍ → ℂ)) : ∀ s : Finset ι, (∀ i ∈ s, ∀ n, MeromorphicAt (cuspFunction h ((P i).coeff n)) 0) → ∀ n, MeromorphicAt (cuspFunction h ((s.prod P).coeff n)) 0`
- **What**: If every coefficient of each polynomial in a finite family is cusp-meromorphic (width `h`), so is every coefficient of their product.
- **How**: `Finset.induction_on`; the inductive step writes the coefficient of a product as the antidiagonal sum `Polynomial.coeff_mul` and closes with `meromorphicAt_cuspFunction_finset_sum` and `meromorphicAt_cuspFunction_mul`.
- **Hypotheses**: arbitrary real width `h` (no positivity needed); coefficientwise cusp meromorphy of each factor.
- **Uses from project**: `meromorphicAt_cuspFunction_const`, `meromorphicAt_cuspFunction_finset_sum`, `meromorphicAt_cuspFunction_mul`
- **Used by**: unused in file (used by Construction.lean:244 and Interpolation.lean:229)
- **Visibility**: public
- **Lines**: 60–80, proof body ≈ 15 lines
- **Notes**: `classical` at top. Verbatim twin of `Interpolation.polynomial_prod_coeff_mdifferentiable_aux` (Interpolation.lean:156–173). Both are instances of "coefficients in a subring are preserved by products", i.e. `Subsemiring.prod_mem` in `Polynomial.lifts S.subtype` (see Observations).

### `theorem Cox.periodic_comp_of_slashInvariant_one`
- **Type**: `{f : ℍ → ℂ} (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) : Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ)`
- **What**: A weight-0 `SL₂(ℤ)`-invariant function, extended to `ℂ` through `ofComplex`, is 1-periodic.
- **How**: Package `f` as a `SlashInvariantForm (Gamma 1) 0` (membership in `Gamma 1` is unpacked with `Subgroup.mem_map`) and apply mathlib's `SlashInvariantFormClass.periodic_comp_ofComplex` with `1 ∈ strictPeriods`.
- **Hypotheses**: weight-zero slash invariance under all of `SL₂(ℤ)`.
- **Uses from project**: `[]`
- **Used by**: unused in file (used by Construction.lean:256,276; Interpolation.lean:269; IntegralDescent.lean:242)
- **Visibility**: public
- **Lines**: 82–94, proof body ≈ 9 lines
- **Notes**: Thin adapter around mathlib `SlashInvariantFormClass.periodic_comp_ofComplex` (Mathlib/NumberTheory/ModularForms/QExpansion.lean:120); only needed because callers work with bare functions rather than `SlashInvariantForm`s.

## File Summary
- Total declarations: 5 (0 defs, 5 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): none within the file (all consumers are downstream files)
- Unused declarations (not used by anything in this file): `coxLinearFactor_coeff_cuspMeromorphicAt`, `polynomial_prod_coeff_cuspMeromorphicAt`, `periodic_comp_of_slashInvariant_one` (all used downstream)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `periodic_comp_of_slashInvariant_one` (L83–94) is mathlib `SlashInvariantFormClass.periodic_comp_ofComplex` (`.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean:120`) plus a 5-line `SlashInvariantForm` packaging. Keep as adapter, or generalize to `(Γ) (hΓ : h ∈ Γ.strictPeriods)` so the width-`m` variants stop re-deriving periodicity.
- `polynomial_prod_coeff_cuspMeromorphicAt` (L61–80): mathlib has the general mechanism `Polynomial.lifts f : Subsemiring S[X]` with `Polynomial.lifts_iff_coeff_lifts` (`Mathlib/Algebra/Polynomial/Lifts.lean:72`) and `Subsemiring.prod_mem`. If the project defines `cuspMeromorphicSubring h : Subring (ℍ → ℂ)` (closure lemmas already exist: LaurentQExpansion.lean:99–132 `meromorphicAt_cuspFunction_add/_mul/_const/_finset_sum/_finset_prod`), then this lemma is `Subring.prod_mem (Polynomial.liftsRing S.subtype) …` composed with `lifts_iff_coeff_lifts`; the same replaces `Interpolation.polynomial_prod_coeff_mdifferentiable_aux` using the existing `holomorphicFunctions : Subring (ℍ → ℂ)` (ModularFunctions/FieldAction.lean:26). `coxLinearFactor_coeff_cuspMeromorphicAt` (L40–58) then becomes `X_mem_lifts`/`C_mem_lifts` (Lifts.lean:103,92) + `Subring.sub_mem`.
- `cuspFunction` here is mathlib `UpperHalfPlane.cuspFunction` (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:76`); `meromorphicAt_cuspFunction_*` are project lemmas (LaurentQExpansion.lean). No mathlib analogue found for the closure lemmas themselves (searched: `meromorphicAt_cuspFunction`, `cuspFunction_mul`, `cuspFunction_add`).
### Missing API / repeated patterns
- The `meromorphicAt_cuspFunction_mul (meromorphicAt_cuspFunction_const h (-1)) hf` idiom for negation appears at L48–50 and IntegralDescent.lean:180–183; add `meromorphicAt_cuspFunction_neg` (and `_sub`, `_pow`) to LaurentQExpansion.lean.
- The three-way `cases n` skeleton for coefficients of `X - C a` (L46–58; Interpolation.lean:145–154) would collapse to a single `Polynomial.coeff_X_sub_C : (X - C a).coeff n = if n = 1 then 1 else if n = 0 then -a else 0`-style lemma, or disappear entirely with the `lifts` approach above.
### Junk candidates
- none (every declaration is consumed downstream; no `#check`/`example`/commented code).
### Moral duplicates within this batch
- `rightCosetEval_cuspMeromorphicAt` (L23–30) ≡ `Interpolation.rightCosetTranslate_cuspMeromorphicAt_aux` (Interpolation.lean:211–220) at `hf := levelJ_cuspData m`.
- `coxLinearFactor_coeff_cuspMeromorphicAt` (L40–58) ≡ `Interpolation.coxLinearFactor_coeff_mdifferentiable_aux` (Interpolation.lean:141–154), predicate swapped.
- `polynomial_prod_coeff_cuspMeromorphicAt` (L61–80) ≡ `Interpolation.polynomial_prod_coeff_mdifferentiable_aux` (Interpolation.lean:156–173), predicate swapped.
### Generalization notes
- `polynomial_prod_coeff_cuspMeromorphicAt` uses nothing about `ℍ → ℂ` beyond the three closure lemmas; it is an instance of the subring/`lifts` statement over any commutative semiring.
- `periodic_comp_of_slashInvariant_one` only uses invariance under `Gamma 1`; the same proof gives `Periodic (f ∘ ofComplex) h` for any `Γ` and `h ∈ Γ.strictPeriods`.
