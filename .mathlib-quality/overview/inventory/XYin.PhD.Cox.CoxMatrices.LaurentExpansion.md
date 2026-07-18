# Source: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/CoxMatrices/LaurentExpansion.lean — project imports: `XYin.PhD.Cox.CoxMatrices.Basic`

All declarations are in namespace `Cox`. Note: many project declarations used here (`j`, `qj`, `laurentqExpansion`, `poleOrder`, `poleRemoved`, `to_qExpansion`, …) come transitively through `XYin.PhD.Cox.CoxMatrices.Basic` from `XYin/PhD/jFunction/jfunction.lean` and `XYin/PhD/LaurentQExpansion/LaurentQExpansion.lean`. Mathlib supplies `UpperHalfPlane.cuspFunction`, `qExpansion`, `eq_cuspFunction`, `qExpansion_coeff_unique` (Mathlib.NumberTheory.ModularForms.QExpansion) and `PowerSeries.rescale`/`expand`.

### `def zeta`
- **Type**: `(m : ℕ+) : ℂ`
- **What**: The primitive `m`-th root of unity `ζ_m = e^{2πi/m}` used throughout equation (11.13) of Cox.
- **How**: Defined as `Complex.exp (2πi / m)`.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `zeta_isPrimitiveRoot`, `coxPhaseAux`, `qParam_coxAction_aux`, `coxPhase_zpow_aux`, `laurentqExpansion_coxAction_coeff_aux`, `laurentqExpansion_coxAction`
- **Visibility**: public
- **Lines**: 23–24, 2 lines
- **Notes**: docstring present

### `theorem zeta_isPrimitiveRoot`
- **Type**: `(m : ℕ+) : IsPrimitiveRoot (zeta m) (m : ℕ)`
- **What**: `ζ_m` is a primitive `m`-th root of unity.
- **How**: Direct from mathlib's `Complex.isPrimitiveRoot_exp` (with `m ≠ 0` from `PNat.ne_zero`).
- **Hypotheses**: none
- **Uses from project**: [`zeta`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 26–28, proof 2 lines
- **Notes**: none

### `def jIntCoeff`
- **Type**: `(n : ℤ) : ℤ`
- **What**: The integer `n`-th Laurent coefficient `c(n)` of the analytic `j`-function's `q`-expansion (so `j = q⁻¹ + 744 + 196884q + …` with all `c(n) ∈ ℤ`).
- **How**: Extracted by `Classical.choose` from the project's integrality theorem `j_laurentQExpansion_isIntegral` (each Laurent coefficient of `j` is the cast of an integer).
- **Hypotheses**: none
- **Uses from project**: [`j_laurentQExpansion_isIntegral`]
- **Used by**: `jIntCoeff_spec`, `jIntCoeff_neg_one`, `transformedJSeries`, `transformedJSeries_coeff`, `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: public
- **Lines**: 30–32, 3 lines
- **Notes**: docstring present; noncomputable (choice)

### `theorem jIntCoeff_spec`
- **Type**: `(n : ℤ) : (laurentqExpansion 1 j).coeff n = (jIntCoeff n : ℂ)`
- **What**: The defining property: the `n`-th Laurent coefficient of `j` (width 1) equals the cast of `jIntCoeff n`.
- **How**: `choose_spec` of the same existence theorem.
- **Hypotheses**: none
- **Uses from project**: [`jIntCoeff`, `j_laurentQExpansion_isIntegral`, `laurentqExpansion`, `j`]
- **Used by**: `jIntCoeff_neg_one`, `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: public
- **Lines**: 34–36, proof 1 line
- **Notes**: none

### `theorem jIntCoeff_neg_one`
- **Type**: `jIntCoeff (-1) = 1`
- **What**: The leading coefficient of `j` is 1: the `q⁻¹`-coefficient of the `j`-expansion equals 1 (simple pole with residue-normalisation 1).
- **How**: The coefficient at `-poleOrder = -1` equals the constant term of the pole-removed expansion (`laurentqExpansion.coeff_neg_poleOrder` with `j_poleOrder = 1`), which via `j_to_qExpansion` is the constant term of the `qj`-expansion, computed as 1 by `qj_qExpansion_coeff_zero`; conclude by injectivity of `ℤ → ℂ`.
- **Hypotheses**: none
- **Uses from project**: [`jIntCoeff`, `jIntCoeff_spec`, `laurentqExpansion`, `j`, `j_poleOrder`, `laurentqExpansion.coeff_neg_poleOrder`, `to_qExpansion`, `j_to_qExpansion`, `qj`, `qj_qExpansion_coeff_zero`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 38–47, proof 9 lines
- **Notes**: none

### `def transformedJSeries`
- **Type**: `{K : Type*} [Field K] {m : ℕ+} (ζ : K) (σ : CoxMatrix m) : LaurentSeries K`
- **What**: Equation (11.13) as a formal Laurent series in `t = q^{1/m}`: the series `∑_n c(n) ζ^{abn} t^{a²n}` (starting at `n = -1`), i.e. coefficient of `t^k` is `c(k/a²)·ζ^{ab·(k/a²)}` when `a² ∣ k` and `k ≥ -a²`, else 0. This is `j((aτ+b)/d)` written formally over an abstract field `K`.
- **How**: HahnSeries constructor: the coefficient function together with a proof that the support is partially well-ordered, obtained from below-boundedness at `-a²` (`BddBelow.isWF` then `Set.IsWF.isPWO`).
- **Hypotheses**: `K` a field, `ζ : K` arbitrary (intended: primitive `m`-th root).
- **Uses from project**: [`jIntCoeff`, `CoxMatrix` (fields `a`, `b`)]
- **Used by**: `transformedJSeries_coeff`, `laurentqExpansion_coxAction_coeff_aux`, `laurentqExpansion_coxAction`
- **Visibility**: public
- **Lines**: 49–64, 16 lines
- **Notes**: docstring present; noncomputable

### `theorem transformedJSeries_coeff`
- **Type**: `{K} [Field K] {m : ℕ+} (ζ : K) (σ : CoxMatrix m) (k : ℤ) : (transformedJSeries ζ σ).coeff k = if (σ.a:ℤ)^2 ∣ k ∧ -((σ.a:ℤ)^2) ≤ k then (jIntCoeff (k/(σ.a:ℤ)^2) : K) * ζ^((σ.a:ℤ)*(σ.b:ℤ)*(k/(σ.a:ℤ)^2)) else 0`
- **What**: Unfolding lemma giving the explicit coefficient formula of `transformedJSeries`.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: [`transformedJSeries`, `jIntCoeff`, `CoxMatrix`]
- **Used by**: `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: public
- **Lines**: 66–72, proof 1 line
- **Notes**: none

### `def coxPhaseAux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : ℂ`
- **What**: The phase `η = ζ_m^{ab}` attached to a Cox matrix `σ = (a, b; 0, d)` — the root-of-unity factor arising when transporting `q` through `τ ↦ (aτ+b)/d`.
- **How**: `zeta m ^ (σ.a * σ.b)`.
- **Hypotheses**: none
- **Uses from project**: [`zeta`, `CoxMatrix`]
- **Used by**: `qParam_coxAction_aux`, `cuspFunction_coxCompose_aux`, `cuspFunction_coxAction_aux`, `coxPhase_ne_zero_aux`, `cuspFunction_coxAction_eventuallyEq_aux`, `cuspFunction_coxAction_meromorphicAt_aux`, `poleOrder_coxAction_aux`, `poleRemoved_coxAction_aux`, `to_qExpansion_coxAction_aux`, `coxPhase_zpow_aux`, `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: private
- **Lines**: 74–75, 2 lines
- **Notes**: none

### `theorem qParam_coxAction_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) (τ : ℍ) : Periodic.qParam 1 (σ.act τ) = coxPhaseAux m σ * Periodic.qParam ((m:ℕ):ℝ) τ ^ (σ.a ^ 2)`
- **What**: The `q`-parameter transformation law: with `q_m = e^{2πiτ/m}` and `στ = (aτ+b)/d`, one has `e^{2πi·στ} = ζ_m^{ab} · q_m^{a²}` — the analytic core of (11.13).
- **How**: Unfolds both `qParam`s to exponentials, combines with `Complex.exp_nat_mul`/`exp_add`, and reduces the exponent identity to `a/d = a²/m` using `m = a·d` (`σ.determinant`) with a `field_simp`/`ring` computation (denominators cleared by `a, d ≠ 0`).
- **Hypotheses**: none beyond the `CoxMatrix` structure.
- **Uses from project**: [`coxPhaseAux`, `zeta`, `CoxMatrix.coe_act`, `CoxMatrix` (fields `determinant`, `a_pos`, `d_pos`, `act`)]
- **Used by**: `cuspFunction_coxCompose_aux`, `poleRemoved_coxAction_aux`, `to_qExpansion_coxAction_aux`
- **Visibility**: private
- **Lines**: 77–91, proof 14 lines
- **Notes**: none

### `theorem periodic_comp_ofComplex_of_vadd_aux`
- **Type**: `{g : ℍ → ℂ} {h : ℝ} (hg : ∀ τ, g (h +ᵥ τ) = g τ) : Periodic (g ∘ UpperHalfPlane.ofComplex) (h : ℂ)`
- **What**: A function on ℍ invariant under real translation by `h` induces an `h`-periodic function on ℂ via the junk-valued extension `ofComplex`.
- **How**: Case split on `im z > 0`: in the upper half-plane use `UpperHalfPlane.ofComplex_apply_of_im_pos` and the hypothesis (noting `im (z + h) = im z`); on the closed lower half-plane both sides are the same junk value by `ofComplex_apply_of_im_nonpos`.
- **Hypotheses**: `g` is invariant under `τ ↦ h +ᵥ τ` on ℍ.
- **Uses from project**: []
- **Used by**: `j_periodic_aux`
- **Visibility**: private
- **Lines**: 93–107, proof 13 lines
- **Notes**: none

### `theorem j_periodic_aux`
- **Type**: `Periodic (j ∘ UpperHalfPlane.ofComplex) 1`
- **What**: The `j`-function, extended to ℂ by `ofComplex`, is 1-periodic.
- **How**: `j` is invariant under the modular translation `T` (`j_modularGroup_smul` combined with `UpperHalfPlane.modular_T_smul`), then apply `periodic_comp_ofComplex_of_vadd_aux`.
- **Hypotheses**: none
- **Uses from project**: [`j`, `j_modularGroup_smul`, `periodic_comp_ofComplex_of_vadd_aux`]
- **Used by**: `cuspFunction_coxAction_aux`
- **Visibility**: private
- **Lines**: 109–113, proof 4 lines
- **Notes**: none

### `theorem cuspFunction_coxCompose_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) (f : ℍ → ℂ) (hfper : Periodic (f ∘ ofComplex) 1) {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) : cuspFunction ((m:ℕ):ℝ) (fun τ ↦ f (σ.act τ)) q = cuspFunction 1 f (coxPhaseAux m σ * q ^ (σ.a ^ 2))`
- **What**: For any 1-periodic `f`, the width-`m` cusp function of `f ∘ σ` at `q` equals the width-1 cusp function of `f` evaluated at the transformed parameter `η q^{a²}`, for `0 < |q| < 1`.
- **How**: Choose `τ ∈ ℍ` with `q_m(τ) = q` via `Periodic.invQParam` (existence of positive imaginary part by `Periodic.im_invQParam_pos_of_norm_lt_one`); the left side is `f(στ)` by `Periodic.cuspFunction_eq_of_nonzero`, the right side is `f(στ)` by `UpperHalfPlane.eq_cuspFunction` after rewriting the parameter via `qParam_coxAction_aux` and `Periodic.qParam_right_inv`.
- **Hypotheses**: `f ∘ ofComplex` is 1-periodic; `q ≠ 0`, `‖q‖ < 1`.
- **Uses from project**: [`coxPhaseAux`, `qParam_coxAction_aux`, `CoxMatrix.act`]
- **Used by**: `cuspFunction_coxAction_aux`
- **Visibility**: private
- **Lines**: 115–135, proof 17 lines
- **Notes**: none

### `theorem cuspFunction_coxAction_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) {q : ℂ} (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) : cuspFunction ((m:ℕ):ℝ) (fun τ ↦ j (σ.act τ)) q = cuspFunction 1 j (coxPhaseAux m σ * q ^ (σ.a ^ 2))`
- **What**: Specialisation of the previous transfer identity to `f = j`.
- **How**: Immediate from `cuspFunction_coxCompose_aux` with periodicity witness `j_periodic_aux`.
- **Hypotheses**: `q ≠ 0`, `‖q‖ < 1`.
- **Uses from project**: [`cuspFunction_coxCompose_aux`, `j_periodic_aux`, `j`, `coxPhaseAux`, `CoxMatrix.act`]
- **Used by**: `cuspFunction_coxAction_eventuallyEq_aux`
- **Visibility**: private
- **Lines**: 137–141, term proof
- **Notes**: none

### `theorem coxPhase_ne_zero_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : coxPhaseAux m σ ≠ 0`
- **What**: The phase `η = ζ_m^{ab}` is nonzero (it is a power of an exponential).
- **How**: `pow_ne_zero` with `Complex.exp_ne_zero`.
- **Hypotheses**: none
- **Uses from project**: [`coxPhaseAux`]
- **Used by**: `poleOrder_coxAction_aux`, `poleRemoved_coxAction_aux`, `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: private
- **Lines**: 143–145, proof 1 line
- **Notes**: none

### `theorem cuspFunction_coxAction_eventuallyEq_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : cuspFunction ((m:ℕ):ℝ) (fun τ ↦ j (σ.act τ)) =ᶠ[nhdsWithin 0 {0}ᶜ] cuspFunction 1 j ∘ fun q ↦ coxPhaseAux m σ * q ^ (σ.a ^ 2)`
- **What**: The pointwise transfer identity upgraded to a germ statement: the two cusp functions agree on a punctured neighbourhood of 0.
- **How**: The unit ball is a punctured neighbourhood of 0 (`Metric.ball_mem_nhds` through `nhdsWithin_le_nhds`); `filter_upwards` then reduces to `cuspFunction_coxAction_aux` on `0 < |q| < 1`.
- **Hypotheses**: none
- **Uses from project**: [`cuspFunction_coxAction_aux`, `coxPhaseAux`, `j`, `CoxMatrix.act`]
- **Used by**: `cuspFunction_coxAction_meromorphicAt_aux`, `poleOrder_coxAction_aux`
- **Visibility**: private
- **Lines**: 147–154, proof 6 lines
- **Notes**: none

### `theorem cuspFunction_coxAction_meromorphicAt_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : MeromorphicAt (cuspFunction ((m:ℕ):ℝ) (fun τ ↦ j (σ.act τ))) 0`
- **What**: The width-`m` cusp function of `j ∘ σ` is meromorphic at `q = 0` (needed to apply the Laurent expansion machinery).
- **How**: It agrees near 0 with `(cuspFunction 1 j) ∘ φ` where `φ(q) = η q^{a²}` is analytic with `φ(0) = 0`; the composite is meromorphic by `MeromorphicAt.comp_analyticAt` applied to the project's `j_cuspFunction_meromorphicAt`, and meromorphy transfers along the germ equality by `MeromorphicAt.congr`.
- **Hypotheses**: none
- **Uses from project**: [`coxPhaseAux`, `j_cuspFunction_meromorphicAt`, `cuspFunction_coxAction_eventuallyEq_aux`, `j`, `CoxMatrix.act`, `CoxMatrix` (field `a_pos`)]
- **Used by**: `to_qExpansion_coxAction_aux`
- **Visibility**: private
- **Lines**: 156–166, proof 9 lines
- **Notes**: none

### `theorem poleOrder_coxAction_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : poleOrder ((m:ℕ):ℝ) (fun τ ↦ j (σ.act τ)) = σ.a ^ 2`
- **What**: The pole order of `j ∘ σ` in the local parameter `q^{1/m}` is `a²`: since `j` has a simple pole in `q` and the substitution `q ↦ η q^{a²}` has vanishing order `a²`, the composite has a pole of order `a²`.
- **How**: Computes the meromorphic order of the composite as (order of base) × (analytic vanishing order of `φ`): the base order is `−1` by `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero` with `j_poleOrder = 1`; `analyticOrderAt φ 0 = a²` via `analyticOrderAt_mul`, `analyticOrderAt_pow`, `analyticOrderAt_id` and nonvanishing of the constant `η`; composition by mathlib's `MeromorphicAt.meromorphicOrderAt_comp` (with non-eventual-constancy of `φ` from `eventuallyConst_iff_analyticOrderAt_sub_eq_top`); transfer to the actual cusp function by `meromorphicOrderAt_congr`, then unfold `UpperHalfPlane.poleOrder` and take `untopD` of `−a² < 0`.
- **Hypotheses**: none
- **Uses from project**: [`coxPhaseAux`, `coxPhase_ne_zero_aux`, `j_poleOrder`, `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder_of_ne_zero`, `j_cuspFunction_meromorphicAt`, `cuspFunction_coxAction_eventuallyEq_aux`, `poleOrder` (`UpperHalfPlane.poleOrder`), `j`, `CoxMatrix.act`, `CoxMatrix` (field `a_pos`)]
- **Used by**: `poleRemoved_coxAction_aux`, `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: private
- **Lines**: 168–223, proof 54 lines
- **Notes**: proof >30 lines (54)

### `theorem poleRemoved_coxAction_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : poleRemoved ((m:ℕ):ℝ) (fun τ ↦ j (σ.act τ)) = fun τ ↦ (coxPhaseAux m σ)⁻¹ * qj (σ.act τ)`
- **What**: The pole-removed function of `j ∘ σ` (i.e. `q_m^{a²}·j(στ)`) equals `η⁻¹·qj(στ)` where `qj = q·j` is the project's regularised `j`.
- **How**: Unfolds `poleRemoved` with the pole order `a²` from `poleOrder_coxAction_aux`, writes `qj(στ) = q_1(στ)·j(στ)`, and substitutes the transformation law `q_1(στ) = η·q_m(τ)^{a²}` (`qParam_coxAction_aux`); the `η` factors cancel by `field_simp` with `η ≠ 0`.
- **Hypotheses**: none
- **Uses from project**: [`poleRemoved` (`UpperHalfPlane.poleRemoved`), `poleOrder_coxAction_aux`, `qj`, `j`, `qParam_coxAction_aux`, `coxPhase_ne_zero_aux`, `coxPhaseAux`, `CoxMatrix.act`]
- **Used by**: `to_qExpansion_coxAction_aux`
- **Visibility**: private
- **Lines**: 225–233, proof 8 lines
- **Notes**: none

### `theorem to_qExpansion_coxAction_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : to_qExpansion ((m:ℕ):ℝ) (fun τ ↦ j (σ.act τ)) = (coxPhaseAux m σ)⁻¹ • (PowerSeries.rescale (coxPhaseAux m σ) (qExpansion 1 qj)).expand (σ.a ^ 2) (pow_ne_zero _ σ.a_pos.ne')`
- **What**: The (power-series) `q^{1/m}`-expansion of `j ∘ σ` equals the `qj`-expansion with variable rescaled by `η` and exponents dilated by `a²`, all divided by `η` — the formal counterpart of substituting `q ↦ η q^{a²}` into `q·j`.
- **How**: Shows the candidate series `P` has-sums to the pole-removed function at every `q_m(τ)`: starting from the project's `hasSum_qExpansion_qj` at `στ`, multiplied by `η⁻¹` and reindexed along the injection `n ↦ a²n` (`Function.Injective.hasSum_iff`, off-image coefficients vanish by `PowerSeries.coeff_expand`); each reindexed term matches by `PowerSeries.coeff_expand_mul`, `PowerSeries.coeff_rescale` and the `qParam` law. Concludes by coefficient uniqueness `qExpansion_coeff_unique` (mathlib), with analyticity of the pole-removed cusp function from the project's `analyticAt_cuspFunction_poleRemoved` applied to `cuspFunction_coxAction_meromorphicAt_aux`.
- **Hypotheses**: none
- **Uses from project**: [`to_qExpansion`, `poleRemoved`, `qj`, `j`, `coxPhaseAux`, `hasSum_qExpansion_qj`, `analyticAt_cuspFunction_poleRemoved`, `cuspFunction_coxAction_meromorphicAt_aux`, `poleRemoved_coxAction_aux`, `qParam_coxAction_aux`, `CoxMatrix.act`, `CoxMatrix` (field `a_pos`)]
- **Used by**: `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: private
- **Lines**: 235–280, proof 44 lines
- **Notes**: proof >30 lines (44)

### `theorem inv_mul_pow_toNat_add_one_aux`
- **Type**: `{η : ℂ} (hη : η ≠ 0) {t : ℤ} (ht : -1 ≤ t) : η⁻¹ * η ^ Int.toNat (t + 1) = η ^ t`
- **What**: Bookkeeping identity converting the natural power `η^{t+1}` (from power-series indexing) divided by `η` into the integer power `η^t`, valid from `t = -1` on.
- **How**: Rewrites both natural powers as `zpow` via `Int.toNat_of_nonneg` and combines exponents with `zpow_add₀`.
- **Hypotheses**: `η ≠ 0`, `t ≥ -1`.
- **Uses from project**: []
- **Used by**: `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: private
- **Lines**: 282–289, proof 6 lines
- **Notes**: none

### `theorem coxPhase_zpow_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) (t : ℤ) : coxPhaseAux m σ ^ t = zeta m ^ (((σ.a : ℤ) * (σ.b : ℤ)) * t)`
- **What**: Integer powers of the phase unfold to `ζ_m^{ab·t}`, matching the exponent shape in `transformedJSeries`.
- **How**: `zpow_natCast` and `zpow_mul` on the definition `η = ζ^{ab}`, then `norm_cast`.
- **Hypotheses**: none
- **Uses from project**: [`coxPhaseAux`, `zeta`, `CoxMatrix`]
- **Used by**: `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: private
- **Lines**: 291–295, proof 2 lines
- **Notes**: none

### `theorem laurentqExpansion_coxAction_coeff_aux`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) (k : ℤ) : (laurentqExpansion ((m:ℕ):ℝ) (fun τ ↦ j (σ.act τ))).coeff k = (transformedJSeries (zeta m) σ).coeff k`
- **What**: Coefficient-by-coefficient identification of the analytic Laurent `q^{1/m}`-expansion of `j ∘ σ` with the formal series of (11.13).
- **How**: Three-way case analysis on `k` against `r = a²`. (i) `k < -a²`: both sides vanish, left by `laurentqExpansion.coeff_eq_zero_of_lt` with `poleOrder_coxAction_aux`. (ii) `a² ∣ k`, `k ≥ -a²`: read the coefficient from the power-series part via `laurentqExpansion.coeff_of_geq` and `to_qExpansion_coxAction_aux`; with `t = k/a²`, the expand/rescale coefficient is `η⁻¹ η^{t+1} c(t)` (`PowerSeries.coeff_expand_mul`, `coeff_rescale`), where `c(t)` is identified as `jIntCoeff t` through `j_to_qExpansion`, `laurentqExpansion.coeff_of_geq` at width 1 (`j_poleOrder`), and `jIntCoeff_spec`; the phase collapses by `inv_mul_pow_toNat_add_one_aux` and `coxPhase_zpow_aux`. (iii) `a² ∤ k`: the `expand` coefficient at a non-multiple of `a²` vanishes (`PowerSeries.coeff_expand` after an `Int.toNat` divisibility transfer), matching the `if_neg` branch.
- **Hypotheses**: none
- **Uses from project**: [`transformedJSeries`, `transformedJSeries_coeff`, `zeta`, `coxPhaseAux`, `coxPhase_ne_zero_aux`, `coxPhase_zpow_aux`, `poleOrder_coxAction_aux`, `to_qExpansion_coxAction_aux`, `inv_mul_pow_toNat_add_one_aux`, `jIntCoeff`, `jIntCoeff_spec`, `laurentqExpansion`, `laurentqExpansion.coeff_eq_zero_of_lt`, `laurentqExpansion.coeff_of_geq`, `to_qExpansion`, `poleOrder`, `j`, `qj`, `j_to_qExpansion`, `j_poleOrder`, `CoxMatrix.act`, `CoxMatrix` (field `a_pos`)]
- **Used by**: `laurentqExpansion_coxAction`
- **Visibility**: private
- **Lines**: 297–388, proof 90 lines
- **Notes**: proof >30 lines (90) — the longest proof in the file

### `theorem laurentqExpansion_coxAction`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) : laurentqExpansion ((m:ℕ):ℝ) (fun τ ↦ j (σ.act τ)) = transformedJSeries (zeta m) σ`
- **What**: The exact analytic/formal bridge for equation (11.13): the Laurent expansion of `j((aτ+b)/d)` in the parameter `q^{1/m}` is precisely the formal series `∑ c(n) ζ_m^{abn} q^{a²n/m}`. Main analytic theorem of the file.
- **How**: HahnSeries extensionality (`ext`) reduces to the coefficientwise identity `laurentqExpansion_coxAction_coeff_aux`.
- **Hypotheses**: none
- **Uses from project**: [`laurentqExpansion`, `transformedJSeries`, `zeta`, `laurentqExpansion_coxAction_coeff_aux`, `j`, `CoxMatrix.act`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 390–396, proof 2 lines
- **Notes**: docstring present (notes the width is `m`, not 1)

### `def reindex`
- **Type**: `{m : ℕ+} (k : ℕ) (hk : Nat.Coprime k (m : ℕ)) : CoxMatrix m → CoxMatrix m`
- **What**: The Galois reindexing of `C(m)` from the proof of Cox's Theorem 11.18(i): `(a, b; 0, d) ↦ (a, bk mod d; 0, d)`, modelling the action of `σ_k ∈ Gal(ℚ(ζ_m)/ℚ)` (i.e. `ζ ↦ ζ^k`) on the Laurent expansions.
- **How**: Keeps `a, d` (so the determinant and `a > 0` are unchanged); `bk mod d < d` by `Nat.mod_lt`; primitivity is preserved because `gcd(bk mod d, d) = gcd(bk, d)` (`Nat.gcd_rec`) and `k ⊥ d` (from `k ⊥ m` and `d ∣ m`) cancels the factor `k` via `Nat.Coprime.gcd_mul_right_cancel`, with `ac_rfl` handling gcd re-association.
- **Hypotheses**: `k` coprime to `m`.
- **Uses from project**: [`CoxMatrix` (fields `a`, `b`, `d`, `a_pos`, `determinant`, `d_pos`, `b_lt`, `primitive`)]
- **Used by**: `reindex_bijective`
- **Visibility**: public
- **Lines**: 398–426, definition 29 lines (built by tactic)
- **Notes**: docstring present

### `theorem reindex_bijective`
- **Type**: `{m : ℕ+} (k : ℕ) (hk : Nat.Coprime k (m : ℕ)) : Function.Bijective (reindex k hk)`
- **What**: For `k ⊥ m`, the reindexing `b ↦ bk mod d` permutes `C(m)` — the fact that makes it a genuine Galois action on the set of Cox roots.
- **How**: Injectivity: equal images force `a` and `d` to agree; `bk ≡ b'k (mod d)` cancels `k` by `Nat.ModEq.cancel_right_of_coprime` (using `gcd(d,k) = 1` from `k ⊥ m`, `d ∣ m`), and `b, b' < d` gives `b = b'` by `Nat.ModEq.eq_of_lt_of_lt`; equality of matrices then follows from `CoxMatrix.toFin_injective`. Surjectivity is automatic on the finite type `C(m)` by `Finite.injective_iff_surjective`.
- **Hypotheses**: `k` coprime to `m`.
- **Uses from project**: [`reindex`, `CoxMatrix.toFin_injective`, `CoxMatrix` (fields `a`, `b`, `d`, `determinant`, `b_lt`)]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 428–458, proof 30 lines
- **Notes**: proof at the 30-line boundary (30 lines)

### File Summary
- Total declarations: 25 (5 defs, 20 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): `coxPhaseAux` (11 uses), `zeta` (6 uses), `jIntCoeff` (4 uses), `transformedJSeries` (3 uses), `qParam_coxAction_aux` (3 uses), `coxPhase_ne_zero_aux` (3 uses)
- Unused declarations (not used by anything in this file): `zeta_isPrimitiveRoot`, `jIntCoeff_neg_one`, `laurentqExpansion_coxAction` (main theorem), `reindex_bijective` (main theorem)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [`poleOrder_coxAction_aux` (54 lines), `to_qExpansion_coxAction_aux` (44 lines), `laurentqExpansion_coxAction_coeff_aux` (90 lines)]
