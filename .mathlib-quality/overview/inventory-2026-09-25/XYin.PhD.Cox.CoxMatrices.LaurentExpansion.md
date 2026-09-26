# Inventory: XYin/PhD/Cox/CoxMatrices/LaurentExpansion.lean  (354 lines)

Realises Cox equation (11.13): for `σ = [[a,b],[0,d]] ∈ C(m)`, the Laurent `q^{1/m}`-expansion of
`j(σ·τ)` is `Σ_n c_n ζ_m^{abn} q^{a²n/m}`. Defines the formal series `transformedJSeries ζ σ`
(over any field, with a chosen `m`-th root `ζ`), proves it equals the project's analytic
`laurentqExpansion m (j ∘ σ.act)`, and defines the Galois reindexing `b ↦ bk mod d` on `C(m)`.

## Declarations

### `def Cox.zeta`
- **Type**: `(m : ℕ+) : ℂ` := `Complex.exp (2 * π * I / m)`
- **What**: The primitive `m`-th root of unity `ζ_m = e^{2πi/m}`.
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `zeta_isPrimitiveRoot`, `coxPhaseAux`, `qParam_coxAction_aux`, `coxPhase_zpow_aux`, `laurentqExpansion_coxAction_coeff_aux`, `laurentqExpansion_coxAction`
- **Visibility**: public
- **Lines**: 24
- **Notes**: Mathlib has no named constant for `exp(2πi/n)`; the API is `Complex.isPrimitiveRoot_exp` (RingTheory/RootsOfUnity/Complex.lean:85). Used in 5 other project files.

### `theorem Cox.zeta_isPrimitiveRoot`
- **Type**: `(m : ℕ+) : IsPrimitiveRoot (zeta m) m`
- **What**: `ζ_m` is a primitive `m`-th root of unity.
- **How**: `Complex.isPrimitiveRoot_exp m (PNat.ne_zero m)`.
- **Hypotheses**: none.
- **Uses from project**: [`zeta`]
- **Used by**: unused in file (used by Kronecker, DiagonalLaurent, LevelThree, UpperHalfPlaneFunctionField, FormalCoxProduct)
- **Visibility**: public
- **Lines**: 26–28, proof ≈ 2 lines
- **Notes**: —

### `def Cox.jIntCoeff`
- **Type**: `(n : ℤ) : ℤ` := `(j_laurentQExpansion_isIntegral (n := n)).choose`
- **What**: The integer Laurent coefficient `c_n` of `j`.
- **How**: `Classical.choose` from the integrality theorem in jfunction.lean.
- **Hypotheses**: none.
- **Uses from project**: [`j_laurentQExpansion_isIntegral`]
- **Used by**: `jIntCoeff_spec`, `jIntCoeff_neg_one`, `transformedJSeries`, `transformedJSeries_coeff`, `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: public (noncomputable)
- **Lines**: 31–32
- **Notes**: Better packaged as an integer Laurent series `jIntLaurent : LaurentSeries ℤ` with `laurentqExpansion 1 j = jIntLaurent.map (Int.castRingHom ℂ)` (mathlib `HahnSeries.map`, RingTheory/HahnSeries/Basic.lean:143). Missing companion `jIntCoeff_of_lt_neg_one : n < -1 → jIntCoeff n = 0` (2 lines from `j_laurentQExpansion_coeff_eq_zero_of_lt_neg_one`, jfunction.lean:487) — its absence is why `transformedJSeries` carries the redundant `-(a²) ≤ k` clause.

### `theorem Cox.jIntCoeff_spec`
- **Type**: `(n : ℤ) : (laurentqExpansion 1 j).coeff n = (jIntCoeff n : ℂ)`
- **What**: The chosen integer is the coefficient.
- **How**: `choose_spec`.
- **Hypotheses**: none.
- **Uses from project**: [`jIntCoeff`, `j_laurentQExpansion_isIntegral`, `laurentqExpansion`, `j`]
- **Used by**: `jIntCoeff_neg_one`, `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: public
- **Lines**: 34–36
- **Notes**: Used by 4 other files.

### `theorem Cox.jIntCoeff_neg_one`
- **Type**: `jIntCoeff (-1) = 1`
- **What**: `j = q^{-1} + …`: the leading coefficient is 1.
- **How**: `laurentqExpansion.coeff_neg_poleOrder` with `j_poleOrder`, `j_to_qExpansion`, `qj_qExpansion_coeff_zero`, then `exact_mod_cast`.
- **Hypotheses**: none.
- **Uses from project**: [`jIntCoeff`, `jIntCoeff_spec`, `laurentqExpansion.coeff_neg_poleOrder`, `j_poleOrder`, `to_qExpansion`, `j_to_qExpansion`, `qj`, `qj_qExpansion_coeff_zero`, `laurentqExpansion`, `j`]
- **Used by**: unused in file (used by Kronecker, DiagonalLaurent, UpperHalfPlaneFunctionField, IntegralDescent)
- **Visibility**: public
- **Lines**: 38–47, proof ≈ 8 lines
- **Notes**: —

### `def Cox.transformedJSeries`
- **Type**: `{K} [Field K] {m : ℕ+} (ζ : K) (σ : CoxMatrix m) : LaurentSeries K`
- **What**: Cox (11.13) as a formal Laurent series in `t = q^{1/m}`: coefficient of `t^k` is `c_{k/a²} ζ^{ab·k/a²}` when `a² ∣ k` and `k ≥ -a²`, else `0`.
- **How**: `HahnSeries` built from the coefficient function; `isPWO_support'` from `BddBelow.isWF` + `Set.IsWF.isPWO` with lower bound `-a²`.
- **Hypotheses**: `K` a field (only `ζ^(ℤ)` needs a `DivisionRing`).
- **Uses from project**: [`jIntCoeff`, `CoxMatrix` (fields `a`, `b`)]
- **Used by**: `transformedJSeries_coeff`, `laurentqExpansion_coxAction_coeff_aux`, `laurentqExpansion_coxAction`
- **Visibility**: public (noncomputable)
- **Lines**: 50–64
- **Notes**: Used by 6 other files. Hand-rolled monomial substitution — see Observations for the `HahnSeries.embDomain`/rescale decomposition.

### `theorem Cox.transformedJSeries_coeff`
- **Type**: `(transformedJSeries ζ σ).coeff k = if (a:ℤ)^2 ∣ k ∧ -(a:ℤ)^2 ≤ k then (jIntCoeff (k / a²) : K) * ζ ^ (a*b * (k / a²)) else 0`
- **What**: Coefficient formula.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`transformedJSeries`, `jIntCoeff`]
- **Used by**: `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: public
- **Lines**: 66–72
- **Notes**: Not `@[simp]`; used by 5 other files.

### `private def Cox.coxPhaseAux`
- **Type**: `(m) (σ) : ℂ` := `zeta m ^ (σ.a * σ.b)`
- **What**: The phase `η = ζ_m^{ab}`.
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: [`zeta`]
- **Used by**: `qParam_coxAction_aux`, `cuspFunction_coxCompose_aux`, `cuspFunction_coxAction_aux`, `coxPhase_ne_zero_aux`, `cuspFunction_coxAction_eventuallyEq_aux`, `cuspFunction_coxAction_meromorphicAt_aux`, `poleOrder_coxAction_aux`, `poleRemoved_coxAction_aux`, `to_qExpansion_coxAction_aux`, `coxPhase_zpow_aux`, `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: private
- **Lines**: 74–75
- **Notes**: —

### `private theorem Cox.qParam_coxAction_aux`
- **Type**: `Periodic.qParam 1 (σ.act τ) = coxPhaseAux m σ * Periodic.qParam (m : ℝ) τ ^ (σ.a ^ 2)`
- **What**: `e^{2πi(aτ+b)/d} = ζ_m^{ab} (e^{2πiτ/m})^{a²}` since `m = ad`.
- **How**: Unfold `Periodic.qParam`, combine exponentials (`Complex.exp_nat_mul`, `exp_add`), `field_simp` with `a, d ≠ 0`, `ring` using `m = a d`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.act`, `CoxMatrix.coe_act`, `CoxMatrix.determinant`, `CoxMatrix.a_pos`, `CoxMatrix.d_pos`, `coxPhaseAux`, `zeta`]
- **Used by**: `cuspFunction_coxCompose_aux`, `poleRemoved_coxAction_aux`, `to_qExpansion_coxAction_aux`
- **Visibility**: private
- **Lines**: 77–91, proof ≈ 13 lines
- **Notes**: The single analytic input of the whole file.

### `private theorem Cox.cuspFunction_coxCompose_aux`
- **Type**: `(f : ℍ → ℂ) (hfper : Periodic (f ∘ ofComplex) 1) (hq0 : q ≠ 0) (hqnorm : ‖q‖ < 1) : cuspFunction (m : ℝ) (fun τ ↦ f (σ.act τ)) q = cuspFunction 1 f (coxPhaseAux m σ * q ^ (σ.a ^ 2))`
- **What**: On the punctured unit disc, the width-`m` cusp function of `f ∘ σ` is the width-1 cusp function of `f` composed with `q ↦ η q^{a²}`.
- **How**: `Periodic.cuspFunction_eq_of_nonzero` (Analysis/Complex/Periodic.lean:119), `Periodic.im_invQParam_pos_of_norm_lt_one` (UpperHalfPlane/Exp.lean:25), `Periodic.qParam_right_inv` (Periodic.lean:61), `UpperHalfPlane.ofComplex_apply_of_im_pos` (UpperHalfPlane/Topology.lean:162), `UpperHalfPlane.eq_cuspFunction` (NumberTheory/ModularForms/QExpansion.lean:79), and `qParam_coxAction_aux`.
- **Hypotheses**: `f` 1-periodic; `0 < ‖q‖ < 1`.
- **Uses from project**: [`CoxMatrix.act`, `coxPhaseAux`, `qParam_coxAction_aux`]
- **Used by**: `cuspFunction_coxAction_aux`
- **Visibility**: private
- **Lines**: 93–113, proof ≈ 19 lines
- **Notes**: Already generic in `f`; only the `j` specialisation is used.

### `private theorem Cox.cuspFunction_coxAction_aux`
- **Type**: same as above with `f := j`
- **What**: Specialisation to `j`.
- **How**: `cuspFunction_coxCompose_aux … ModularFunction.j_periodic`.
- **Hypotheses**: `0 < ‖q‖ < 1`.
- **Uses from project**: [`cuspFunction_coxCompose_aux`, `j`, `ModularFunction.j_periodic`, `coxPhaseAux`, `CoxMatrix.act`]
- **Used by**: `cuspFunction_coxAction_eventuallyEq_aux`
- **Visibility**: private
- **Lines**: 115–119, proof ≈ 1 line
- **Notes**: One-line wrapper; could be inlined.

### `private theorem Cox.coxPhase_ne_zero_aux`
- **Type**: `coxPhaseAux m σ ≠ 0`
- **What**: `η ≠ 0`.
- **How**: `pow_ne_zero`, `Complex.exp_ne_zero`.
- **Hypotheses**: none.
- **Uses from project**: [`coxPhaseAux`, `zeta`]
- **Used by**: `poleOrder_coxAction_aux`, `poleRemoved_coxAction_aux`, `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: private
- **Lines**: 121–123
- **Notes**: —

### `private theorem Cox.cuspFunction_coxAction_eventuallyEq_aux`
- **Type**: `cuspFunction (m : ℝ) (fun τ ↦ j (σ.act τ)) =ᶠ[𝓝[≠] 0] cuspFunction 1 j ∘ fun q ↦ coxPhaseAux m σ * q ^ (σ.a ^ 2)`
- **What**: The previous identity holds on a punctured neighbourhood of 0.
- **How**: `filter_upwards` with the unit ball in `𝓝[≠] 0` (`Metric.ball_mem_nhds`, `nhdsWithin_le_nhds`, `self_mem_nhdsWithin`).
- **Hypotheses**: none.
- **Uses from project**: [`cuspFunction_coxAction_aux`, `coxPhaseAux`, `CoxMatrix.act`, `j`]
- **Used by**: `cuspFunction_coxAction_meromorphicAt_aux`, `poleOrder_coxAction_aux`
- **Visibility**: private
- **Lines**: 125–132, proof ≈ 6 lines
- **Notes**: —

### `private theorem Cox.cuspFunction_coxAction_meromorphicAt_aux`
- **Type**: `MeromorphicAt (cuspFunction (m : ℝ) (fun τ ↦ j (σ.act τ))) 0`
- **What**: `j ∘ σ` is meromorphic at the cusp of width `m`.
- **How**: `MeromorphicAt.comp_analyticAt` (Analysis/Meromorphic/Basic.lean:438) of `j_cuspFunction_meromorphicAt` with the analytic `q ↦ η q^{a²}` (`fun_prop`), transported by `MeromorphicAt.congr`.
- **Hypotheses**: none.
- **Uses from project**: [`j_cuspFunction_meromorphicAt`, `cuspFunction_coxAction_eventuallyEq_aux`, `coxPhaseAux`, `CoxMatrix.a_pos`, `CoxMatrix.act`, `j`]
- **Used by**: `to_qExpansion_coxAction_aux`
- **Visibility**: private
- **Lines**: 134–141, proof ≈ 6 lines
- **Notes**: —

### `private theorem Cox.poleOrder_coxAction_aux`
- **Type**: `poleOrder (m : ℝ) (fun τ ↦ j (σ.act τ)) = σ.a ^ 2`
- **What**: The pole order of `j(σ·τ)` in `q^{1/m}` is `a²`.
- **How**: `analyticOrderAt (η q^r) = r` (via `analyticOrderAt_mul`, `analyticOrderAt_pow` Analysis/Analytic/Order.lean:455, `analyticOrderAt_id`), non-constancy via `eventuallyConst_iff_analyticOrderAt_sub_eq_top` (Order.lean:80), base order `-1` from `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` + `j_poleOrder`, composition via `MeromorphicAt.meromorphicOrderAt_comp` (Meromorphic/Order.lean:810), transfer via `meromorphicOrderAt_congr`, and `poleOrder_eq_toNat_neg_meromorphicOrderAt`.
- **Hypotheses**: none.
- **Uses from project**: [`poleOrder`, `poleOrder_eq_toNat_neg_meromorphicOrderAt`, `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder`, `j_poleOrder`, `j_cuspFunction_meromorphicAt`, `cuspFunction_coxAction_eventuallyEq_aux`, `coxPhaseAux`, `coxPhase_ne_zero_aux`, `CoxMatrix.act`, `CoxMatrix.a_pos`, `j`]
- **Used by**: `poleRemoved_coxAction_aux`, `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: private
- **Lines**: 143–184, proof ≈ 40 lines
- **Notes**: Proof >30 lines. The 10-line sub-block `analyticOrderAt (fun q ↦ η q^r) 0 = r` (151–160) is a mathlib-shaped lemma `analyticOrderAt_const_mul_pow` (mathlib has `analyticOrderAt_smul`, `analyticOrderAt_mul`, `analyticOrderAt_id` in Analytic/Order.lean but not the packaged monomial case). The `WithTop ℤ` arithmetic (172–175) is a `norm_cast` workaround.

### `private theorem Cox.poleRemoved_coxAction_aux`
- **Type**: `poleRemoved (m : ℝ) (fun τ ↦ j (σ.act τ)) = fun τ ↦ (coxPhaseAux m σ)⁻¹ * qj (σ.act τ)`
- **What**: After removing the pole, `q_m^{a²} j(σ τ) = η⁻¹ · (q₁ j)(σ τ) = η⁻¹ qj(σ τ)`.
- **How**: `UpperHalfPlane.poleRemoved` unfolded with `poleOrder_coxAction_aux`, `qParam_coxAction_aux`, `field_simp`.
- **Hypotheses**: none.
- **Uses from project**: [`poleRemoved`, `poleOrder_coxAction_aux`, `qj`, `qParam_coxAction_aux`, `coxPhase_ne_zero_aux`, `coxPhaseAux`, `CoxMatrix.act`, `j`]
- **Used by**: `to_qExpansion_coxAction_aux`
- **Visibility**: private
- **Lines**: 186–194, proof ≈ 6 lines
- **Notes**: —

### `private theorem Cox.to_qExpansion_coxAction_aux`
- **Type**: `to_qExpansion (m : ℝ) (fun τ ↦ j (σ.act τ)) = (coxPhaseAux m σ)⁻¹ • (PowerSeries.rescale (coxPhaseAux m σ) (qExpansion 1 qj)).expand (σ.a ^ 2) _`
- **What**: The holomorphic-part power series of `j ∘ σ` in `q_m` is `η⁻¹ · (rescale by η, then expand by a²)` of the `q`-expansion of `qj = q·j`.
- **How**: Uniqueness of `q`-expansion coefficients (`qExpansion_coeff_unique`, NumberTheory/ModularForms/QExpansion.lean:691) applied to the `HasSum` obtained from `hasSum_qExpansion_qj` by reindexing along `n ↦ a² n` (`Function.Injective.hasSum_iff`) with `PowerSeries.coeff_expand_mul` (RingTheory/PowerSeries/Expand.lean:87), `PowerSeries.coeff_rescale` (PowerSeries/Basic.lean:562), `PowerSeries.coeff_expand` (Expand.lean:110); analyticity from `analyticAt_cuspFunction_poleRemoved`.
- **Hypotheses**: none.
- **Uses from project**: [`to_qExpansion`, `poleRemoved`, `poleRemoved_coxAction_aux`, `cuspFunction_coxAction_meromorphicAt_aux`, `analyticAt_cuspFunction_poleRemoved`, `hasSum_qExpansion_qj`, `qj`, `qParam_coxAction_aux`, `coxPhaseAux`, `CoxMatrix.act`, `CoxMatrix.a_pos`, `j`]
- **Used by**: `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: private
- **Lines**: 196–241, proof ≈ 44 lines
- **Notes**: Proof >30 lines. Lines 216–237 (`hreindexed`/`hinj`/`hasSum_iff`/`coeff_expand` with `¬ r ∣ n`) are the same skeleton as LaurentQExpansion/Algebra.lean:303–324 (`hasFPowerSeriesAt_expand_analyticTaylor`), whose public wrapper `to_qExpansion_nat_mul` (Algebra.lean:365) is the `η = 1`, `φ = id` case.

### `private theorem Cox.inv_mul_pow_toNat_add_one_aux`
- **Type**: `(hη : η ≠ 0) (ht : -1 ≤ t) : η⁻¹ * η ^ Int.toNat (t + 1) = η ^ t`
- **What**: `η^{-1} η^{t+1} = η^t` with the ℕ/ℤ exponent conversion.
- **How**: `zpow_natCast`, `Int.toNat_of_nonneg`, `zpow_add₀`.
- **Hypotheses**: `η ≠ 0`, `t ≥ -1`.
- **Uses from project**: []
- **Used by**: `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: private
- **Lines**: 243–250, proof ≈ 5 lines
- **Notes**: Pure `GroupWithZero` lemma stated for ℂ.

### `private theorem Cox.coxPhase_zpow_aux`
- **Type**: `coxPhaseAux m σ ^ t = zeta m ^ ((a:ℤ) * b * t)`
- **What**: `η^t = ζ^{abt}`.
- **How**: `zpow_natCast`, `zpow_mul`, `norm_cast`.
- **Hypotheses**: none.
- **Uses from project**: [`coxPhaseAux`, `zeta`]
- **Used by**: `laurentqExpansion_coxAction_coeff_aux`
- **Visibility**: private
- **Lines**: 252–256, proof ≈ 2 lines
- **Notes**: —

### `private theorem Cox.laurentqExpansion_coxAction_coeff_aux`
- **Type**: `(laurentqExpansion (m : ℝ) (fun τ ↦ j (σ.act τ))).coeff k = (transformedJSeries (zeta m) σ).coeff k`
- **What**: Coefficientwise identification of the analytic Laurent expansion with the formal series (11.13).
- **How**: `laurentqExpansion.coeff_of_qExpansion` + `poleOrder_coxAction_aux`, then a three-way split: `k < -a²` (both 0), `a² ∣ k` (write `k = a² t`, `Int.toNat_mul`, `PowerSeries.coeff_expand_mul`/`coeff_rescale`/`coeff_smul`, `jIntCoeff_spec` via `laurentqExpansion.coeff_of_geq`, `inv_mul_pow_toNat_add_one_aux`, `coxPhase_zpow_aux`), `¬ a² ∣ k` (both 0 by `PowerSeries.coeff_expand`).
- **Hypotheses**: none.
- **Uses from project**: [`laurentqExpansion`, `laurentqExpansion.coeff_of_qExpansion`, `laurentqExpansion.coeff_of_geq`, `transformedJSeries`, `transformedJSeries_coeff`, `poleOrder_coxAction_aux`, `to_qExpansion_coxAction_aux`, `jIntCoeff`, `jIntCoeff_spec`, `j_poleOrder`, `j_to_qExpansion`, `qj`, `coxPhaseAux`, `coxPhase_ne_zero_aux`, `coxPhase_zpow_aux`, `inv_mul_pow_toNat_add_one_aux`, `zeta`, `CoxMatrix.act`, `CoxMatrix.a_pos`, `j`]
- **Used by**: `laurentqExpansion_coxAction`
- **Visibility**: private
- **Lines**: 258–300, proof ≈ 41 lines
- **Notes**: Proof >30 lines (the earlier overview's "~90 lines" is stale — now 43 lines at 258–300). Same case skeleton as Algebra.lean `laurentqExpansion_nat_mul_coeff` (384) / `_of_not_dvd` (417). See Observations for the helper that collapses it.

### `theorem Cox.laurentqExpansion_coxAction`
- **Type**: `(m) (σ) : laurentqExpansion (m : ℝ) (fun τ ↦ j (σ.act τ)) = transformedJSeries (zeta m) σ`
- **What**: Cox (11.13): the analytic/formal bridge, at width `m` (parameter `q^{1/m}`).
- **How**: `HahnSeries.ext` + the coefficient lemma.
- **Hypotheses**: none.
- **Uses from project**: [`laurentqExpansion`, `transformedJSeries`, `laurentqExpansion_coxAction_coeff_aux`, `zeta`, `CoxMatrix.act`, `j`]
- **Used by**: unused in file (used by UpperHalfPlaneFunctionField, IntegralDescent)
- **Visibility**: public
- **Lines**: 304–308, proof ≈ 2 lines
- **Notes**: —

### `def Cox.reindex`
- **Type**: `{m} (k : ℕ) (hk : Nat.Coprime k m) : CoxMatrix m → CoxMatrix m`
- **What**: Galois reindexing `[[a,b],[0,d]] ↦ [[a, bk mod d],[0,d]]` (proof of Cox Thm 11.18(i)).
- **How**: `Nat.mod_lt` for `b_lt`; primitivity by `Nat.gcd_rec`, `Nat.Coprime.gcd_mul_right_cancel` using `k ⊥ d` (from `k ⊥ m`, `d ∣ m`).
- **Hypotheses**: `k` coprime to `m`.
- **Uses from project**: [`CoxMatrix` (fields), `CoxMatrix.d_pos`]
- **Used by**: `reindex_bijective`
- **Visibility**: public
- **Lines**: 311–326
- **Notes**: Defined by `fun σ ↦ by … refine {…}` so `simp only [reindex]` (333, 335, 338; FormalCoxProduct.lean:113) unfolds the whole term — missing `reindex_a/_b/_d` simp lemmas. Re-derives `σ.d ∣ m` (313–314). Not packaged as `Equiv.Perm` or as a `MulAction (ZMod m)ˣ (CoxMatrix m)`.

### `theorem Cox.reindex_bijective`
- **Type**: `Function.Bijective (reindex k hk)`
- **What**: Reindexing is a permutation of `C(m)`.
- **How**: Injective: extract `a`, `d`, then `Nat.ModEq.cancel_right_of_coprime` (Data/Nat/ModEq.lean:416) and `Nat.ModEq.eq_of_lt_of_lt`, finish by `cases; simp_all`; surjective from `Finite.injective_iff_surjective`.
- **Hypotheses**: `k ⊥ m`.
- **Uses from project**: [`reindex`, `CoxMatrix` (fields `determinant`, `b_lt`)]
- **Used by**: unused in file (used by FormalCoxProduct.lean only)
- **Visibility**: public
- **Lines**: 328–352, proof ≈ 23 lines
- **Notes**: Third `cases σ; cases τ; simp_all` ext site (349–351); re-derives `σ.d ∣ m` (339–340).

## File Summary
- Total declarations: 23 (5 defs, 18 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): `coxPhaseAux` (11), `zeta` (6), `jIntCoeff` (5), `CoxMatrix.act` (all analytic lemmas), `qParam_coxAction_aux` (3), `coxPhase_ne_zero_aux` (3), `transformedJSeries` (3)
- Unused declarations (not used by anything in this file): `zeta_isPrimitiveRoot`, `jIntCoeff_neg_one`, `laurentqExpansion_coxAction`, `reindex_bijective` (all used by other files)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `poleOrder_coxAction_aux` (143–184, 40), `to_qExpansion_coxAction_aux` (196–241, 44), `laurentqExpansion_coxAction_coeff_aux` (258–300, 41)

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- **Monomial substitution (the (11.13) pattern).** `transformedJSeries` (50) is, in mathlib terms, `HahnSeries.embDomain` along `k ↦ a²·k` of the zpow-rescale `c_t ↦ ζ^{ab t} c_t` of the integer series of `j`. Mathlib (grep-verified): `HahnSeries.embDomain` (RingTheory/HahnSeries/Basic.lean:441), `embDomain_coeff` (449), `embDomain_notin_range` (477), `embDomain_add` (Addition.lean:294), `embDomain_mul` (Multiplication.lean:857), `embDomainRingHom (f : Γ →+ Γ') (hfi) (hf : ∀ g g', f g ≤ f g' ↔ g ≤ g')` (Multiplication.lean:899) — `k ↦ r*k` on ℤ (r > 0) satisfies both, so the "expand" half is a ring hom for free. Mathlib has NO Laurent/Hahn-level rescale (`coeff k ↦ c^k · coeff k`; grep of `RingTheory/HahnSeries/*` and `LaurentSeries.lean` for `rescale|zpow` finds only `single_zpow`); `PowerSeries.rescale` (PowerSeries/Basic.lean:537) and `PowerSeries.expand` (PowerSeries/Expand.lean:33, `= subst (X^p)` per `expand_apply` line 36) are power-series only, and `PowerSeries.subst` (PowerSeries/Substitution.lean:158, `rescale_eq_subst` line 394) would package `rescale c ∘ expand r = subst (C c * X^r)` at the power-series level. `Polynomial.expand` (Algebra/Polynomial/Expand.lean:40) is irrelevant here. The `IsPrimitiveRoot`/`ZMod` API in play is `Complex.isPrimitiveRoot_exp` (RootsOfUnity/Complex.lean:85) here and `IsPrimitiveRoot.zpow_eq_one_iff_dvd`, `autToPow` in FormalCoxProduct.
- **The helper that collapses `laurentqExpansion_coxAction_coeff_aux` (258–300) and `to_qExpansion_coxAction_aux` (196–241):** define `LaurentSeries.substMonomial (c : K) (r : ℕ) (hr : r ≠ 0) (F : LaurentSeries K) : LaurentSeries K` with `coeff_substMonomial : (substMonomial c r hr F).coeff k = if (r:ℤ) ∣ k then c ^ (k / r) * F.coeff (k / r) else 0` (`c ≠ 0`, zpow), i.e. `embDomainRingHom (mulLeft r) ∘ zpowRescale c`, and prove ONE analytic bridge `laurentqExpansion_comp_of_qParam_eq {h h' : ℝ} {φ : ℍ → ℍ} {c : ℂ} {r : ℕ} (hc : c ≠ 0) (hr : r ≠ 0) (hq : ∀ τ, Periodic.qParam h' (φ τ) = c * Periodic.qParam h τ ^ r) (hmero : MeromorphicAt (cuspFunction h' f) 0) (hper : Periodic (f ∘ ofComplex) h') : laurentqExpansion h (f ∘ φ) = substMonomial c r hr (laurentqExpansion h' f)`. Then (11.13) is `laurentqExpansion_coxAction := by rw [bridge (qParam_coxAction_aux …)]; ext; simp [coeff_substMonomial, transformedJSeries_coeff, jIntCoeff_spec]`, and the whole private chain 93–300 (≈180 lines) plus Algebra.lean's `to_qExpansion_nat_mul`/`laurentqExpansion_nat_mul_coeff*` (365–440, the `c = 1, φ = id, h = r h'` case) become instances. The July proposal `PowerSeries.coeff_smul_rescale_expand` (step7-api.md:449) is the power-series shadow of `coeff_substMonomial`.
- `poleOrder_coxAction_aux` (143): missing mathlib lemma `analyticOrderAt_const_mul_pow : c ≠ 0 → analyticOrderAt (fun z ↦ c * (z - z₀)^n) z₀ = n` (151–160); mathlib has `analyticOrderAt_smul`, `analyticOrderAt_mul`, `analyticOrderAt_pow` (Analytic/Order.lean:455), `analyticOrderAt_id`.
- `reindex` (311) is the `(ZMod m)ˣ`-action on `C(m)`; mathlib's `ZMod.val_coe_unit_coprime` (Data/ZMod/Basic.lean:799, used in FormalCoxProduct:153) is the natural input type: `reindex (u : (ZMod m)ˣ)` with `MulAction` laws `reindex_one`, `reindex_mul` (absent).
### Missing API / repeated patterns
- `jIntCoeff_of_lt_neg_one : n < -1 → jIntCoeff n = 0` (from jfunction.lean:487) — would make the `-(a²) ≤ k` clause in `transformedJSeries` (52, 69) redundant and simplify `transformedJSeries_map`/`_mem_integralLaurentSeries`/`_pow_eq_reindex` in FormalCoxProduct.
- `reindex_a`, `reindex_b`, `reindex_d` simp lemmas (unfolded by `simp only [reindex]` at 333, 335, 338; FormalCoxProduct.lean:113).
- `CoxMatrix.d_dvd` re-derived at 313–314, 339–340 (and Cardinality.lean:56, 70).
- HasSum-reindexing-along-`n ↦ r n` block (216–237) duplicated at Algebra.lean:303–324 → `PowerSeries.hasSum_expand_of_hasSum : HasSum (fun n ↦ F.coeff n • x^(r n)) s → HasSum (fun n ↦ (F.expand r hr).coeff n • x^n) s`.
- `transformedJSeries_coeff` (66) should be `@[simp]`; `zeta_isPrimitiveRoot` could be an instance-like `IsPrimitiveRoot` fact used via `hζ`.
### Junk candidates
- `cuspFunction_coxAction_aux` (115–119): one-line specialisation of `cuspFunction_coxCompose_aux`; inline.
- `Mathlib.NumberTheory.Cyclotomic.Basic` is imported (6) but nothing cyclotomic is used in this file (only `Complex.isPrimitiveRoot_exp`, which lives in `RootsOfUnity/Complex`).
- No dead `#check`/`example`s or commented-out code.
### Moral duplicates within this batch
- `to_qExpansion_coxAction_aux` (196) ≈ Algebra.lean `to_qExpansion_nat_mul` (365) + `hasFPowerSeriesAt_expand_analyticTaylor` (290): same expand-by-reindexing argument, one with an extra phase `η`.
- `laurentqExpansion_coxAction_coeff_aux` (258) ≈ Algebra.lean `laurentqExpansion_nat_mul_coeff` (384) + `laurentqExpansion_nat_mul_coeff_of_not_dvd` (417): same `k < -pole / r ∣ k / ¬ r ∣ k` split with `Int.toNat_mul` and `coeff_of_geq`.
- `reindex_bijective`'s injectivity (330–351) has the same shape as Basic.lean `toFin_injective` (96) and `inclusionMatrix_injective` (288).
### Generalization notes
- `transformedJSeries` (50) needs only `[DivisionRing K]` (zpow of `ζ`) — or `[CommRing K]` if the exponent is reduced mod `m` using `IsPrimitiveRoot` — not `Field`.
- `cuspFunction_coxCompose_aux` (93) is already generic in `f`; the entire chain 125–241 is specialised to `j` only through `j_periodic`, `j_cuspFunction_meromorphicAt`, `j_poleOrder`, and could be stated for any `f` with `CuspData 1` and pole order `N` (giving pole order `N a²`).
- `inv_mul_pow_toNat_add_one_aux` (243) holds in any `GroupWithZero`; stated for ℂ.
- `reindex`/`reindex_bijective` (311–352) never use that `m` is the determinant beyond `σ.d ∣ m`; the true hypothesis is `k ⊥ σ.d` for every `σ`, i.e. `k ⊥ m` is used only through `hk.coprime_dvd_right`.
